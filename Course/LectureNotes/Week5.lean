import Course.Common
import Mathlib.Combinatorics.SimpleGraph.Maps

/-
Today: Structures and typeclasses

Recommended reading: MIL Ch. 6 and 7; TPL Ch. 9

-/

namespace Course.Week5

section Points

/- # Structures -/

/- Structures are essentially inductive types with a single constructor
  and are used to *bundle* data and/or properties of data. -/
@[ext] -- Generate extensionality lemmas automatically
structure Point2 (α : Type*) where
  x : α
  y : α

-- The constructor of a structure is named `mk` by default
#check Point2.mk

#check Point2.ext
#check Point2.ext_iff

def A : Point2 ℤ := Point2.mk 3 4

#eval A

-- We can use familiar notation to build instances (implicitly using the `mk` constructor)
def B : Point2 ℤ := ⟨1, 2⟩

#eval B.y

--#eval A + A -- This doesn't work because we haven't told Lean how to add `Point2 ℤ` instances

def add : Point2 ℤ → Point2 ℤ → Point2 ℤ := fun a b ↦ ⟨a.x + b.x, a.y + b.y⟩

#eval add A A -- Now this works
-- #eval A + A -- This still doesn't work

-- Compare this to the perhaps more familiar `uncurried` version
def add' : Point2 ℤ × Point2 ℤ → Point2 ℤ := Function.uncurry add
#check Function.curry
#check Function.uncurry
-- It is usually more convenient for formalization to use the `curry` version as in `add`

-- In just the same way we could define a component-wise multiplication
def mul : Point2 ℤ → Point2 ℤ → Point2 ℤ := fun a b ↦ ⟨a.x * b.x, a.y * b.y⟩

/- # Typeclasses -/
-- `add` provides a group structure on `Point2 ℤ` -- what does that mean in Lean?
#check Group -- check the Mathlib definition of a Group

/-
 Mathlib makes extensive use of *typeclasses* to build algebraic hierarchies
 A typeclass is just like a structure but with extra functionality:
 Lean keeps an internal record of instances of typeclasses and tries to automatically
 synthesize appropriate instances when we ask it to do so. This makes building
 even very complex algebraic hierarchies surprisingly simple.
-/

-- Let's illustrate this by implementing commutative monoids
#check Monoid -- Of course Mathlib already has (commutative) monoids
#check CommMonoid

class CommMonoid' (M : Type*) where -- The `class` keyword tells Lean that this is a typeclass
  mul' : M → M → M -- addition should be a map taking two arguments in `G` and returning another argument in `G`
  one' : M -- There is a distinguished element called `one`
  -- Now we need to list all the properties that these should satisfy
  mul_assoc' (x y z : M) : mul' (mul' x y) z = mul' x (mul' y z)
  mul_one' (x : M) : mul' x one' = x -- x * 1 = x
  mul_comm' (x y : M) : mul' x y = mul' y x

-- To make use of this we should build some instances of Monoids
-- Let's show that `Point2 ℤ` is a Monoid with our version of `mul`

instance : CommMonoid' (Point2 ℤ) where
  mul' := mul
  one' := ⟨1, 1⟩
  mul_assoc' := by
    intro a b c
    ext
    -- unfold mul
    -- dsimp
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
  mul_one' := by
    intro a
    ext
    · exact mul_one _
    · exact mul_one _
  mul_comm' := by
    intro a b
    ext
    · exact mul_comm _ _
    · exact mul_comm _ _

-- Now Lean knows that `Point2 ℤ` is a commutative monoid
-- The `#synth` command can be used to find explicit instances of typeclasses
#synth CommMonoid' (Point2 ℤ)

-- We can prove theorems that hold in any `CommMonoid'`
theorem one_mul' {M : Type*} [CommMonoid' M] (x : M) : CommMonoid'.mul' CommMonoid'.one' x = x := by
  rw [CommMonoid'.mul_comm']
  exact CommMonoid'.mul_one' _


/-
  Note three different kinds of brackets `{ }`, `[ ]`, `( )`
  - `{ }` is used for implicit arguments that Lean will attempt to fill in automatically using type inference
    (similar to modern programming languages like Kotlin or typescript)
  - `[ ]` is also an implicit argument, but it invokes the typeclass inference mechanism to *synthesize* an instance
    (we'll see that this is more powerful than just a lookup mechanism)
    In particular this can only be used for typeclasses.
    Note that it is not necessary (and not recommended) to provide a name for the instance.
  - `( )` is for explicit arguments that we'll have to provide when using the theorem
    (but as we saw tactics such as `rw` will make an attempt to fill in even explicit arguments)
-/

#check one_mul'

-- Usually we can simply ignore implicit arguments and trust Lean to fill them in appropriately
#check one_mul' A

-- We can explicitly provide implicit arguments as follows (sometimes needed)
#check one_mul' (M := Point2 ℤ)

-- We can force all implicit arguments to become explicit using `@` (rarely needed)
#check @one_mul' (Point2 ℤ) inferInstance A
-- Here we used `inferInstance` to invoke typeclass inference
#check inferInstance

-- The built-in typeclasses can often be used to infer algebraic structures
variable {α : Type*} {G : Type*} [Group G]

/- The group structure on `G` naturally induces a group structure
  on functions `α → G` (by applying operations in `G` pointwise) -/
example : Group (α → G) := by infer_instance -- `infer_instance` is the tactic version of `inferInstance`

variable (f : α → G)

#check f * f
#synth Group (α → G)

/- # Notation typeclasses -/

-- Note how it is very cumbersome that we have to write
-- things like `add A B` or `CommMonoid'.mul' x y`
-- It would be much nicer if we could use standard notation like `+` and `*`

-- Notation overloading is also done with typeclasses
#check Add -- `+`
#check Mul -- `*`
#check HAdd -- heterogeneous version of `Add`
#check HMul

--#eval A + B -- This doesn't work

instance : Add (Point2 ℤ) := ⟨add⟩

-- Now Lean will recognize `+` for `Point2 ℤ` instances
#eval A
#eval B
#eval A + B

-- Typeclass inference is powerful because it can chain instances
-- For example:
instance {M : Type*} [CommMonoid' M] : Mul M := ⟨CommMonoid'.mul'⟩

/- Here we told Lean that when it sees a `CommMonoid'` instance it should interpret
   the notation `*` as `CommMonoid'.mul'`
   Earlier we also told Lean that `Point2 ℤ` is a `CommMonoid'`, and Lean
   can put these two facts together to synthesize an instance of `Mul (Point2 ℤ)`. -/
set_option trace.Meta.synthInstance true in -- We can look at the internals of typeclass inference by using this trace command
#synth Mul (Point2 ℤ) -- This is useful if we want to find out how exactly the multiplication for a given type is implemented

-- Let's test that this works
-- #eval A * B

-- Similarly we can overload the symbol `1` to mean `CommMonoid'.one'`
#check One
instance {M : Type*} [CommMonoid' M] : One M := ⟨CommMonoid'.one'⟩

variable {M : Type*} [CommMonoid' M]
#check (1 * 1 : M)

example (x : M) : 1 * x = x * 1 := by sorry

/- # Hierarchies -/

/- In Mathlib algebraic structures are implemented hierarchically using `extend`.
  We can use `extend` to extend structures.  -/

/- Let us extend our `CommMonoid'` to a full-fledged commutative group. -/
class CommGroup'' (G : Type*) extends CommMonoid' G where
  inv : G → G
  mul_inv_cancel' : ∀ g : G, inv g * g = 1

-- The class `Inv` also provides the notation `⁻¹` (`\^-`)
#check Inv

/- The way it is done in Mathlib is to separate *data* such as `inv` from
  their properties such as `mul_inv_cancel` -/
class CommGroup' (G : Type*) extends CommMonoid' G, Inv G where
  mul_inv_cancel' : ∀ g : G, g⁻¹ * g = 1

-- An annoying thing now is that we need to explicitly refer to the various levels of the hierarchy
-- when referencing properties
#check CommGroup'.mul_inv_cancel'
#check CommMonoid'.mul_comm'
-- #check mul_comm' -- This doesn't work

-- The `export` command can fix this: it moves identifiers from a given namespace into the current namespace
export CommMonoid' (mul_assoc' mul_one' mul_comm' mul')
export CommGroup' (mul_inv_cancel')

#check mul_comm' -- Now this works
#check mul_assoc'

theorem inv_mul_cancel {G : Type*} [CommGroup' G] (g : G) : g * g⁻¹ = 1 := by
  -- rw [mul_comm'] -- This doesn't work because `rw` because `mul_comm'` was not defined in terms of `*`
  change mul' g g⁻¹ = 1
  rw [mul_comm']
  exact mul_inv_cancel' _

end Points


section Graphs

/- # Another example: Implementing graphs -/

#check SimpleGraph -- A Mathlib definition

/- Let's define undirected graphs (allowing loops) -/
structure Graph (V : Type*) [Fintype V] where
  adj : V → V → Prop -- adjacency relation
  symm : ∀ v w : V, adj v w = adj w v

variable {V : Type*} [Fintype V]

namespace Graph

/- It's also easy to define complete graphs -/
def completeGraph (V : Type*) [Fintype V] : Graph V where
  adj := fun v w ↦ v ≠ w
  symm := by intro v w; simp; tauto

-- `abbrev` is like `def` but telling Lean to always unfold this definition
abbrev K (n : ℕ) := completeGraph (Fin n)

-- This is equivalent to marking `def` with the attribute `@[reducible]`
-- @[reducible]
-- def K (n : ℕ) := completeGraph (Fin n)

#check K 4

def edges (G : Graph V) : Set (V × V) := { (v, w) | G.adj v w }

#check edges (K 4)

-- Because `edges` lives in the namespace `Graph` and its first argument is of type `Graph`
-- we can use the following useful notation
#check (K 4).edges -- Equivalent to `edges (K 4)`

/- # Digression -/

-- #eval edges (K 4) -- Lean can't compute with `Sets`, so `#eval` won't work

#check Decidable -- `Decidable` instances can be used to generate code that can be used for computations, e.g. in `#eval`
#check DecidableRel
#check DecidableEq

variable (G : Graph V)

-- How do we convince Lean to compute the (finite) edge set of a graph for us?
-- In this definition we need to *assume* that `G.adj` is decidable
def edges' [DecidableRel G.adj] : Finset (V × V) := { (v, w) | G.adj v w }

-- #eval edges' (K 4) -- This still doesn't work because Lean doesn't know how to make a `DecidableRel`
--                    -- instance for `(K 4).adj`

-- We should tell Lean how to decide the `adj` of a complete graph if vertex equality is decidable
instance [DecidableEq V] : DecidableRel (completeGraph V).adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ v ≠ w)

#eval edges' (K 4) -- Now this works

-- We can also compute other graph properties, e.g. degree of a vertex

-- By default Lean tries to compile some code that can be used to actually evaluate functions
-- we define on explicit inputs, but here this will fail because `Set.ncard` is generally not computable,
-- if we mark definitions with `noncomputable` Lean will not attempt to compile code
noncomputable def degree' [DecidableRel G.adj] (v : V) : ℕ := { w | G.adj v w }.ncard

-- In this case we can adjust the definition slightly to make the compilation go through
-- (the degree of a vertex in a finite graph with computable adjacencies is computable)
def degree [DecidableRel G.adj] (v : V) : ℕ := ({ w | G.adj v w } : Finset V).card

#eval degree (K 4) 0

end Graph

end Graphs

end Course.Week5
