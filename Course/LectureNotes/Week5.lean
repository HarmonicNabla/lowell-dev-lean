import Course.Common
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option linter.unusedTactic false

/-
Today: Structures

Recommended reading: MIL Ch. 6 and 7; TPL Ch. 9

-/

namespace Course.Week5

section Points

/- Structures are essentially inductive types with a single constructor
  and are used to *bundle* data and/or properties of data. -/
structure Point (α : Type*) where
  x : α
  y : α

-- The constructor of a structure is named `mk` by default
#check Point.mk

-- We can use familiar notation to build instance
def myZero : Point ℤ := ⟨0, 0⟩

def A : Point ℤ := ⟨1, 2⟩

--#eval A + A -- This doesn't work because we haven't told Lean how to add `Point ℤ` instances

def add : Point ℤ → Point ℤ → Point ℤ := fun a b ↦ ⟨a.1 + b.1, a.2 + b.2⟩

#eval add A A -- Now this works
-- #eval A + A -- This still doesn't work

end Points

section Typeclasses

-- The `+` notation is overloaded in Lean using a *typeclass*
/-
A typeclass is just like a structure but with extra functionality:
 Lean keeps an internal record of instances of typeclasses and tries to
-/


#check HAdd
instance : HAdd (Point ℤ) (Point ℤ) (Point ℤ) := ⟨add⟩
#eval A + A

end Typeclasses

section Graphs

#check SimpleGraph

structure Graph (V : Type*) [Fintype V] where
  adj : V → V → Prop
  symm : ∀ v w : V, adj v w = adj w v

variable {V : Type*} [Fintype V]

def completeGraph (V : Type*) [Fintype V] : Graph V where
  adj := fun v w ↦ v ≠ w
  symm := by intro v w; simp; tauto

instance [DecidableEq V] : DecidableRel (completeGraph V).adj :=
  inferInstanceAs <| DecidableRel (fun v w ↦ v ≠ w)

@[reducible]
def K (n : ℕ) := completeGraph (Fin n)

#check completeGraph (Fin 2)

variable (G : Graph V)

def edges : Set (V × V) := { (v, w) | G.adj v w }

def degree [DecidableRel G.adj] (v : V) : ℕ := ({ w | G.adj v w } : Finset V).card

def edges' [DecidableRel G.adj] : Finset (V × V) := { (v, w) | G.adj v w }

#eval degree (K 3) default

#eval edges' (K 3)
#eval (edges' (K 3)).card

end Graphs

end Course.Week5
