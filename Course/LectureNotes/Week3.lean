import Course.Common

set_option linter.unusedTactic false

/-
Today: Sets and Functions

Recommended reading: MIL Ch. 4

-/

/- # Sets -/

namespace Course

section Sets

variable {α : Type*} {x : α} {A B C : Set α}
variable {n : ℕ}

open Set

#check Set -- A set is represented in Lean by a function from the type of elements to `Prop`

/- We can define sets in Lean using familiar syntax -/
def oddNumbers : Set ℕ := { n : ℕ | Odd n }

/- Type `∈` by `\in` -/
#check Membership.mem

/- `n ∈ oddNumbers` is *definitionally equal* to `Odd n` -/
example: n ∈ oddNumbers ↔ Odd n := by rfl

example : 7 ∈ oddNumbers := by
  change ∃ k, 7 = 2*k+1  -- `change` allows us to change the goal into anything that is definitionally equal to it
                -- (can usually be omitted)
  --unfold Odd
  use 3
  -- rfl

/- A shorter way to write this proof -/
example : 7 ∈ oddNumbers := ⟨3, by rfl⟩

/- There is also `∉` (type `\notin`)-/
example : 2 ∉ oddNumbers := by
  change ¬ Odd 2
  exact Nat.not_odd_iff.mpr rfl

#check Nat.not_odd_iff.mpr

/- Two sets are equal if they have the same elements.
  This is called *extensionality* and we can invoke this principle using the tactic `ext` -/
example : oddNumbers = {n | ∃ k, n = k + k + 1 } := by
  ext n
  constructor
  -- · rintro ⟨k, hk⟩
  --   use k
  --   simp [hk, two_mul]
  -- · rintro ⟨k, hk⟩
  --   use k
  --   simp [hk, two_mul]
  <;> {
    rintro ⟨k, hk⟩
    use k
    simp [hk, two_mul]
  }

/- Set operations correspond to logical connectives -/

example : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by rfl

/- The subset relation can be thought of as an implication
  Type `⊆` using `\subset`
-/
example : oddNumbers ⊆ { n | n ≥ 1} := by
  --change ∀ n, Odd n → n ≥ 1
  rintro n ⟨k, hk⟩
  -- change n ≥ 1
  dsimp       -- simplify using only definitional equality
  -- obtain ⟨k, hk⟩ := hn
  rw [hk]
  exact Nat.le_add_left 1 (2 * k)

#check subset_trans -- slightly different definition

example : A ⊆ B ∧ B ⊆ C → A ⊆ C := by
  -- tauto
  rintro ⟨h, h'⟩ a ha -- `rintro` can introduce hypotheses and deconstruct them at the same time
  -- have : a ∈ B := h ha
  exact h' (h ha)

/- Unions
  Type `∪` using `\un` -/
example : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by rfl
#check mem_union

/- Intersections
  Type `∩` using `\cap` -/
example : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by rfl
#check mem_inter

/- Complements
  Type `ᶜ` using `\compl` -/
example : x ∈ Aᶜ ↔ x ∉ A := by rfl
#check mem_compl

/- Set difference -/
example : x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by rfl
#check mem_diff

example : A ∪ B = B ∪ A := by
  ext
  constructor <;> {
    rintro (_ | _)
    · right; assumption
    · left; assumption
  }
  -- ext
  -- simp [or_comm]

/- We can use `simp` & `tauto` to automate a lot of the legwork -/
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext
  simp? -- `simp?` asks Lean to tell us what `simp` lemmas were used
  tauto

/- Empty set
   Type using `\emptyset`
 -/
example : x ∈ (∅ : Set α) ↔ False := by rfl

#check Set.ext_iff -- useful when set equality appears as hypothesis

example (h : A ∩ B = ∅) : x ∈ A → x ∉ B := by
  -- intro ha
  -- simp [Set.ext_iff] at h
  -- exact h x ha
  simp_all [Set.ext_iff] -- `simp_all` repeatedly simplifies goal and hypotheses until no further simplification is possible

/- Universal set -/
example : x ∈ Set.univ ↔ True := by rfl

/- Let's do one more example on foot (without `simp` / `tauto`). -/
example : A \ B ∪ B = B ∪ A := by
  ext x
  constructor
  · rintro (⟨_, _⟩ | _)
    · right; assumption
    · left; assumption
  · rintro (h | h)
    · right; assumption
    · by_cases h' : x ∈ B
      · right; assumption
      · left; exact ⟨h, h'⟩

end Sets

/- # Functions -/

section Functions

open Set Function

variable {α β : Type*} {f g : α → β}

/- Define functions using the keyword `fun`
   Type `↦` using `\mapsto`
   Carefully note the difference between `→` and `↦`
-/
def myFunction : ℕ → ℕ := fun n ↦ 2 * n + 3

/- `fun` is preferred over the alternative name `λ` (like `lambda` in Python. The name is motivated by `lambda calculus`)
  `=>` is alternative notation for `↦`
-/

#eval myFunction 2

/- Remember that implications and universal quantifiers are function types, so
  we can also use `fun` to construct proof terms -/
example : ∀ n : ℕ, n^2 + 1 = 1 + n * n := fun n ↦ by ring

variable {s t : Set α} {v u : Set β} {x : α} {y : β}

/- Images -/
#check f '' s
#check image

example : y ∈ f '' s ↔ ∃ x ∈ s, f x = y := by rfl
#check mem_image

example : f '' s ∪ f '' t = f '' (s ∪ t) := by
  ext y
  constructor
  · rintro (⟨x, hx, hx'⟩|⟨x, hx, hx'⟩)
    · use x; exact ⟨Or.inl hx, hx'⟩
    · use x; exact ⟨Or.inr hx, hx'⟩
  · simp
    rintro x (hx|hx) hx'
    · left; use x
    · right; use x

example : f '' s ∪ f '' t = f '' (s ∪ t) := by
  aesop

/- Preimages
   Type `⁻¹` using `\-1`
 -/
#check preimage
#check f ⁻¹' u

example : x ∈ f ⁻¹' u ↔ f x ∈ u := by rfl
#check mem_preimage

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  exact preimage_inter

/- Properties of functions -/

#check Injective f
#check Surjective f
#check Bijective f

variable {γ : Type*} {g : β → γ}

example (hf : Injective f) (hg : Injective g): Injective (g ∘ f) := by
  intro x y h
  -- have := hg h
  -- have := hf this
  -- assumption
  exact hf (hg h)

--variable {α β : Type*} [Inhabited α]

open Classical

variable [Inhabited α]

#check (default : α) -- Inhabitated types provide a default element
#eval (default : ℕ)
#eval (default : ℝ)

#check Nonempty -- Compare `Inhabitated` to `Nonempty`

/- Let us do a slightly more involved example -/
example : (∃ f : α → β, Injective f) ↔ ∃ g : β → α, Surjective g := by
  constructor
  · -- Let `f` be injective
    rintro ⟨f, hf⟩
    -- Then define `g y` to be `x` such that `f x = y` if `y` is in the range of `f`, and any element otherwise
    -- Note here we use Lean's version of the axiom of choice
    #check Classical.choice
    #check Classical.choose
    -- We can introduce local definitions using `let`
    let g : β → α := fun y ↦ if h : y ∈ range f then choose h else default
    #check ite
    #check dite
    use g
    -- To show that `g` is surjective it suffices to show `g (f x) = x` for every `x`.
    intro x
    use f x
    -- `g (f x) = x` holds because `f` is injective
    #check dif_pos
    #check Classical.choose_spec
    have h : f x ∈ range f := by use x
    have : g (f x) = choose h := dif_pos h
    have : f (choose h) = f x := choose_spec h
    have : choose h = x := hf this
    calc
      g (f x) = choose h := by assumption
      _ = x := by assumption
  · -- Let `g` be surjective.
    rintro ⟨g, hg⟩
    -- Define `f x` to be an element `y` such that `g y = x` (exists because `g` is surjective)
    #check hg x
    let f : α → β := fun x ↦ choose (hg x)
    use f
    -- To show that `f` is injective, let `x, x'` such that `f x = f' x`.
    intro x x' h
    -- Then `x = g (f x) = g (f x') = x'` by definition of `g`.
    calc
      _ = g (f x) := by rw [choose_spec (hg x)]
      _ = g (f x') := by rw [h]
      _ = x' := by rw [choose_spec (hg x')]

open Real

example : Bijective (fun x : ℝ ↦ 2 * x) := by
  constructor
  · intro x y h
    dsimp at h
    #check mul_left_cancel₀
    refine mul_left_cancel₀ ?_ h    -- `refine` is like `exact` except you can use holes `?_` that will become new subgoals
    norm_num
    -- exact mul_left_cancel₀ (by norm_num) h
  · intro y
    dsimp
    use (y/2)
    ring

/- Lean knows about standard functions and their properties -/
#check exp
#check Complex.exp
#check sin
#check cos
#check log    /- In Lean `log x` is defined for all real numbers `x`. If `x ≤ 0` it uses a junk value. -/

#check exp_add
#check exp_zero
#check exp_neg
#check exp_pos

example : log 1 = 0 := log_one

example : log 0 = 0 := log_zero

#check log_mul

example : Injective exp := exp_injective

#check InjOn

example : InjOn (fun x : ℝ ↦ x^2) {x | 0 ≤ x} := by
  intro x hx y hy h
  dsimp at *    -- simplify using only definitional equality at goal and all hypotheses
  calc
    _ = √(x^2) := by rw [sqrt_sq_eq_abs, abs_of_nonneg hx]    -- `\sqrt`
    _ = √(y^2) := by rw [h]
    _ = _      := by rw [sqrt_sq_eq_abs, abs_of_nonneg hy]

#check range

example : range exp = {y | 0 < y} := by
  exact range_exp

#check Icc 0 1    -- closed interval `[0, 1]`
#check Ioo 0 1    -- open interval `(0, 1)`
#check Ioc 0 1    -- half-open interval `(0, 1]`

end Functions

end Course
