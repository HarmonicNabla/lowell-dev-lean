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
def oddNumbers : Set ℕ := { n | Odd n }

/- Type `∈` by `\in` -/
#check Membership.mem

/- `n ∈ oddNumbers` is *definitionally equal* to `Odd n` -/
example: n ∈ oddNumbers ↔ Odd n := by rfl

example : 7 ∈ oddNumbers := by
  change Odd 7  -- `change` allows us to change the goal into anything that is definitionally equal to it
                -- (can usually be omitted)
  use 3
  rfl

/- A shorter way to write this proof -/
example : 7 ∈ oddNumbers := ⟨3, by rfl⟩

/- There is also `∉` (type `\notin`)-/
example : 2 ∉ oddNumbers := by
  change ¬ Odd 2
  sorry

/- Two sets are equal if they have the same elements.
  This is called *extensionality* and we can invoke this principle using the tactic `ext` -/
example : oddNumbers = {n | ∃ k, n = k + k + 1 } := by
  ext n
  constructor <;> {
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
  -- change ∀ n, Odd n → n ≥ 1
  intro n hn
  dsimp       -- simplify using only definitional equality
  obtain ⟨k, hk⟩ := hn
  sorry

example : A ⊆ B ∧ B ⊆ C → A ⊆ C := by
  -- rintro ⟨h, h'⟩ _ ha -- `rintro` can introduce hypotheses and deconstruct them at the same time
  -- exact h' (h ha)
  sorry

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
  constructor
  · rintro (_ | _)
    · right; assumption
    · left; assumption
  · sorry
  -- simp [or_comm]

/- We can use `simp` & `tauto` to automate a lot of the legwork -/
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext
  simp
  tauto

/- Empty set
   Type using `\emptyset`
 -/
example : x ∈ (∅ : Set α) ↔ False := by rfl

#check Set.ext_iff

example (h : A ∩ B = ∅) : x ∈ A → x ∉ B := by
  intro ha
  simp [Set.ext_iff] at h
  exact h x ha
  --simp_all [Set.ext_iff] -- `simp_all` repeatedly simplifies goal and hypotheses until no further simplification is possible

/- Universal set -/
example : x ∈ Set.univ ↔ True := by rfl

/- Let's do one more example on foot (without `simp` / `tauto`). -/
example : A \ B ∪ B = B ∪ A := by
  sorry

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
  · sorry
    -- simp
    -- rintro x (hx|hx) hx'
    -- · left; use x
    -- · right; use x

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
  sorry

/- Properties of functions -/

#check Injective f
#check Surjective f
#check Bijective f

variable {γ : Type*} {g : β → γ}

example (hf : Injective f) (hg : Injective g): Injective (g ∘ f) := by
  sorry

--variable {α β : Type*} [Inhabited α]

open Classical

variable [Inhabited α]

#check (default : α) -- Inhabitated types provide a default element
#eval (default : ℕ)

#check Nonempty -- Compare `Inhabitated` to `Nonempty`

/- Let us do a slightly more involved example -/
example : (∃ f : α → β, Injective f) ↔ ∃ g : β → α, Surjective g := by
  constructor
  · -- Let `f` be injective
    rintro ⟨f, hf⟩
    -- Then define `g y` to be `x` such that `f x = y` if `y` is in the range of `f`, and any element otherwise
    -- Note here we use Lean's version of the axiom of choice
    #check Classical.choice
    -- We can introduce local definitions using `let`
    let g : β → α := sorry
    -- To show that `g` is surjective it suffices to show `g (f x) = x` for every `x`.

    -- `g (f x) = x` holds because `f` is injective
    #check dif_pos
    #check Classical.choose_spec
    sorry
  · -- Let `g` be surjective.
    rintro ⟨g, hg⟩
    -- Define `f x` to be an element `y` such that `g y = x` (exists because `g` is surjective)
    let f : α → β := sorry
    -- To show that `f` is injective, let `x, x'` such that `f x = f' x`.

    -- Then `x = g (f x) = g (f x') = x'` by definition of `g`.
    sorry

open Real

example : Bijective (fun x : ℝ ↦ 2 * x) := by
  sorry

/- Lean knows about standard functions and their properties -/
#check exp
#check sin
#check cos
#check log    /- In Lean `log x` is defined for all real numbers `x`. If `x ≤ 0` it uses a junk value. -/

example : log 1 = 0 := log_one

example : Injective exp := exp_injective

#check InjOn

example : InjOn (fun x : ℝ ↦ x^2) {x | 0 ≤ x} := by
  intro x hx y hy h
  dsimp at *    -- simplify using only definitional equality at goal and all hypotheses
  calc
    _ = √(x^2) := by rw [sqrt_sq_eq_abs, abs_of_nonneg hx]
    _ = √(y^2) := by rw [h]
    _ = _      := by rw [sqrt_sq_eq_abs, abs_of_nonneg hy]

#check range

example : range exp = {x | 0 < x} := by
  sorry


end Functions

end Course
