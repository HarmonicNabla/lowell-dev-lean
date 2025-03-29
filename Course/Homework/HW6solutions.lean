import Course.Common

set_option linter.unusedTactic false
/-

Homework sheet 6
Due March 27 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 10.1

-/

namespace HW6

section

open Filter

variable {α : Type*} {s₀ : Set α}
-- Show that the set of sets that contain `s₀` is a filter.
-- (as an extra challenge try to do this without using any tactics)
example : Filter α where
  sets := { s | s₀ ⊆ s }
  univ_sets := fun _ _ ↦ True.intro
  sets_of_superset := fun hs hs' _ h ↦ hs' <| hs h
  inter_sets := fun hs hs' _ h ↦ ⟨hs h, hs' h⟩

-- Show that the set of subsets of `ℝ` that contain an open interval of the form `(-ε, ε)` form a filter.
example : Filter ℝ where
  sets := { s | ∃ ε > 0, ∀ x, |x| < ε → x ∈ s }
  univ_sets := by use 1; simp
  sets_of_superset := by
    rintro s s' ⟨ε, hε, hε'⟩ hs'
    use ε
    exact ⟨hε, fun x hx ↦ hs' <| hε' x hx⟩
  inter_sets := by -- Hint: Use the minimum of `ε₁` and `ε₂`
    rintro s s' ⟨ε₁, hε₁, hε₁'⟩ ⟨ε₂, hε₂, hε₂'⟩
    use min ε₁ ε₂
    constructor
    · exact lt_min hε₁ hε₂
    · intro x hx
      refine ⟨hε₁' x ?_, hε₂' x ?_⟩
      · exact Trans.trans hx <| min_le_left _ _
      · exact Trans.trans hx <| min_le_right _ _

end

section

open Real Filter Topology

#check abs_le
example (f : ℝ → ℝ) (h₁ : ∀ᶠ x in atTop, f x ≤ 1) (h₂ : ∀ᶠ x in atTop, -1 ≤ f x) :
    ∀ᶠ x in atTop, |f x| ≤ 1 := by
  filter_upwards [h₁, h₂] with x hx hx'
  exact abs_le.mpr ⟨hx', hx⟩

example (p : ℕ → Prop) (q : ℕ → Prop) (h₁ : ∀ᶠ n in atTop, p n)
    (h₂ : ∀ᶠ n in atTop, ¬ q n) : ∀ᶠ n in atTop, ¬ (q n ∨ ¬ p n) := by
  filter_upwards [h₁, h₂] with n hn hn'
  tauto

#check exp_lt_one_iff
example (a : ℕ → ℝ) (h : Tendsto a atTop atBot): ∀ᶠ n in atTop, exp (1 + a n) < 1 := by
  rw [tendsto_atTop_atBot] at h
  obtain ⟨N, hN⟩ := h (-2)
  rw [eventually_atTop]
  use N
  intro n hn
  specialize hN n hn
  rw [exp_lt_one_iff]
  linarith only [hN]

#check sin_int_mul_pi
#check Int.le_ceil
-- Show that `sin x` is zero for arbitrarily large values of `x`.
example : ∃ᶠ x in atTop, sin x = 0 := by
  rw [frequently_atTop]
  intro L
  use ⌈L / π⌉ * π
  constructor
  · calc
      _ ≥ (L / π) * π := by gcongr; exact Int.le_ceil _
      _ = L := by field_simp
  · exact sin_int_mul_pi _

end

end HW6
