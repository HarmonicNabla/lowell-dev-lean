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
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-- Show that the set of subsets of `ℝ` that contain an open interval of the form `(-ε, ε)` form a filter.
example : Filter ℝ where
  sets := { s | ∃ ε > 0, ∀ x, |x| < ε → x ∈ s }
  univ_sets := by
    sorry
  sets_of_superset := by
    sorry
  inter_sets := by -- Hint: Use the minimum of `ε₁` and `ε₂`
    sorry

end

section

open Real Filter Topology

#check abs_le
example (f : ℝ → ℝ) (h₁ : ∀ᶠ x in atTop, f x ≤ 1) (h₂ : ∀ᶠ x in atTop, -1 ≤ f x) :
    ∀ᶠ x in atTop, |f x| ≤ 1 := by -- Hint: Use `filter_upwards`
  sorry

example (p : ℕ → Prop) (q : ℕ → Prop) (h₁ : ∀ᶠ n in atTop, p n)
    (h₂ : ∀ᶠ n in atTop, ¬ q n) : ∀ᶠ n in atTop, ¬ (q n ∨ ¬ p n) := by
  sorry

#check exp_lt_one_iff
example (a : ℕ → ℝ) (h : Tendsto a atTop atBot): ∀ᶠ n in atTop, exp (1 + a n) < 1 := by
  sorry

#check sin_int_mul_pi
#check Int.le_ceil
-- Show that `sin x` is zero for arbitrarily large values of `x`.
example : ∃ᶠ x in atTop, sin x = 0 := by
  sorry

end

end HW6
