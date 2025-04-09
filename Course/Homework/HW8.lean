import Course.LectureNotes.Week8

/-

Homework sheet 8
Due Apr 17 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 12.1

-/

namespace HW8

open Real Interval Course Course.Week8

section

open intervalIntegral Finset

-- Use Lean to compute the following integrals: reasonably simplify your answers as much as possible
#check integral_sub
example : ∫ x in (0:ℝ)..1, 5 * x ^ 4 - 3 * x ^ 2 + x = sorry := by
  sorry

#check sin_sq_add_cos_sq
example : ∫ x in (0:ℝ)..1, 2 * (1 - (sin x) ^ 2 - (cos x) ^ 2) ^ 2 = sorry := by
  sorry

#check integral_comp_const_mul
#check exp_mul
#check rpow_natCast
example : ∫ x in (0:ℝ)..5, (exp x) ^ 2 = sorry := by
  sorry

-- Here is an example for integration by parts
#check integral_mul_deriv_eq_deriv_mul
#check Real.deriv_exp
example : ∫ x in (0:ℝ)..1, x * exp x = sorry := by
  calc
    -- Prepare for application of integration by parts
    _ = ∫ x in (0:ℝ)..1, x * (deriv exp x) := by sorry
    -- Apply integration by parts
    _ = exp 1 - ∫ x in (0:ℝ)..1, (deriv id x) * exp x := by
      -- rw [integral_mul_deriv_eq_deriv_mul (u' := sorry) (v := sorry)]
      sorry
    _ = _ := by
      sorry

section

open NNReal

variable {f : ℝ → ℝ} (hf : Continuous f)

#check abs_integral_le_integral_abs -- Triangle inequality for integrals
#check integral_mono -- Monotonicity of integrals
#check smul_eq_mul
-- Let us prove a basic, but very useful estimate for integrals
example (h L : ℝ≥0) (hf' : ∀ x, |f x| ≤ L) : |∫ x in (0:ℝ)..h, f x| ≤ h * L := by
  calc
    _ ≤ ∫ x in (0:ℝ)..h, |f x| := sorry
    _ ≤ ∫ x in (0:ℝ)..h, L.val := sorry
    _ = _ := by sorry

end

end

section Fubini

open MeasureTheory Function Set

variable {a b : ℝ}

variable {f : ℝ → ℝ → ℝ} -- Let `f` be a function of 2 real variables.

#check uncurry f -- This is `f` written as a function of pairs `(x, y)` which is closer to what we would write on paper

-- This one is *optional* -- see it as a challenge.
-- Let us deduce Fubini's theorem on interchanging double integrals on intervals
-- from the more general Fubini theorem in Mathlib.
#check integral_integral_swap -- Fubini in Mathlib
theorem integral_integral_swap_of_continuous (hf : Integrable (uncurry f) ((length.restrict (Ι a b)).prod (length.restrict (Ι a b)))) :
    ∫ x in a..b, ∫ y in a..b, f x y = ∫ y in a..b, ∫ x in a..b, f x y := by
  sorry -- *optional*

-- If you want yet more challenge, try this (also *optional*):
-- The assumption in the previous theorem looks a little technical but it follows from continuity.
-- Look for appropriate lemmas in Mathlib.
#check Measure.prod_restrict -- Start with this
#check ContinuousOn.integrableOn_compact -- Continuous functions are integrable on compact sets.
-- Note the half-open interval `I a b` is not compact because it is not closed.
-- But it is contained in the closed interval `uIcc a b` which is compact, so you should also use:
#check IntegrableOn.mono_set
theorem integrable_uncurry_restrict_prod_of_continuous_uncurry (hf : Continuous (uncurry f)) :
    Integrable (uncurry f) ((length.restrict (Ι a b)).prod (length.restrict (Ι a b))) := by
  sorry -- *optional*

end Fubini

end HW8
