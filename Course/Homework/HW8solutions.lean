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
example : ∫ x in (0:ℝ)..1, 5 * x ^ 4 - 3 * x ^ 2 + x = 1 / 2 := by
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_pow, integral_pow, integral_id]
  · norm_num
  all_goals { apply ContinuousOn.intervalIntegrable; fun_prop }

#check sin_sq_add_cos_sq
example : ∫ x in (0:ℝ)..1, 2 * (1 - (sin x) ^ 2 - (cos x) ^ 2) ^ 2 = 0 := by
  simp_rw [sub_sub, sin_sq_add_cos_sq]
  rw [integral_const]
  simp

#check integral_comp_const_mul
#check exp_mul
#check rpow_natCast
example : ∫ x in (0:ℝ)..5, (exp x) ^ 2 = 1 / 2 * (exp (10) - 1) := by
  calc
    _ = ∫ x in (0:ℝ)..5, exp (2 * x) := by
      congr! with x; rw [mul_comm, exp_mul, ← rpow_natCast]; rfl
    _ = 1 / 2 * ∫ x in (0:ℝ)..10, exp x := by
      convert integral_comp_const_mul _ 2 (by positivity)
      · norm_num
      · norm_num
      · fun_prop
    _ = 1 / 2 * (exp (10) - 1) := by rw [integral_exp]; simp

-- Here is an example for integration by parts
#check integral_mul_deriv_eq_deriv_mul
#check Real.deriv_exp
example : ∫ x in (0:ℝ)..1, x * exp x = 1 := by
  calc
    -- Prepare for application of integration by parts
    _ = ∫ x in (0:ℝ)..1, x * (deriv exp x) := by simp_rw [Real.deriv_exp]
    _ = exp 1 - ∫ x in (0:ℝ)..1, (deriv id x) * exp x := by
      -- Apply integration by parts
      rw [integral_mul_deriv_eq_deriv_mul (u' := fun _ ↦ 1) (v := exp)]
      · simp
      · exact fun _ _ ↦ hasDerivAt_id _
      · intro _ _
        convert hasDerivAt_exp _
        exact Real.deriv_exp
      · apply ContinuousOn.intervalIntegrable; fun_prop
      · rw [Real.deriv_exp]; apply ContinuousOn.intervalIntegrable; fun_prop
    _ = _ := by
      simp_rw [deriv_id, one_mul]
      rw [integral_exp]
      simp

variable {f : ℝ → ℝ} (hf : Continuous f)

#check abs_integral_le_integral_abs -- Triangle inequality for integrals
#check integral_mono -- Monotonicity of integrals
#check smul_eq_mul
open NNReal in
example (h L : ℝ≥0) (hf' : ∀ x, |f x| ≤ L) : |∫ x in (0:ℝ)..h, f x| ≤ h * L := by
  calc
    _ ≤ ∫ x in (0:ℝ)..h, |f x| := abs_integral_le_integral_abs (by positivity)
    _ ≤ ∫ x in (0:ℝ)..h, L.val := integral_mono h.2 (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_const _) hf'
    _ = _ := by rw [integral_const, smul_eq_mul, sub_zero]; rfl



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
  repeat simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [integral_smul, integral_smul]
  congr! 2
  exact integral_integral_swap hf

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
  rw [Measure.prod_restrict]
  apply IntegrableOn.integrable
  refine IntegrableOn.mono_set (t := (uIcc a b) ×ˢ (uIcc a b)) ?_ ?_
  · apply ContinuousOn.integrableOn_compact
    · apply IsCompact.prod <;> exact isCompact_uIcc
    · exact Continuous.continuousOn hf
  · apply prod_mono <;> exact uIoc_subset_uIcc

end Fubini

end HW8
