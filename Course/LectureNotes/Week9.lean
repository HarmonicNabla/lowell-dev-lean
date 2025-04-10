import Course.Common

/-
Today: Formalization practice

-/

namespace Course.Week9

/- Let us practice putting together what we have learned by formalizing a mathematically interesting theorem:

*Riemann-Lebesgue lemma*
Let `f : [a, b] → ℝ` be continuously differentiable.
Then `∫ x in a..b, sin (R * x) * f x` converges to `0` as `R → ∞`.
 -/

open intervalIntegral

#check integral_mul_deriv_eq_deriv_mul

#check Metric.tendsto_atTop
#check IsCompact.exists_bound_of_continuousOn
#check isCompact_uIcc

#check abs_integral_le_integral_abs
#check integral_mono_on

theorem riemannLebesgue {a b : ℝ} (hab : a ≤ b) : True := sorry

end Course.Week9
