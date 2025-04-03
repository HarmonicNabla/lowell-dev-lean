import Course.Common
import Mathlib.Analysis.SpecialFunctions.Integrals

set_option linter.unusedTactic false

/-
Today: Integrals

Recommended reading: MIL Ch. 12.1

-/

namespace Course.Week8

open Real
open intervalIntegral Interval

/-
In Lean, integrals are defined using *measure theory*, but we'll not assume or need
any knowledge of measure theory here. -/
noncomputable abbrev length := @MeasureTheory.volume ℝ inferInstance

/- We'll only work with integrals of functions on intervals -/
#check intervalIntegral
#check MeasureTheory.integral -- `intervalIntegral` is defined as a special case of the *Bochner integral*

variable {f : ℝ → ℝ}
variable {a b : ℝ}

-- Type `∫` using `\integral`
#check ∫ x in a..b, f x   -- The integral of `f` on the interval `[a,b]`

#check integral_id
example (h : ℝ) : (∫ x in (0:ℝ)..h, x) = h ^ 2 / 2 := by
  sorry

#check integral_pow
example (h : ℝ) : (∫ x in (0:ℝ)..h, x ^ 2) = h ^ 3 / 3 := by
  sorry

-- Integrals of special functions
#check integral_sin
example : ∫ x in (0:ℝ)..2 * π, sin x = 0 := by
  sorry

#check integral_cos
#check integral_exp

-- As usual the interval is defined for all integrands, but it equals the junk value 0 if the integrand is not integrable
#check IntervalIntegrable

#check integral_add
#check integral_const_mul
#check ContinuousOn.intervalIntegrable
example (h : ℝ) : (∫ x in (0:ℝ)..h, 2 * x + x ^ 3) = h ^ 2 + h ^ 4 / 4 := by
  sorry

#check [[a, b]] -- Alternative notation for intervals that also works when `b < a` (then it means `[b, a]`)
-- The fundamental theorem of calculus
#check integral_deriv_eq_sub
example (hdiff : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x) (hint : IntervalIntegrable (deriv f) length a b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  sorry

-- The (other part of the) fundamental theorem calculus
#check Continuous.deriv_integral
example (hcont : Continuous f) (x : ℝ): deriv (fun x ↦ ∫ t in (0:ℝ)..x, f t) x = f x := by
  sorry

-- Mathlib has lots of FTC variants
#check integral_eq_sub_of_hasDerivAt
#check integral_hasStrictDerivAt_right
#check integral_hasStrictDerivAt_left

#check integral_mul_deriv_eq_deriv_mul -- Integration by parts
#check integral_comp_smul_deriv -- Integration by substitution

open Finset

-- Rewriting under binders: `simp_rw`


example {F : ℕ → ℝ → ℝ} (hF : ∀ n, Continuous (F n)) (N : ℕ) (a b : ℝ) : ∑ n ∈ range N, ∫ x in a..b, F n x = ∫ x in a..b, (∑ n ∈ range N, F n x) := by
  sorry

end Course.Week8
