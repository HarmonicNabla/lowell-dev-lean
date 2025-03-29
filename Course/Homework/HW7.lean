import Course.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Convex.Deriv

set_option linter.unusedTactic false
/-

Homework sheet 7
Due Apr 3 10am

All problems are mandatory unless stated otherwise.

Optional: Do all the problems in MIL Ch. 11.1

-/

namespace HW7

open Real Set Function

-- State and prove that the derivative of `1 / 3 * x ^ 3` equals `x ^ 2` (for all `x`).
example (x : ℝ) : sorry := sorry

#check HasDerivAt.exp
example (x : ℝ) : deriv (fun x ↦ exp (x ^ 2)) x = 2 * x * exp (x ^ 2) := by
  sorry

-- Compute the 4th order derivative of `sin`
lemma deriv4_sin : deriv^[4] sin = fun x ↦ sin x := by
  sorry

variable {f : ℝ → ℝ}

example (x : ℝ) : DifferentiableAt ℝ f x → ContinuousAt f x := by
  sorry

-- Recall from calculus that a function is strictly increasing if its derivative is positive.
#check strictMonoOn_of_deriv_pos
example : StrictMonoOn (fun x : ℝ ↦ x ^ 2 + exp x) (Ici 0) := by
  have hd {x : ℝ} : deriv (fun x : ℝ ↦ x ^ 2 + exp x) x = 2 * x + exp x := by
    sorry

  apply strictMonoOn_of_deriv_pos
  · sorry
  · sorry
  · sorry

#check two_le_pi
#check intermediate_value_Icc'
-- Use the intermediate value theorem to show:
example : ∃ x ∈ Icc 0 π, 1 + x * cos x = 0 := by
  sorry

-- Recall from calculus that a function is concave if its second derivative is `≤ 0`.
-- Use this to prove that the function `f(x)=x*(1-x)` is concave.
#check concaveOn_of_deriv2_nonpos
example : ConcaveOn ℝ (Icc 0 1) (fun x : ℝ ↦ x * (1 - x)) := by
  have hd1 : deriv (fun x : ℝ ↦ x * (1 - x)) = fun x ↦ 1 - 2 * x := by
    sorry
  have hd2 : deriv^[2] (fun x : ℝ ↦ x * (1 - x)) = fun _ ↦ -2 := by
    sorry

  sorry -- Use `concaveOn_of_deriv2_nonpos`

end HW7
