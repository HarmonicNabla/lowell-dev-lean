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
example (x : ℝ) : deriv (fun x ↦ 1 / 3 * x ^ 3) x = x ^ 2 := by
  simp

#check HasDerivAt.exp
example (x : ℝ) : deriv (fun x ↦ exp (x ^ 2)) x = 2 * x * exp (x ^ 2) := by
  apply HasDerivAt.deriv
  convert HasDerivAt.exp (hasDerivAt_pow _ _) using 1
  ring

-- Compute the 4th order derivative of `sin`
lemma deriv4_sin : deriv^[4] sin = fun x ↦ sin x := by
  simp

variable {f : ℝ → ℝ}

example (x : ℝ) : DifferentiableAt ℝ f x → ContinuousAt f x :=
  fun h ↦ DifferentiableAt.continuousAt h

-- Recall from calculus that a function is strictly increasing if its derivative is positive.
#check strictMonoOn_of_deriv_pos
example : StrictMonoOn (fun x : ℝ ↦ x ^ 2 + exp x) (Ici 0) := by
  have hd {x : ℝ} : deriv (fun x : ℝ ↦ x ^ 2 + exp x) x = 2 * x + exp x := by
    apply HasDerivAt.deriv
    apply HasDerivAt.add
    · convert hasDerivAt_pow _ _
      rw [pow_one]
    · exact hasDerivAt_exp _
  apply strictMonoOn_of_deriv_pos
  · exact convex_Ici _
  · fun_prop
  · intro x hx
    simp at hx
    rw [hd]
    positivity

#check two_le_pi
#check intermediate_value_Icc'
-- Use the intermediate value theorem to show:
example : ∃ x ∈ Icc 0 π, 1 + x * cos x = 0 := by
  apply intermediate_value_Icc'
  · positivity
  · fun_prop
  · and_intros
    · simp; exact Trans.trans (show 1 ≤ 2 by norm_num) two_le_pi
    · simp

-- Recall from calculus that a function is concave if its second derivative is `≤ 0`.
-- Use this to prove that the function `f(x)=x*(1-x)` is concave.
#check concaveOn_of_deriv2_nonpos
example : ConcaveOn ℝ (Icc 0 1) (fun x : ℝ ↦ x * (1 - x)) := by
  have hd1 : deriv (fun x : ℝ ↦ x * (1 - x)) = fun x ↦ 1 - 2 * x := by
    ext x
    apply HasDerivAt.deriv
    convert HasDerivAt.mul (hasDerivAt_id x) (HasDerivAt.const_sub _ (hasDerivAt_id x)) using 1
    simp; ring
  have hd2 : deriv^[2] (fun x : ℝ ↦ x * (1 - x)) = fun _ ↦ -2 := by
    rw [iterate_succ, iterate_one, comp_apply, hd1]
    ext x
    apply HasDerivAt.deriv
    rw [show -2 = (0 : ℝ) - 2 by norm_num]
    apply HasDerivAt.sub
    · exact hasDerivAt_const _ _
    · convert HasDerivAt.const_mul _ (hasDerivAt_id x) using 1
      norm_num
  apply concaveOn_of_deriv2_nonpos
  · exact convex_Icc _ _
  · fun_prop
  · fun_prop
  · rw [hd1]; fun_prop
  · intro x hx
    rw [hd2]
    simp


end HW7
