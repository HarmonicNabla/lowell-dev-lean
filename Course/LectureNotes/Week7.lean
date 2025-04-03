import Course.Common
import Mathlib.Analysis.Calculus.Deriv.Abs

/-
Today: Derivatives

Recommended reading: MIL Ch. 11.1

-/

namespace Course.Week7

open Real

variable {f : ℝ → ℝ}

section Derivatives

variable {a x₀ h : ℝ}

-- The derivative of `f` is written using
#check deriv f -- The function `f'` (if it exists)

-- Note: If `f` is not differentiable, `deriv f` is defined as the junk value `0`

-- The fact that `f` has a certain derivative at a point
variable {a : ℝ}
#check HasDerivAt f a x₀ -- `f'(a) = x₀`, meaning `f` has a derivative at `x₀` and it equals `a`

-- Difference quotient definition of derivative
#check hasDerivAt_iff_tendsto

-- We can also say that `f` has a derivative without mentioning what its value is
#check DifferentiableAt ℝ f a -- `f` has a derivative at `a` (is differentiable at `a`)

-- Mathlib contains many basic derivatives
#check deriv_exp
example (x : ℝ) : deriv exp x = exp x := by simp

#check deriv_sin
example (x : ℝ) : deriv sin x = cos x := by simp

-- `simp` can also use some basic properties of derivatives
example (x : ℝ) : deriv (fun y ↦ exp (y + 2)) x = exp (x + 2) := by simp

example (x : ℝ) : deriv (fun y ↦ 2 * cos y + 5 * sin y) x = -2 * sin x + 5 * cos x := by simp

#check deriv_add -- Derivative of `f + g`
#check deriv_const -- Derivative of a constant
#check deriv_id -- Derivative of `f x = x` (`identity` function)
#check deriv_pow -- Derivative of `f x = x ^ n`

#check deriv_mul -- Product rule
example (x : ℝ) : (deriv (fun var ↦ var * sin var)) x = sin x + x * cos x := by simp

#check deriv_div -- Quotient rule
#check deriv_comp -- Chain rule

-- There are also versions of these rules for `HasDerivAt` and `DifferentiableAt`
#check HasDerivAt.mul -- Product rule
#check DifferentiableAt.mul

-- Careful: `deriv f = g` does not imply that `f` is differentiable (because of junk values)

-- For example: `deriv log` is defined everywhere and equals `x⁻¹`
#check deriv_log -- Note `log` is defined as `x ↦ log |x|` in Lean
                 -- This makes the derivative formula true for all `x` (junk values at `x = 0`)
example : deriv log 0 = 0 := by rw [deriv_log, inv_zero]

-- But of course `log |⬝|` is not differentiable at `0` and Lean knows that:
example (x : ℝ) : DifferentiableAt ℝ log x ↔ x ≠ 0 := by exact differentiableAt_log_iff

-- The absolute value function is not differentiable at `0`
example : ¬ DifferentiableAt ℝ (fun y : ℝ ↦ |y|) 0 := by
  exact not_differentiableAt_abs_zero

example (x : ℝ) : deriv (fun y ↦ y ^ 2 + exp y) x = 2 * x + exp x := by
  -- `simp` can do this too
  apply HasDerivAt.deriv
  apply HasDerivAt.add
  ·
    -- have aux : 2 * x = 2 * x ^ (2 - 1) := by simp
    -- rw [aux]
    -- exact hasDerivAt_pow _ _
    convert hasDerivAt_pow _ _ -- Note the goal doesn't match `hasDerivAt_pow` exactly
                               -- `convert` is a useful tactic for such cases: it will try
                               -- to pattern match the given term against the goal and
                               -- generate subgoals for the differences
    ring
  · exact hasDerivAt_exp _

#check HasDerivAt.const_mul
example (x : ℝ) : deriv (fun y ↦ sin (2 * y) + 3 * exp (5 * y)) x = cos (2 * x) * 2 + 15 * exp (5 * x) := by
  -- `simp` fails here
  apply HasDerivAt.deriv
  refine HasDerivAt.add ?_ ?_ -- `refine` is like `exact` except one can use `?_` for missing terms resulting in corresponding subgoals
  · convert HasDerivAt.comp x (hasDerivAt_sin _) (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id _)) using 2
    exact (mul_one _).symm
    -- convert HasDerivAt.comp x (hasDerivAt_sin _) (HasDerivAt.const_mul (2 : ℝ) <| hasDerivAt_id _) using 2
    -- sorry
  · convert HasDerivAt.const_mul (3 : ℝ) _ using 1
    rotate_left -- Change order of subgoals
    exact 5 * exp (5 * x) -- A goal doesn't have to be a proposition!
    · convert HasDerivAt.exp (HasDerivAt.const_mul (5 : ℝ) (hasDerivAt_id _)) using 1
      simp; ring
    · ring

end Derivatives

section Intervals

/- We often want to consider functions defined on intervals.
  In Lean it is more convenient to instead consider only functions defined on all of `ℝ`
  and use junk values outside of the domain.
-/

open Real Set

variable {a b : ℝ}

#check Icc a b  -- closed interval `[a, b]`
#check Ioo a b  -- open interval `(a, b)`
#check Ico a b  -- half-closed interval `[a, b)`
#check Ioi a    -- interval `(a, ∞)`
#check Ici a    -- interval `[a, ∞)`
#check Iio b    -- interval `(-∞, b)`
#check Iic b    -- interval `(-∞, b]`

example (x : ℝ) : x ∈ Ioo a b ↔ a < x ∧ x < b := by rfl

#check NNReal -- The non-negative real numbers `[0, ∞)` as a `subtype`
#check Ici 0 -- `[0, ∞)` as a `Set ℝ`

structure MyNNReal where
  val : ℝ
  nonneg : 0 ≤ val

example : MyNNReal := ⟨5, by positivity⟩

-- Subtypes are the type-analogues of subsets:
-- A subtype bundles a value together with a property
example (x : ℝ) (h : 0 ≤ x) : NNReal where
  val := x
  property := h

-- There is a similar notation as for sets
example : NNReal = {x : ℝ // 0 ≤ x} := by rfl
/- In practice, subtypes can be cumbersome and are best avoided whenever possible -/

#check ENNReal -- Extended non-negative reals `[0, ∞]`
#check EReal -- Extended real numbers `[-∞, ∞]`

-- Derivatives considered only within a subset (such as an interval)
#check derivWithin
#check HasDerivWithinAt
#check DifferentiableWithinAt

end Intervals

section Continuity

open Filter Topology Set

#check ContinuousAt
-- `f` is continuous at `x₀` if `lim_{x → x₀} f x = f x₀`
example (x₀ : ℝ) : ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by rfl

#check ContinuousWithinAt -- Continuity within a subset
#check ContinuousOn -- Continuity (within) at every point in a subset
#check Continuous
#check continuous_iff_continuousAt -- A function is continuous iff it is continuous at every point

-- The square root function is continuous on `[0, ∞)`
example : ContinuousOn sqrt (Ici 0) := by -- `√x`
  -- In Lean, `sqrt x` is defined as `0` for `x ≤ 0`, so it's actually continuous everywhere
  apply continuousOn_of_forall_continuousAt
  exact fun x _ ↦ continuous_iff_continuousAt.mp continuous_sqrt x

example : Continuous (fun y ↦ exp (y ^ 2 * cos y)) := by
  fun_prop -- Tactic that can prove some function properties automatically

/- The intermediate value theorem:
  If a function is continuous on an interval `[a, b]`, then it achieves
  all values between `f a` and `f b`. -/
#check intermediate_value_Icc

theorem exists_eq_zero_of_continuous {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b) (ha : f a ≤ 0) (hb : 0 ≤ f b) : ∃ x ∈ Icc a b, f x = 0 := intermediate_value_Icc hab hf ⟨ha, hb⟩


example : ∃ x ∈ Icc (-1) 1, x - sin x = 0 := by
  apply exists_eq_zero_of_continuous
  · fun_prop
  · norm_num
  all_goals { -- `all_goals` applies the same tactic(s) to all remaining goals
    norm_num
    exact sin_le_one _
  }

end Continuity

end Course.Week7

#min_imports
