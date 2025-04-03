import Course.Common

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

/- We'll only work with integrals of functions on intervals -/
#check intervalIntegral
#check MeasureTheory.integral -- `intervalIntegral` is defined as a special case of the *Bochner integral*

variable {f : ℝ → ℝ}
variable {a b : ℝ}

#check [[a, b]] -- The set `[a, b]` or `[b, a]` depending on ordering of `a`, `b`

-- Type `∫` using `\integral`
#check ∫ x in a..b, f x   -- The integral of `f` on the interval `[a,b]`

#check integral_const

#check integral_id
example (h : ℝ) : (∫ x in (0:ℝ)..h, x) = h ^ 2 / 2 := by
  convert integral_id
  ring

#check integral_pow
example (h : ℝ) : (∫ x in (0:ℝ)..h, x ^ 2) = h ^ 3 / 3 := by
  convert integral_pow _
  · ring
  · norm_num

-- Integrals of special functions
#check integral_sin
example : ∫ x in (0:ℝ)..2 * π, sin x = 0 := by
  rw [integral_sin]
  simp

#check integral_cos
#check integral_exp

-- As usual the interval is defined for all integrands, but it equals the junk value 0 if the integrand is not integrable
#check IntervalIntegrable
#check ContinuousOn.intervalIntegrable
example : IntervalIntegrable (fun x ↦ sin (x * exp (x ^ 2))) length a b := by
  apply ContinuousOn.intervalIntegrable
  fun_prop

#check length
#check integral_add
#check integral_const_mul
example (h : ℝ) : (∫ x in (0:ℝ)..h, 2 * x + x ^ 3) = h ^ 2 + h ^ 4 * (1 / 4) := by
  rw [integral_add, integral_const_mul, integral_pow, integral_id]
  · simp; ring
  · apply ContinuousOn.intervalIntegrable; fun_prop
  · apply ContinuousOn.intervalIntegrable; fun_prop

#check [[a, b]] -- Alternative notation for intervals that also works when `b < a` (then it means `[b, a]`)
-- The fundamental theorem of calculus
#check integral_deriv_eq_sub
example (hdiff : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x) (hint : IntervalIntegrable (deriv f) length a b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  exact integral_deriv_eq_sub hdiff hint

-- The (other part of the) fundamental theorem calculus
#check Continuous.deriv_integral
example (hcont : Continuous f) (x : ℝ): deriv (fun x ↦ ∫ t in (0:ℝ)..x, f t) x = f x := by
  exact Continuous.deriv_integral f hcont 0 x

-- Mathlib has lots of FTC variants
#check integral_eq_sub_of_hasDerivAt
#check integral_hasStrictDerivAt_right
#check integral_hasStrictDerivAt_left

#check integral_mul_deriv_eq_deriv_mul -- Integration by parts

-- Rewriting under binders: `simp_rw`
#check cos_sq
example : ∫ x in (0:ℝ)..π, (cos (x / 2)) ^ 2 = π / 2 := by
  -- rw [cos_sq] -- doesn't work
  simp_rw [cos_sq]
  -- field_simp -- works here
  rw [integral_add, integral_const]
  simp_rw [div_eq_mul_inv]
  simp_rw [show ∀ x : ℝ, 2 * (x * 2⁻¹) = x by field_simp] -- Use `show` to inline an auxiliary hypothesis and its proof
  rw [integral_mul_const, integral_cos]
  simp
  all_goals { apply ContinuousOn.intervalIntegrable; fun_prop }

-- Another way to rewrite under binders is *conversion mode*: `conv` tactic
example : ∫ x in (0:ℝ)..π, (cos (x / 2)) ^ 2 = π / 2 := by
  conv =>
    enter [1, 1, x] -- Traverse to the desired location in the syntax tree
    rw [cos_sq] -- Now we can rewrite / simplify
    ring_nf
  field_simp


-- Can also do this using `congr` / `congr!`
example : ∫ x in (0:ℝ)..π, (cos (x / 2)) ^ 2 = π / 2 := by
  calc
    _ = ∫ x in (0:ℝ)..π, 1 / 2 + cos x * (1 / 2) := by
      -- congr; ext x; rw [cos_sq]; ring_nf
      congr! with x
      rw [cos_sq]; ring_nf
    _ = _ := by field_simp

-- `congr!` can be overambitious:
example : ∫ x in (0:ℝ)..1, x - x = ∫ x in (0:ℝ)..1, 1 - 1 := by
  --congr! -- Will generate subgoals `x = 1`
  congr! 2 -- Only go 2 levels deep into the syntax tree
  simp

open Finset in
theorem sum_integral {F : ℕ → ℝ → ℝ} (hF : ∀ n, Continuous (F n)) (N : ℕ) (a b : ℝ) :
    ∑ n ∈ range N, ∫ x in a..b, F n x = ∫ x in a..b, (∑ n ∈ range N, F n x) := by
  induction' N with N ih
  · simp
  · rw [sum_range_succ, ih, ← integral_add]
    · congr!; rw [sum_range_succ]
    all_goals { apply ContinuousOn.intervalIntegrable; fun_prop }

#check integral_comp_mul_deriv -- Integration by substitution
#check hasDerivAt_mul_const
theorem integral_comp_const_mul (hf : Continuous f) (r : ℝ) (hr : 0 < r) : ∫ x in a..b, f (r * x) = (1 / r) * ∫ x in (r * a)..(r * b), f x := by
  calc
    _ = (1 / r) * ∫ x in a..b, f (r * x) * r := by
      rw [← integral_const_mul]
      congr! 2; field_simp
    _ = _ := by
      congr! 1
      convert integral_comp_mul_deriv _ _ _ using 1
      · intro x hx;
        -- #check hasDerivAt_const_mul -- doesn't  seem to exist, so we need to change order of multiplication
        rw [show HMul.hMul r = fun x ↦ x * r by ext x; exact mul_comm _ _]
        exact hasDerivAt_mul_const _
      · fun_prop
      · exact hf

end Course.Week8
