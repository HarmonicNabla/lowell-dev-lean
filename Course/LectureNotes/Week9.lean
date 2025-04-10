import Course.Common

/-
Today: Formalization practice

-/

namespace Course.Week9

/- Let us practice putting together what we have learned by formalizing a mathematically interesting theorem:

*Riemann-Lebesgue lemma*
Let `f : [a, b] → ℝ` be continuously differentiable.
Then `∫ x in a..b, sin (R * x) * f x` converges to `0` as `R → ∞`.
(Actually this holds with much weaker assumptions on `f`.)

 -/

open Real intervalIntegral Set Filter Topology

#check integral_mul_deriv_eq_deriv_mul

#check Metric.tendsto_atTop

#check abs_integral_le_integral_abs
#check integral_mono_on

#check abs_add_le

variable {f : ℝ → ℝ} {f' : ℝ → ℝ}

theorem riemannLebesgue {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (uIcc a b)) :
    Tendsto (fun R ↦ ∫ x in a..b, sin (R * x) * f x) atTop (𝓝 0) := by

  have deriv_cos_mul {R : ℝ} : deriv (fun x ↦ cos (R * x)) = fun x ↦ -R * sin (R * x) := by
    ext
    apply HasDerivAt.deriv
    convert HasDerivAt.cos (HasDerivAt.const_mul R (hasDerivAt_id _)) using 1
    rw [id]; ring

  have sin_mul_eq_deriv {R x : ℝ} (hR : 0 < R) : sin (R * x) = -R⁻¹ * deriv (fun x ↦ cos (R * x)) x := by
    rw [deriv_cos_mul]; field_simp

  have eq1 {R : ℝ} (hR : 0 < R) : ∫ x in a..b, sin (R * x) * f x =
      -R⁻¹ * (cos (R * b) * f b - cos (R * a) * f a) + R⁻¹ * ∫ x in a..b, cos (R * x) * f' x := by
    calc
      _ = -R⁻¹ * ∫ x in a..b, (deriv (fun x ↦ cos (R * x)) x) * f x := by
        simp_rw [sin_mul_eq_deriv hR, mul_assoc]; rw [integral_const_mul]
      _ = _ := by
        simp_rw [mul_comm _ (f _)]
        rw [integral_mul_deriv_eq_deriv_mul (u := f) (v := fun x ↦ cos (R * x)) (u' := f')]
        · simp_rw [mul_comm (f' _) _]; ring
        · exact hf
        · simp; fun_prop
        · apply ContinuousOn.intervalIntegrable; exact hf'
        · apply ContinuousOn.intervalIntegrable; rw [deriv_cos_mul]; fun_prop

  have exists_forall_abs_integral_sin_mul_le : ∃ C, ∀ R > 0, |∫ x in a..b, sin (R * x) * f x| ≤ C * R⁻¹ := by
    let C := |f b| + |f a| + ∫ x in a..b, |f' x|
    use C
    intro R hR
    rw [eq1 hR]
    calc
      _ ≤ |-R⁻¹ * (cos (R * b) * f b - cos (R * a) * f a)| + |R⁻¹ * ∫ (x : ℝ) in a..b, cos (R * x) * f' x| := abs_add_le _ _
      _ ≤ R⁻¹ * (|f b| + |f a|) + R⁻¹ * ∫ x in a..b, |f' x| := by
        gcongr
        · sorry
        · rw [abs_mul, abs_of_pos (show 0 < R⁻¹ by positivity)]
          gcongr
          calc
            _ ≤ ∫ x in a..b, |cos (R * x) * f' x| := abs_integral_le_integral_abs hab
            _ ≤ _ := by
              apply integral_mono hab
              · sorry
              · sorry
              · intro x
                dsimp
                rw [abs_mul]
                nth_rewrite 2 [← one_mul |f' _|]
                gcongr
                exact abs_cos_le_one _
      _ = _ := by ring

  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := exists_forall_abs_integral_sin_mul_le
  by_cases C_pos : 0 < C
  · use 2 * C * ε⁻¹
    intro R hR
    simp
    have R_pos : 0 < R := by
      calc
        _ < 2 * C * ε⁻¹ := by positivity
        _ ≤ R := hR
    calc
      _ ≤ C * R⁻¹ := hC _ R_pos
      _ ≤ C * (2 * C * ε⁻¹)⁻¹ := by sorry
      _ = ε / 2 := by field_simp; ring
      _ < ε := by linarith only [hε]
  · -- Here `C ≤ 0`, so we must have `C = 0`
    have : C = 0 := by sorry -- Follows by contradiction because `abs` is nonnegative
    -- Then we win because `0 < ε`
    sorry


end Course.Week9
