import Course.Common

/-

Homework sheet 9
Due Apr 24 10am

-/

namespace HW9

open Real intervalIntegral Set Filter Topology

variable {f : ℝ → ℝ} {f' : ℝ → ℝ}

/-
  This week's task is a little different:
  your goal is to complete the proof of the Riemann-Lebesgue lemma that we started in class.
-/
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
      _ ≤ R⁻¹ * (|cos (R * b) * f b - cos (R * a) * f a| + |∫ (x : ℝ) in a..b, cos (R * x) * f' x|) := by
        -- sorry
        rw [abs_mul, abs_neg, abs_mul, abs_of_pos (show 0 < R⁻¹ by positivity), mul_add]
      _ ≤ R⁻¹ * (|cos (R * b)| * |f b| + |cos (R * a)| * |f a| + |∫ (x : ℝ) in a..b, cos (R * x) * f' x|) := by
        -- sorry
        gcongr; convert abs_add_le _ _ using 1
        · rw [abs_mul, abs_neg, abs_mul]
        · infer_instance
      _ ≤ R⁻¹ * (1 * |f b| + 1 * |f a| + ∫ x in a..b, |cos (R * x) * f' x|) := by
        -- sorry
        gcongr
        · exact abs_cos_le_one _
        · exact abs_cos_le_one _
        · exact abs_integral_le_integral_abs hab
      _ ≤ R⁻¹ * (|f b| + |f a| + ∫ x in a..b, |f' x|) := by
        rw [one_mul, one_mul]; gcongr
        apply integral_mono hab
        · apply ContinuousOn.intervalIntegrable; fun_prop -- sorry
        · apply ContinuousOn.intervalIntegrable; fun_prop -- sorry
        · intro x
          dsimp
          rw [abs_mul]
          nth_rewrite 2 [← one_mul |f' _|]
          gcongr
          exact abs_cos_le_one _
      _ = _ := by rw [mul_comm]

  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := exists_forall_abs_integral_sin_mul_le
  have C_nonneg : 0 ≤ C := by
    calc
      0 ≤ |∫ (x : ℝ) in a..b, sin (1 * x) * f x| := abs_nonneg _ -- sorry
      _ ≤ C * 1⁻¹ := hC 1 (by positivity) -- sorry
      _ = _ := by simp
  by_cases C_zero : C = 0
  · -- If `C = 0` the claim follows because `0 < ε`
    use 1
    -- sorry
    intro R hR
    simp only [dist_zero_right, norm_eq_abs]
    calc
      _ ≤ C * R⁻¹ := hC _ (by positivity)
      _ < _ := by rw [C_zero, zero_mul]; exact hε
  · use 2 * C * ε⁻¹
    intro R hR
    simp only [dist_zero_right, norm_eq_abs]
    have R_pos : 0 < R := by
      calc
        _ < 2 * C * ε⁻¹ := by positivity
        _ ≤ R := hR
    calc
      _ ≤ C * R⁻¹ := hC _ R_pos
      _ ≤ C * (2 * C * ε⁻¹)⁻¹ := by gcongr -- sorry
      _ = ε / 2 := by field_simp; ring
      _ < ε := by linarith only [hε]


end HW9
