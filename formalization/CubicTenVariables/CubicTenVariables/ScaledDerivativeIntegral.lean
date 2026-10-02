import CubicTenVariables.DeltaKernelTruncation

/-! Integrating the near-origin and exterior derivative bounds needed for the
smooth delta amplitude. The two pointwise bounds remain explicit hypotheses. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScaledDerivativeIntegral
open MeasureTheory Set

/-- A peak of width `a` and height `a^(-j-1)`, with the exterior power tail
arising from second-order Poisson summation, has scaled integral at most `4B`. -/
theorem scaled_integral_le (f : ℝ → ℂ) (hf : Integrable f)
    (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) (j : ℕ)
    (hnear : ∀ y : ℝ, |y| ≤ a → ‖f y‖ ≤ B/a^(j+1))
    (hfar : ∀ y : ℝ, a ≤ |y| → ‖f y‖ ≤ B*a*|y|^(-((j+2 : ℕ) : ℝ))) :
    a^j * (∫ y : ℝ, ‖f y‖) ≤ 4*B := by
  let F : ℝ → ℂ := fun y => (‖f y‖ : ℂ)
  have hi : Integrable F := hf.norm.ofReal
  have hnorm (y : ℝ) : ‖F y‖ = ‖f y‖ := by
    simp only [F,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have htail := DeltaKernelTruncation.norm_integral_sub_Ioo_le F hi (B*a) a ha
    (j+1) (by omega) (by
      intro y hy
      simpa only [hnorm,Nat.add_assoc,show (1+1 : ℕ)=2 from rfl] using hfar y hy)
  have hpeak : ‖∫ y in Ioo (-a) a, F y‖ ≤ B/a^(j+1)*(2*a) := by
    have hb := norm_setIntegral_le_of_norm_le_const (f := F)
      (s := Ioo (-a) a) (μ := volume)
      (measure_Ioo_lt_top : volume (Ioo (-a) a) < ⊤) (C := B/a^(j+1)) (by
        intro y hy
        rw [hnorm]
        apply hnear y
        exact (abs_lt.mpr hy).le)
    simpa only [Real.volume_real_Ioo_of_le (by linarith : -a ≤ a),sub_neg_eq_add,
      ← two_mul] using hb
  have htotal : (∫ y : ℝ, ‖f y‖) = ‖∫ y, F y‖ := by
    have he : (∫ y, F y) = Complex.ofReal (∫ y : ℝ, ‖f y‖) := integral_complex_ofReal
    have hpos : 0 ≤ ∫ y : ℝ, ‖f y‖ := integral_nonneg (fun y => norm_nonneg (f y))
    rw [he]
    simp only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hpos]
  have hsum : (∫ y : ℝ, ‖f y‖) ≤
      (2*(B*a)/(j+1 : ℕ))*a^(-((j+1 : ℕ) : ℝ)) + B/a^(j+1)*(2*a) := by
    rw [htotal]
    calc
      _ ≤ ‖(∫ y, F y)-(∫ y in Ioo (-a) a, F y)‖ +
          ‖∫ y in Ioo (-a) a, F y‖ := by
            simpa only [add_comm] using norm_le_insert'
              (∫ y, F y) (∫ y in Ioo (-a) a, F y)
      _ ≤ _ := add_le_add htail hpeak
  have hscaled := mul_le_mul_of_nonneg_left hsum (pow_nonneg ha.le j)
  have he : a^j * ((2*(B*a)/(j+1 : ℕ))*a^(-((j+1 : ℕ) : ℝ)) +
      B/a^(j+1)*(2*a)) = 2*B/(j+1 : ℕ)+2*B := by
    rw [Real.rpow_neg ha.le,Real.rpow_natCast,pow_succ]
    field_simp
  rw [he] at hscaled
  have hden : (1 : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (show 1 ≤ j+1 by omega)
  have hb : 2*B/(j+1 : ℕ) ≤ 2*B :=
    div_le_self (by positivity) hden
  linarith

end CubicTenVariables.ScaledDerivativeIntegral
