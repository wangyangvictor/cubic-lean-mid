import CubicTenVariables.ConductorFixedFrequency

/-! The elementary positive-moment threshold inequality and the actual
frequency-height estimate inside a translated coordinate box. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorPositiveMeanNumerics
open ConductorFixedFrequency

theorem le_scaled_moment (K K0 : ℝ) (hK0 : 0 < K0) (hK : K0 ≤ K) :
    K ≤ K0^(-(1 : ℝ)/2)*K^((3 : ℝ)/2) := by
  have hKpos : 0 < K := hK0.trans_le hK
  have hb : K^(-(1 : ℝ)/2) ≤ K0^(-(1 : ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos hK0 hK (by norm_num)
  calc
    K = K^(-(1 : ℝ)/2)*K^((3 : ℝ)/2) := by
      rw [← Real.rpow_add hKpos]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hKpos.le _)

theorem height_le (u : Fin 10 → ℝ) (L : ℝ) (hL : 0 ≤ L) (m : ℕ)
    (v : Fin 10 → ℤ) (hv : ∀ i, |(v i : ℝ)-u i| ≤ L) :
    frequencyHeight v ≤ 2+‖u‖+L+(m : ℝ) := by
  have hdiff : ‖(fun i => (v i : ℝ))-u‖ ≤ L := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro i
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hv i
  have he : (fun i => (v i : ℝ)) = ((fun i => (v i : ℝ))-u)+u := by
    ext i
    simp
  have hnorm : ‖fun i => (v i : ℝ)‖ ≤ ‖u‖+L := by
    calc
      _ = ‖((fun i => (v i : ℝ))-u)+u‖ := congrArg norm he
      _ ≤ ‖(fun i => (v i : ℝ))-u‖+‖u‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  dsimp only [frequencyHeight]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

end CubicTenVariables.ConductorPositiveMeanNumerics
