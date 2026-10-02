import CubicTenVariables.GradientWindowScaling
import CubicTenVariables.GradientVolumeNumerics
import CubicTenVariables.RealRegularGradientChart

/-! The actual ten-variable gradient-window volume estimate on the fixed
regular chart selected from rational anisotropy. Window width and final
epsilon loss are distinct parameters. No literature premise occurs. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientPhysicalWindow
open MvPolynomial MeasureTheory HessianTheorem11 GradientChartVolume GradientWindowScaling
open GradientVolumeNumerics RealRegularGradientChart
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℝ}

theorem window_measure_ne_top (D : Data F) (hF : F.IsHomogeneous 3)
    (P α : ℝ) (hP : 0 < P) (hα : α ≠ 0) (v : Fin 10 → ℝ) (Δ : ℝ) :
    volume (window F D.box P α v Δ) ≠ ⊤ := by
  rw [volume_window F hF D.box P α hP hα]
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top D.box_compact.measure_lt_top.ne
    (measure_mono (fun _ hx => hx.1))

/-- The scale and center are quantified after one chart-dependent constant. -/
theorem exists_physical_bound (D : Data F) (hF : F.IsHomogeneous 3) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ P : ℝ, 0 < P → ∀ α : ℝ, α ≠ 0 →
      ∀ (v : Fin 10 → ℝ) (Δ : ℝ), 0 ≤ Δ →
      (volume (window F D.box P α v Δ)).toReal ≤
        A*P^10*min 1 ((Δ/(|α| * P^2))^7) := by
  obtain ⟨B,hB,hbox⟩ := D.exists_box_bound
  obtain ⟨A,hA,hbound⟩ := GradientChartVolume.exists_real_bound F D.rows D.cols
    D.cols_injective D.domain D.box D.antiConstant D.antilipschitz D.box_subset_domain B hB hbox
  refine ⟨A,hA,?_⟩
  intro P hP α hα v Δ hΔ
  rw [volume_window_real F hF D.box P α hP hα]
  have h := mul_le_mul_of_nonneg_left
    (hbound ((α*P^2)⁻¹ • v) (Δ/(|α| * P^2)) (by positivity)) (pow_nonneg hP.le 10)
  convert h using 1; ring

/-- Literal dyadic-gradient window, before choosing a loss parameter. A width
P^η produces the displayed P^(10+7η), with no hidden identification of epsilons. -/
theorem exists_dyadic_bound (D : Data F) (hF : F.IsHomogeneous 3) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (P R φ q θ η : ℝ), 1 ≤ P → 1 ≤ R → 0 < φ →
      R ≤ q → φ ≤ |θ| → 0 ≤ η → ∀ v : Fin 10 → ℝ,
      (volume (window F D.box P (q*θ) v (P^η*Vzero P R φ))).toReal ≤
        A*P^((10 : ℝ)+7*η)*(R/(P*Vzero P R φ))^7 := by
  obtain ⟨A,hA,hbound⟩ := exists_physical_bound D hF
  refine ⟨A,hA,?_⟩
  intro P R φ q θ η hP hR hφ hq hθ hη v
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hq0 : 0 < q := hR0.trans_le hq
  have hθ0 : θ ≠ 0 := abs_pos.mp (hφ.trans_le hθ)
  have hΔ : 0 ≤ P^η*Vzero P R φ := by
    exact mul_nonneg (Real.rpow_nonneg hP0.le _) (Vzero_pos P R φ hP0 hR0).le
  have h := hbound P hP0 (q*θ) (mul_ne_zero hq0.ne' hθ0) v _ hΔ
  rw [abs_mul,abs_of_pos hq0] at h
  have hn := physical_factor P R φ q θ η hP hR0 hφ hq hθ hη 10 7
  norm_num only [Nat.cast_ofNat] at hn
  calc
    _ ≤ A*P^10*min 1 ((P^η*Vzero P R φ/(q*|θ| * P^2))^7) := h
    _ = A*(P^10*min 1 ((P^η*Vzero P R φ/(q*|θ| * P^2))^7)) := by ring
    _ ≤ A*(P^((10 : ℝ)+7*η)*(R/(P*Vzero P R φ))^7) :=
      mul_le_mul_of_nonneg_left hn (zero_le_one.trans hA)
    _ = _ := by ring

/-- The needed epsilon-loss estimate uses width P^(epsilon/7). -/
theorem exists_epsilon_bound (D : Data F) (hF : F.IsHomogeneous 3) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (ε P R φ q θ : ℝ), 0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ →
      R ≤ q → φ ≤ |θ| → ∀ v : Fin 10 → ℝ,
      (volume (window F D.box P (q*θ) v (P^(ε/7)*Vzero P R φ))).toReal ≤
        A*P^((10 : ℝ)+ε)*(R/(P*Vzero P R φ))^7 := by
  obtain ⟨A,hA,hbound⟩ := exists_dyadic_bound D hF
  refine ⟨A,hA,?_⟩
  intro ε P R φ q θ hε hP hR hφ hq hθ v
  have h := hbound P R φ q θ (ε/7) hP hR hφ hq hθ (by positivity) v
  have he : (10 : ℝ)+7*(ε/7)=10+ε := by ring
  rwa [he] at h

/-- Rational anisotropy supplies the actual point, chart and weight as well
as the uniform volume estimate. No regular chart or fiber bound is supplied. -/
theorem exists_data_and_bound (G : AnisotropicCubic 10) :
    ∃ (D : Data (map (algebraMap ℚ ℝ) G.polynomial)) (A : ℝ),
      1 ≤ A ∧ ∀ (ε P R φ q θ : ℝ), 0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ →
        R ≤ q → φ ≤ |θ| → ∀ v : Fin 10 → ℝ,
        (volume (window (map (algebraMap ℚ ℝ) G.polynomial) D.box P (q*θ) v
          (P^(ε/7)*Vzero P R φ))).toReal ≤
          A*P^((10 : ℝ)+ε)*(R/(P*Vzero P R φ))^7 := by
  obtain ⟨D⟩ := RealRegularGradientChart.exists_data G
  obtain ⟨A,hA,hbound⟩ := exists_epsilon_bound D (G.homogeneous.map _)
  exact ⟨D,A,hA,hbound⟩

end CubicTenVariables.GradientPhysicalWindow
