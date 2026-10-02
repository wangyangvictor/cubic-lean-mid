import CubicTenVariables.AveragedGradientVolume
import CubicTenVariables.LocalSupremumComparable

/-! The required n=10 local-supremum volume estimate for the actual chosen
counting weight. The source uses one epsilon for two roles; here the width
exponent epsilon/17 and final exponent epsilon are stated separately. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalSupremumVolumeEstimate
open MvPolynomial MeasureTheory HessianTheorem11 RealRegularGradientChart
open AveragedGradientVolume LocalSupremumNumerics GradientVolumeNumerics

/-- One constant works for all epsilon, physical parameters, real window
radii and subsets of the fixed chart box. Only a fixed lower comparison for
|alpha| is needed. The empty frequency regime has bound exactly zero. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Set (Fin 10 → ℝ)), K ⊆ D.box →
      ∀ (ε P R φ α L : ℝ), 0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ → 0 ≤ L →
      c*(R*φ) ≤ |α| →
      volumeSum F K P α (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L ≤
        if P^(ε/17)*V P R φ < 1 then 0
        else C*P^((10 : ℝ)+ε)*
          (if 1 < φ*P^3 then (1+L/V P R φ)^7*(1+Vzero P R φ+L)^3*(Vzero P R φ)^7
           else (V P R φ+L)^10) := by
  obtain ⟨A,hA,hraw⟩ := AveragedGradientVolume.exists_scaled_bound F hF D
  have hf := LocalSupremumComparable.factor_ge_one c
  have htwo : (2:ℝ)^10 ≤ LocalSupremumComparable.factor c := by
    have hh := one_le_pow₀ (le_max_left (1:ℝ) c⁻¹) (n := 7)
    unfold LocalSupremumComparable.factor
    nlinarith
  refine ⟨A*LocalSupremumComparable.factor c,by nlinarith,?_⟩
  intro K hK ε P R φ α L hε hP hR hφ hL hα
  by_cases hcut : P^(ε/17)*V P R φ < 1
  · rw [if_pos hcut,volumeSum_eq_zero_of_lt_one F K P α _ _ L hcut]
  rw [if_neg hcut]
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hα0 : α ≠ 0 := abs_pos.mp ((mul_pos hc (mul_pos hR0 hφ)).trans_le hα)
  have hb := hraw K hK P R φ α (ε/17) L hP0 hR0 hα0 hL
  by_cases hlarge : 1 < φ*P^3
  · rw [if_pos hlarge]
    have hn := LocalSupremumComparable.large_epsilon_bound c ε P R φ α L
      hc hε hP hR hφ hL (le_of_not_gt hcut) hlarge hα
    calc
      _ ≤ A*rawBound P R φ α (ε/17) L := hb
      _ ≤ A*(LocalSupremumComparable.factor c*P^((10 : ℝ)+ε)*(1+L/V P R φ)^7*
          (1+Vzero P R φ+L)^3*(Vzero P R φ)^7) :=
        mul_le_mul_of_nonneg_left hn (zero_le_one.trans hA)
      _ = _ := by ring
  · rw [if_neg hlarge]
    have hn := LocalSupremumNumerics.small_epsilon_bound ε P R φ α L
      hε hP hR hφ hL (le_of_not_gt hcut) (le_of_not_gt hlarge)
    have hv := V_pos P R φ hP0 hR0
    calc
      _ ≤ A*rawBound P R φ α (ε/17) L := hb
      _ ≤ A*((2:ℝ)^10*P^((10 : ℝ)+ε)*(V P R φ+L)^10) :=
        mul_le_mul_of_nonneg_left hn (zero_le_one.trans hA)
      _ ≤ A*(LocalSupremumComparable.factor c*P^((10 : ℝ)+ε)*(V P R φ+L)^10) := by
        gcongr
      _ = _ := by ring

/-- The estimate on the actual support of the smooth counting weight. -/
theorem exists_support_bound (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε P R φ α L : ℝ),
      0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ → 0 ≤ L → c*(R*φ) ≤ |α| →
      volumeSum F (tsupport D.weight.weight) P α
        (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L ≤
        if P^(ε/17)*V P R φ < 1 then 0
        else C*P^((10 : ℝ)+ε)*
          (if 1 < φ*P^3 then (1+L/V P R φ)^7*(1+Vzero P R φ+L)^3*(Vzero P R φ)^7
           else (V P R φ+L)^10) := by
  obtain ⟨C,hC,hbound⟩ := exists_bound F hF D c hc
  exact ⟨C,hC,hbound (tsupport D.weight.weight) D.support_subset_box⟩

/-- The real regular chart and genuine counting weight are constructed from
rational anisotropy before the comparison constant and every analytic scale.
There is no supplied rank point, chart, volume estimate or literature input. -/
theorem exists_data_and_bound (G : AnisotropicCubic 10) :
    ∃ D : Data (map (algebraMap ℚ ℝ) G.polynomial),
      ∀ c : ℝ, 0 < c → ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε P R φ α L : ℝ),
      0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ → 0 ≤ L → c*(R*φ) ≤ |α| →
      volumeSum (map (algebraMap ℚ ℝ) G.polynomial) (tsupport D.weight.weight) P α
        (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L ≤
        if P^(ε/17)*V P R φ < 1 then 0
        else C*P^((10 : ℝ)+ε)*
          (if 1 < φ*P^3 then (1+L/V P R φ)^7*(1+Vzero P R φ+L)^3*(Vzero P R φ)^7
           else (V P R φ+L)^10) := by
  obtain ⟨D⟩ := RealRegularGradientChart.exists_data G
  exact ⟨D,fun c hc => exists_support_bound _ (G.homogeneous.map _) D c hc⟩

end CubicTenVariables.LocalSupremumVolumeEstimate
