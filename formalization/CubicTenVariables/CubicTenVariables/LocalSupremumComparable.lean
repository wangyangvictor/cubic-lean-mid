import CubicTenVariables.LocalSupremumNumerics

/-! A fixed lower comparability constant for the phase changes only the
uniform numerical constant in the large-phase local-supremum estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.LocalSupremumComparable
open GradientVolumeNumerics LocalSupremumNumerics

/-- The constant is fixed before all scale and phase parameters. -/
def factor (c : ℝ) : ℝ := (2 : ℝ)^10 * (max 1 c⁻¹)^7

theorem factor_ge_one (c : ℝ) : 1 ≤ factor c := by
  have hk : (1 : ℝ) ≤ (max 1 c⁻¹)^7 := one_le_pow₀ (le_max_left _ _)
  unfold factor
  nlinarith

theorem large_algebra (c P M W Z A L : ℝ) (hc : 0 < c)
    (hP : 0 ≤ P) (hM : 1 ≤ M) (hW : 0 < W) (hZ : 0 ≤ Z)
    (hA : c*W ≤ A) (hL : 0 ≤ L) (hMW : 1 ≤ M*W) :
    P^10*(1+M*W+L)^7*(1+M*Z+L)^3*min 1 ((M*Z/A)^7) ≤
      factor c*(P^10*M^17)*(1+L/W)^7*(1+Z+L)^3*Z^7 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hA0 : 0 < A := (mul_pos hc hW).trans_le hA
  have h₁ := pow_le_pow_left₀ (show 0 ≤ 1+M*W+L by positivity)
    (selected_factor M W L hM hL hMW) 7
  have h₂ := pow_le_pow_left₀ (show 0 ≤ 1+M*Z+L by positivity)
    (complement_factor M Z L hM hL) 3
  have hdiv : M*Z/A ≤ c⁻¹*(M*(Z/W)) := by
    calc
      _ ≤ M*Z/(c*W) := div_le_div_of_nonneg_left
        (mul_nonneg hM0 hZ) (mul_pos hc hW) hA
      _ = _ := by field_simp
  have h₃ : min 1 ((M*Z/A)^7) ≤ (c⁻¹*(M*(Z/W)))^7 :=
    (min_le_right _ _).trans (pow_le_pow_left₀ (by positivity) hdiv 7)
  have hp := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left h₁ (pow_nonneg hP 10)) h₂
      (by positivity) (by positivity)) h₃ (by positivity) (by positivity)
  have hcancel : (W+L)^7*(Z/W)^7=(1+L/W)^7*Z^7 := by
    rw [← mul_pow,← mul_pow]
    congr 1
    field_simp
  calc
    _ ≤ P^10*(2*M*(W+L))^7*(M*(1+Z+L))^3*(c⁻¹*(M*(Z/W)))^7 := hp
    _ = (2:ℝ)^7*(c⁻¹)^7*(P^10*M^17)*((W+L)^7*(Z/W)^7)*(1+Z+L)^3 := by ring
    _ = (2:ℝ)^7*(c⁻¹)^7*(P^10*M^17)*(1+L/W)^7*(1+Z+L)^3*Z^7 := by
      rw [hcancel]
      ring
    _ ≤ _ := by
      unfold factor
      have htwo : (2:ℝ)^7 ≤ (2:ℝ)^10 := by norm_num
      have hcmax : (c⁻¹)^7 ≤ (max 1 c⁻¹)^7 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hc.le) (le_max_right _ _) 7
      gcongr

/-- High phase with an arbitrary fixed positive lower comparison constant. -/
theorem large_bound (c P R φ α η L : ℝ) (hc : 0 < c)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (_hφ : 0 < φ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hcut : 1 ≤ P^η*V P R φ) (hlarge : 1 < φ*P^3)
    (hα : c*(R*φ) ≤ |α|) :
    rawBound P R φ α η L ≤
      factor c*P^((10 : ℝ)+17*η)*(1+L/V P R φ)^7*
        (1+Vzero P R φ+L)^3*(Vzero P R φ)^7 := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hA : c*V P R φ ≤ |α| * P^2 := by
    rw [V_large P R φ hP0 hlarge,← mul_assoc]
    exact mul_le_mul_of_nonneg_right hα (sq_nonneg P)
  have h := large_algebra c P (P^η) (V P R φ) (Vzero P R φ) (|α| * P^2) L
    hc hP0.le (Real.one_le_rpow hP hη) (V_pos P R φ hP0 hR0)
    (Vzero_pos P R φ hP0 hR0).le hA hL hcut
  rw [physical_power P η hP0] at h
  exact h

/-- The low-phase bound does not require a phase comparison. -/
theorem small_bound (P R φ α η L : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hφ : 0 < φ) (hη : 0 ≤ η) (hL : 0 ≤ L) (hcut : 1 ≤ P^η*V P R φ)
    (hsmall : φ*P^3 ≤ 1) :
    rawBound P R φ α η L ≤
      (2:ℝ)^10*P^((10 : ℝ)+17*η)*(V P R φ+L)^10 :=
  LocalSupremumNumerics.small_bound P R φ α η L hP hR hφ hη hL hcut hsmall

theorem large_epsilon_bound (c ε P R φ α L : ℝ) (hc : 0 < c) (hε : 0 < ε)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 < φ) (hL : 0 ≤ L)
    (hcut : 1 ≤ P^(ε/17)*V P R φ) (hlarge : 1 < φ*P^3)
    (hα : c*(R*φ) ≤ |α|) :
    rawBound P R φ α (ε/17) L ≤
      factor c*P^((10 : ℝ)+ε)*(1+L/V P R φ)^7*
        (1+Vzero P R φ+L)^3*(Vzero P R φ)^7 := by
  have h := large_bound c P R φ α (ε/17) L hc hP hR hφ (by positivity)
    hL hcut hlarge hα
  have he : (10 : ℝ)+17*(ε/17)=10+ε := by ring
  rwa [he] at h

theorem small_epsilon_bound (ε P R φ α L : ℝ) (hε : 0 < ε)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 < φ) (hL : 0 ≤ L)
    (hcut : 1 ≤ P^(ε/17)*V P R φ) (hsmall : φ*P^3 ≤ 1) :
    rawBound P R φ α (ε/17) L ≤
      (2:ℝ)^10*P^((10 : ℝ)+ε)*(V P R φ+L)^10 :=
  LocalSupremumNumerics.small_epsilon_bound ε P R φ α L hε hP hR hφ hL hcut hsmall

end CubicTenVariables.LocalSupremumComparable
