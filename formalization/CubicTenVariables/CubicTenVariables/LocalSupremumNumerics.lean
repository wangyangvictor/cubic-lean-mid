import CubicTenVariables.GradientVolumeNumerics

/-! Numerical assembly of the local-supremum volume estimate. The frequency
and gradient width exponent eta is distinct from the final epsilon loss.
The high-phase branch pays 7+3+7 copies of eta; the low-phase branch pays
only 10, which is bounded by the same displayed loss of 17 eta. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.LocalSupremumNumerics
open GradientVolumeNumerics

def V (P R φ : ℝ) : ℝ := (R/P)*max 1 (φ*P^3)

def rawBound (P R φ α η L : ℝ) : ℝ :=
  P^10*(1+P^η*V P R φ+L)^7*(1+P^η*Vzero P R φ+L)^3*
    min 1 ((P^η*Vzero P R φ/(|α| * P^2))^7)

theorem V_pos (P R φ : ℝ) (hP : 0 < P) (hR : 0 < R) : 0 < V P R φ := by
  unfold V
  positivity

theorem V_large (P R φ : ℝ) (hP : 0 < P) (hφ : 1 < φ*P^3) :
    V P R φ=R*φ*P^2 := by
  rw [V,max_eq_right hφ.le]
  field_simp

theorem V_small (P R φ : ℝ) (hφ : φ*P^3 ≤ 1) : V P R φ=R/P := by
  simp only [V,max_eq_left hφ,mul_one]

theorem Vzero_small (P R φ : ℝ) (hφ : φ*P^3 ≤ 1) : Vzero P R φ=R/P := by
  have hs : Real.sqrt (φ*P^3) ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hφ
  simp only [Vzero,max_eq_left hs,mul_one]

theorem selected_factor (M W L : ℝ) (hM : 1 ≤ M) (hL : 0 ≤ L) (hMW : 1 ≤ M*W) :
    1+M*W+L ≤ 2*M*(W+L) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) hL]

theorem complement_factor (M W L : ℝ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    1+M*W+L ≤ M*(1+W+L) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) hL]

/-- Algebraic high-phase estimate, before substituting the physical scales. -/
theorem large_algebra (P M W Z A L : ℝ) (hP : 0 ≤ P) (hM : 1 ≤ M)
    (hW : 0 < W) (hZ : 0 ≤ Z) (hA : W ≤ A) (hL : 0 ≤ L) (hMW : 1 ≤ M*W) :
    P^10*(1+M*W+L)^7*(1+M*Z+L)^3*min 1 ((M*Z/A)^7) ≤
      (2:ℝ)^10*(P^10*M^17)*(1+L/W)^7*(1+Z+L)^3*Z^7 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hA0 : 0 < A := hW.trans_le hA
  have h₁ := pow_le_pow_left₀ (show 0 ≤ 1+M*W+L by positivity)
    (selected_factor M W L hM hL hMW) 7
  have h₂ := pow_le_pow_left₀ (show 0 ≤ 1+M*Z+L by positivity)
    (complement_factor M Z L hM hL) 3
  have hdiv : M*Z/A ≤ M*(Z/W) := by
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_left (mul_nonneg hM0 hZ) hW hA
  have h₃ : min 1 ((M*Z/A)^7) ≤ (M*(Z/W))^7 :=
    (min_le_right _ _).trans (pow_le_pow_left₀ (by positivity) hdiv 7)
  have hp := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left h₁ (pow_nonneg hP 10)) h₂
      (by positivity) (by positivity)) h₃ (by positivity) (by positivity)
  have hcancel : (W+L)^7*(Z/W)^7=(1+L/W)^7*Z^7 := by
    rw [← mul_pow,← mul_pow]
    congr 1
    field_simp
  calc
    _ ≤ P^10*(2*M*(W+L))^7*(M*(1+Z+L))^3*(M*(Z/W))^7 := hp
    _ = (2:ℝ)^7*(P^10*M^17)*((W+L)^7*(Z/W)^7)*(1+Z+L)^3 := by ring
    _ = (2:ℝ)^7*(P^10*M^17)*(1+L/W)^7*(1+Z+L)^3*Z^7 := by rw [hcancel]; ring
    _ ≤ _ := by
      have hc : (2:ℝ)^7 ≤ (2:ℝ)^10 := by norm_num
      gcongr

/-- The small-phase branch needs only ten factors of M. -/
theorem small_algebra (P M W A L : ℝ) (hP : 0 ≤ P) (hM : 1 ≤ M)
    (hW : 0 < W) (hL : 0 ≤ L) (hMW : 1 ≤ M*W) :
    P^10*(1+M*W+L)^7*(1+M*W+L)^3*min 1 ((M*W/A)^7) ≤
      (2:ℝ)^10*(P^10*M^17)*(W+L)^10 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hp : (1+M*W+L)^10 ≤ (2*M*(W+L))^10 :=
    pow_le_pow_left₀ (by positivity) (selected_factor M W L hM hL hMW) 10
  have hMpow : M^10 ≤ M^17 := pow_le_pow_right₀ hM (by decide)
  calc
    _ ≤ P^10*(1+M*W+L)^7*(1+M*W+L)^3 :=
      mul_le_of_le_one_right (by positivity) (min_le_left _ _)
    _ = P^10*(1+M*W+L)^10 := by ring
    _ ≤ P^10*(2*M*(W+L))^10 := mul_le_mul_of_nonneg_left hp (pow_nonneg hP 10)
    _ = (2:ℝ)^10*(P^10*M^10)*(W+L)^10 := by ring
    _ ≤ _ := by gcongr

/-- Exact conversion of the natural-power bookkeeping to the real power. -/
theorem physical_power (P η : ℝ) (hP : 0 < P) :
    P^10*(P^η)^17=P^((10 : ℝ)+17*η) := by
  rw [← Real.rpow_natCast P 10,← Real.rpow_natCast (P^η) 17,
    ← Real.rpow_mul hP.le,← Real.rpow_add hP]
  congr 1
  norm_num
  ring

/-- High phase, with the width loss explicitly equal to 17 eta. -/
theorem large_bound (P R φ α η L : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (_hφ : 0 < φ) (hη : 0 ≤ η) (hL : 0 ≤ L) (hcut : 1 ≤ P^η*V P R φ)
    (hlarge : 1 < φ*P^3) (hα : R*φ ≤ |α|) :
    rawBound P R φ α η L ≤
      (2:ℝ)^10*P^((10 : ℝ)+17*η)*(1+L/V P R φ)^7*
        (1+Vzero P R φ+L)^3*(Vzero P R φ)^7 := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hM : 1 ≤ P^η := Real.one_le_rpow hP hη
  have hW : 0 < V P R φ := V_pos P R φ hP0 hR0
  have hZ : 0 ≤ Vzero P R φ := (Vzero_pos P R φ hP0 hR0).le
  have hA : V P R φ ≤ |α| * P^2 := by
    rw [V_large P R φ hP0 hlarge]
    exact mul_le_mul_of_nonneg_right hα (sq_nonneg P)
  have h := large_algebra P (P^η) (V P R φ) (Vzero P R φ) (|α| * P^2) L
    hP0.le hM hW hZ hA hL hcut
  rw [physical_power P η hP0] at h
  exact h

/-- Small phase, uniformly bounded by the same safe 17 eta loss. -/
theorem small_bound (P R φ α η L : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (_hφ : 0 < φ) (hη : 0 ≤ η) (hL : 0 ≤ L) (hcut : 1 ≤ P^η*V P R φ)
    (hsmall : φ*P^3 ≤ 1) :
    rawBound P R φ α η L ≤
      (2:ℝ)^10*P^((10 : ℝ)+17*η)*(V P R φ+L)^10 := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have he : Vzero P R φ=V P R φ := by rw [Vzero_small P R φ hsmall,V_small P R φ hsmall]
  have h := small_algebra P (P^η) (V P R φ) (|α| * P^2) L hP0.le
    (Real.one_le_rpow hP hη) (V_pos P R φ hP0 hR0) hL hcut
  rw [physical_power P η hP0] at h
  simpa only [rawBound,he] using h

/-- Final epsilon is obtained by choosing the window width exponent epsilon/17. -/
theorem large_epsilon_bound (ε P R φ α L : ℝ) (hε : 0 < ε)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 < φ) (hL : 0 ≤ L)
    (hcut : 1 ≤ P^(ε/17)*V P R φ) (hlarge : 1 < φ*P^3) (hα : R*φ ≤ |α|) :
    rawBound P R φ α (ε/17) L ≤
      (2:ℝ)^10*P^((10 : ℝ)+ε)*(1+L/V P R φ)^7*
        (1+Vzero P R φ+L)^3*(Vzero P R φ)^7 := by
  have h := large_bound P R φ α (ε/17) L hP hR hφ (by positivity) hL hcut hlarge hα
  have he : (10 : ℝ)+17*(ε/17)=10+ε := by ring
  rwa [he] at h

theorem small_epsilon_bound (ε P R φ α L : ℝ) (hε : 0 < ε)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 < φ) (hL : 0 ≤ L)
    (hcut : 1 ≤ P^(ε/17)*V P R φ) (hsmall : φ*P^3 ≤ 1) :
    rawBound P R φ α (ε/17) L ≤
      (2:ℝ)^10*P^((10 : ℝ)+ε)*(V P R φ+L)^10 := by
  have h := small_bound P R φ α (ε/17) L hP hR hφ (by positivity) hL hcut hsmall
  have he : (10 : ℝ)+17*(ε/17)=10+ε := by ring
  rwa [he] at h

end CubicTenVariables.LocalSupremumNumerics
