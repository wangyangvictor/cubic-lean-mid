import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Numerical rescaling of a rank-r gradient-volume estimate. The exponent
of the window width is kept distinct from the final epsilon loss. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientVolumeNumerics

def Vzero (P R φ : ℝ) : ℝ := (R/P)*max 1 (Real.sqrt (φ*P^3))

theorem Vzero_pos (P R φ : ℝ) (hP : 0 < P) (hR : 0 < R) : 0 < Vzero P R φ := by
  unfold Vzero
  positivity

theorem minimum_ratio (P R φ : ℝ) (hP : 0 < P) (hR : 0 < R) (hφ : 0 < φ) :
    min 1 (Vzero P R φ/(R*φ*P^2)) ≤ R/(P*Vzero P R φ) := by
  have ht : 0 < φ*P^3 := by positivity
  have hs : 0 < Real.sqrt (φ*P^3) := Real.sqrt_pos.mpr ht
  by_cases h : φ*P^3 ≤ 1
  · have hs1 : Real.sqrt (φ*P^3) ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt h
    have hv : Vzero P R φ=R/P := by simp only [Vzero,max_eq_left hs1,mul_one]
    rw [hv]
    have he : R/(P*(R/P))=1 := by field_simp
    rw [he]
    exact min_le_left _ _
  · have hs1 : 1 ≤ Real.sqrt (φ*P^3) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (le_of_not_ge h)
    have hv : Vzero P R φ=(R/P)*Real.sqrt (φ*P^3) := by
      simp only [Vzero,max_eq_right hs1]
    apply (min_le_right 1 _).trans
    rw [hv]
    apply le_of_eq
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ P^3*φ by positivity)]

theorem scaled_min_pow (M D t : ℝ) (hM : 1 ≤ M) (hD : 0 ≤ D) (_ht : 0 ≤ t)
    (hDt : D ≤ M*t) (r : ℕ) :
    min 1 (D^r) ≤ M^r*(min 1 t)^r := by
  by_cases h : t ≤ 1
  · rw [min_eq_right h]
    calc
      min 1 (D^r) ≤ D^r := min_le_right _ _
      _ ≤ (M*t)^r := pow_le_pow_left₀ hD hDt r
      _ = _ := mul_pow M t r
  · rw [min_eq_left (le_of_not_ge h),one_pow,mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ hM)

theorem width_ratio_le (P R φ q θ η : ℝ) (hP : 0 < P) (hR : 0 < R)
    (hφ : 0 < φ) (hq : R ≤ q) (hθ : φ ≤ |θ|) :
    P^η*Vzero P R φ/(q*|θ| *P^2) ≤
      P^η*(Vzero P R φ/(R*φ*P^2)) := by
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_left
  · exact mul_nonneg (Real.rpow_nonneg hP.le _) (Vzero_pos P R φ hP hR).le
  · positivity
  · have hq0 : 0 ≤ q := hR.le.trans hq
    gcongr

theorem volume_factor (P R φ q θ η : ℝ) (hP : 1 ≤ P) (hR : 0 < R)
    (hφ : 0 < φ) (hq : R ≤ q) (hθ : φ ≤ |θ|) (hη : 0 ≤ η) (r : ℕ) :
    min 1 ((P^η*Vzero P R φ/(q*|θ| *P^2))^r) ≤
      P^((r : ℝ)*η)*(R/(P*Vzero P R φ))^r := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hv : 0 < Vzero P R φ := Vzero_pos P R φ hP0 hR
  have hq0 : 0 < q := hR.trans_le hq
  have hθ0 : 0 < |θ| := hφ.trans_le hθ
  have hM : 1 ≤ P^η := Real.one_le_rpow hP hη
  have hd : 0 ≤ P^η*Vzero P R φ/(q*|θ| *P^2) := by positivity
  have ht : 0 ≤ Vzero P R φ/(R*φ*P^2) := by positivity
  have h := scaled_min_pow (P^η) _ _ hM hd ht
    (width_ratio_le P R φ q θ η hP0 hR hφ hq hθ) r
  have hm := minimum_ratio P R φ hP0 hR hφ
  have hpow : (P^η)^r=P^((r : ℝ)*η) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hP0.le]
    congr 1
    ring
  rw [hpow] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_min zero_le_one ht) hm r) (Real.rpow_nonneg hP0.le _))

theorem physical_factor (P R φ q θ η : ℝ) (hP : 1 ≤ P) (hR : 0 < R)
    (hφ : 0 < φ) (hq : R ≤ q) (hθ : φ ≤ |θ|) (hη : 0 ≤ η) (n r : ℕ) :
    P^n * min 1 ((P^η*Vzero P R φ/(q*|θ| *P^2))^r) ≤
      P^((n : ℝ)+(r : ℝ)*η)*(R/(P*Vzero P R φ))^r := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have h := mul_le_mul_of_nonneg_left
    (volume_factor P R φ q θ η hP hR hφ hq hθ hη r) (pow_nonneg hP0.le n)
  convert h using 1
  rw [← mul_assoc,← Real.rpow_natCast P n,← Real.rpow_add hP0]

end CubicTenVariables.GradientVolumeNumerics
