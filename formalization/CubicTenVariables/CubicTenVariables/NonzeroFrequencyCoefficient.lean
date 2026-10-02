import CubicTenVariables.NonzeroFrequencyNumerics

/-! Exact coefficient and epsilon bookkeeping for the n=10 nonzero-frequency
reduction. These are numerical inequalities, with no arithmetic or analytic
estimate assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.NonzeroFrequencyCoefficient
open NonzeroFrequencyNumerics

/-- The averaging denominator dominates the positive integer window width. -/
theorem width_ratio_le (R : ℝ) (hR : 0 ≤ R) (L : ℕ) (hL : 1 ≤ L) :
    ((L : ℝ)+R^((1 : ℝ)/3))^10 / (((2*L+1 : ℕ) : ℝ)^10) ≤
      (1+R^((1 : ℝ)/3)/(L : ℝ))^10 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hden : (L : ℝ) ≤ ((2*L+1 : ℕ) : ℝ) := by exact_mod_cast (show L ≤ 2*L+1 by omega)
  have hratio : ((L : ℝ)+R^((1 : ℝ)/3))/((2*L+1 : ℕ) : ℝ) ≤
      ((L : ℝ)+R^((1 : ℝ)/3))/(L : ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity) hLpos hden
  have hp := pow_le_pow_left₀ (by positivity :
    0 ≤ ((L : ℝ)+R^((1 : ℝ)/3))/((2*L+1 : ℕ) : ℝ)) hratio 10
  have he : ((L : ℝ)+R^((1 : ℝ)/3))/(L : ℝ) = 1+R^((1 : ℝ)/3)/(L : ℝ) := by
    rw [add_div,div_self hLpos.ne']
  rw [← div_pow,← he]
  exact hp

/-- Conversion of the shifted-average coefficient to the phase-optimization
coefficient, for every positive natural window width. -/
theorem shifted_coefficient_le (P R φ Ca ε b Kgeom : ℝ) (L : ℕ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 ≤ φ) (hCa : 0 ≤ Ca)
    (hKgeom : 0 ≤ Kgeom) (hL : 1 ≤ L) :
    φ*((Ca*P^(7*ε)*((L : ℝ)+R^((1 : ℝ)/3))^10*R^b) /
      (((2*L+1 : ℕ) : ℝ)^10)) * (R^10)⁻¹ * (P^(10+ε)*Kgeom) ≤
    Ca*P^(7*ε)*(φ*R^(b-10)*P^(10+ε)*
      (1+R^((1 : ℝ)/3)/(L : ℝ))^10*Kgeom) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hr : R^b*(R^10)⁻¹=R^(b-10) := by
    simp [Real.rpow_sub hR0,div_eq_mul_inv]
  calc
    _ = Ca*P^(7*ε)*(φ*(R^b*(R^10)⁻¹)*P^(10+ε)*
        (((L : ℝ)+R^((1 : ℝ)/3))^10 / (((2*L+1 : ℕ) : ℝ)^10))*Kgeom) := by ring
    _ = Ca*P^(7*ε)*(φ*R^(b-10)*P^(10+ε)*
        (((L : ℝ)+R^((1 : ℝ)/3))^10 / (((2*L+1 : ℕ) : ℝ)^10))*Kgeom) := by rw [hr]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hKgeom
      exact mul_le_mul_of_nonneg_left (width_ratio_le R hR0.le L hL) (by positivity)

/-- The literal cube-root width satisfies the same coefficient inequality. -/
theorem cubeRoot_coefficient_le (P R φ Ca ε b Kgeom : ℝ)
    (hP : 1 ≤ P) (hR : 1 ≤ R) (hφ : 0 ≤ φ) (hCa : 0 ≤ Ca)
    (hKgeom : 0 ≤ Kgeom) :
    φ*((Ca*P^(7*ε)*((cubeRootWidth R : ℝ)+R^((1 : ℝ)/3))^10*R^b) /
      (((2*cubeRootWidth R+1 : ℕ) : ℝ)^10)) * (R^10)⁻¹ * (P^(10+ε)*Kgeom) ≤
    Ca*P^(7*ε)*(φ*R^(b-10)*P^(10+ε)*
      (1+R^((1 : ℝ)/3)/(cubeRootWidth R : ℝ))^10*Kgeom) :=
  shifted_coefficient_le P R φ Ca ε b Kgeom (cubeRootWidth R) hP hR hφ hCa hKgeom
    (cubeRootWidth_pos R hR)

/-- The seven-epsilon shifted-average loss fits into the final source loss. -/
theorem exponent_combine (P β η ε : ℝ) (hP : 1 ≤ P) (hβ : 0 < β)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) :
    P^(7*ε)*P^(7+ε+18*η+(β+5/2)*(ε/17)-saving β) ≤
      P^(7+(18+β)*(η+ε)-saving β) := by
  rw [← Real.rpow_add (zero_lt_one.trans_le hP)]
  apply Real.rpow_le_rpow_of_exponent_le hP
  nlinarith [mul_nonneg hβ.le hη,mul_nonneg hβ.le hε]

/-- The admissible source phase is at most one when eta≤1. -/
theorem phase_le_one (P R φ η : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hη : η ≤ 1) (hφ : φ ≤ (R*P^((3 : ℝ)/2))^(-1+η)) : φ ≤ 1 := by
  apply hφ.trans
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact one_le_mul_of_one_le_of_one_le hR (Real.one_le_rpow hP (by norm_num))
  · linarith

/-- The original dyadic moduli lie below P² once P≥4. -/
theorem twice_radius_le_square (P R : ℝ) (hP : 4 ≤ P)
    (hRP : R ≤ P^((3 : ℝ)/2)) : 2*R ≤ P^2 := by
  have hP0 : 0 < P := by linarith
  have hs : (2 : ℝ) ≤ P^((1 : ℝ)/2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hP
      (by norm_num : (0 : ℝ) ≤ 1/2)
    have hfour : (4 : ℝ)^((1 : ℝ)/2)=2 := by norm_num [← Real.sqrt_eq_rpow]
    simpa only [hfour] using h
  calc
    2*R ≤ 2*P^((3 : ℝ)/2) := mul_le_mul_of_nonneg_left hRP (by norm_num)
    _ ≤ P^((1 : ℝ)/2)*P^((3 : ℝ)/2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = P^2 := by
      rw [← Real.rpow_add hP0]
      norm_num

end CubicTenVariables.NonzeroFrequencyCoefficient
