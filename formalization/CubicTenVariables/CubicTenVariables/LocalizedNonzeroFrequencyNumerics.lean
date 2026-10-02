import CubicTenVariables.LocalizedFrequencyComparison
import CubicTenVariables.NonzeroFrequencyCoefficient

/-! A fixed threshold places all lcm denominators in the range required
by rapid frequency decay while retaining the original dyadic radius. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedNonzeroFrequencyNumerics

theorem twice_weighted_radius_le_square (P R κ : ℝ) (hκ : 0 < κ)
    (hP : (2*κ)^2 ≤ P) (hRP : R ≤ P^((3:ℝ)/2)) : 2*κ*R ≤ P^2 := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hs : 2*κ ≤ P^((1:ℝ)/2) := by
    have hh := Real.sqrt_le_sqrt hP
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2*κ),Real.sqrt_eq_rpow] using hh
  calc
    2*κ*R ≤ (2*κ)*P^((3:ℝ)/2) := mul_le_mul_of_nonneg_left hRP (by positivity)
    _ ≤ P^((1:ℝ)/2)*P^((3:ℝ)/2) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = P^2 := by rw [← Real.rpow_add hP0]; norm_num

end CubicTenVariables.LocalizedNonzeroFrequencyNumerics
