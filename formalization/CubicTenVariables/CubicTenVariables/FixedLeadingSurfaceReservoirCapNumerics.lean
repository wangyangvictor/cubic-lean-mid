import CubicTenVariables.FixedLeadingSurfacePrimeReservoir

/-! # Literal natural caps for the logarithmic-prime reservoir -/
namespace CubicTenVariables.FixedLeadingSurfaceReservoirCapNumerics
noncomputable section
open TranslatedDepthSeven

/-- Rounding the terminal modulus upward only adds one to its fixed
coefficient, since the two height powers have product at least one. -/
theorem ceil_terminal_cap_le
    (H : ℕ) (Cq α δ : ℝ) (hH : 1 ≤ H)
    (hCq : 0 ≤ Cq) (hα : 0 ≤ α) (hδ : 0 ≤ δ) :
    (⌈Cq * (H : ℝ) ^ α * (H : ℝ) ^ δ⌉₊ : ℝ) ≤
      (Cq + 1) * (H : ℝ) ^ δ * (H : ℝ) ^ α := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have ha := Real.one_le_rpow hHr hα
  have hd := Real.one_le_rpow hHr hδ
  have hp : 1 ≤ (H : ℝ) ^ α * (H : ℝ) ^ δ := by nlinarith
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ Cq * (H : ℝ) ^ α * (H : ℝ) ^ δ by positivity)
  nlinarith

/-- The actual prime cap is bounded by an explicit small power. The
logarithmic estimate is proved in mathlib and requires no new assumption. -/
theorem floor_prime_cap_le
    (H : ℕ) (Cint δ : ℝ) (hH : 1 ≤ H)
    (hCint : 0 ≤ Cint) (hδ : 0 < δ) :
    (⌊2 * (Cint * Real.log (H : ℝ))⌋₊ : ℝ) ≤
      (2 * Cint / δ) * (H : ℝ) ^ δ := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlog := Real.log_nonneg hHr
  have hf := Nat.floor_le
    (show 0 ≤ 2 * (Cint * Real.log (H : ℝ)) by positivity)
  have hg := Real.log_le_rpow_div (show 0 ≤ (H : ℝ) by positivity) hδ
  calc
    _ ≤ 2 * (Cint * Real.log (H : ℝ)) := hf
    _ ≤ 2 * (Cint * ((H : ℝ) ^ δ / δ)) := by gcongr
    _ = _ := by ring

/-- The fixed coefficients occurring in the ordinary-box reservoir are
nonnegative in the full range used by the determinant estimate. -/
theorem actual_reservoir_coefficients_nonneg
    (d e : ℕ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    0 ≤ manuscriptPoolDepthCoefficient (e + 1 + d + 2 : ℕ) α ∧
    0 ≤ manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) α ∧
    0 ≤ (4 * manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) α *
      (δ / 3)⁻¹) * 2 ∧
    0 ≤ 2 * manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) α / δ := by
  simp only [manuscriptPrimeIntervalCoefficient, manuscriptPoolDepthCoefficient]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

end
end CubicTenVariables.FixedLeadingSurfaceReservoirCapNumerics
