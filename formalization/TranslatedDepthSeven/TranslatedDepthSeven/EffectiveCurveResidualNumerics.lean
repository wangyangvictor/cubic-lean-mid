import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absorbing the degree-effective curve residual

The degree-effective curve estimate used in the surface determinant route
has residual
`c * E^4 * H^(1/2) * (log H + E)`.  This file records the elementary
power bookkeeping when the current total component degree satisfies
`E <= A * H^eta`.  It is independent of all geometric definitions.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- If the total curve-degree mass grows like `H^eta`, its fourth-power
curve-count residual costs five copies of `eta`: four from `E^4` and one
from `log H + E`. -/
theorem effectiveCurveResidual_le_target
    (c A E H eta epsilon : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hH : 1 ≤ H) (heta : 0 < eta)
    (hEbound : E ≤ A * H ^ eta)
    (hexponent : (1 / 2 : ℝ) + 5 * eta ≤ 1 + epsilon) :
    c * E ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) * (Real.log H + E) ≤
      c * A ^ (4 : ℕ) * (eta⁻¹ + A) * H ^ (1 + epsilon) := by
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hlog : Real.log H ≤ eta⁻¹ * H ^ eta := by
    have h := Real.log_le_rpow_div hH0 heta
    rw [div_eq_inv_mul] at h
    exact h
  have hsum : Real.log H + E ≤ (eta⁻¹ + A) * H ^ eta := by
    calc
      Real.log H + E ≤ eta⁻¹ * H ^ eta + A * H ^ eta :=
        add_le_add hlog hEbound
      _ = (eta⁻¹ + A) * H ^ eta := by ring
  have hEpow : E ^ (4 : ℕ) ≤ (A * H ^ eta) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hE hEbound 4
  have hsum0 : 0 ≤ Real.log H + E := by
    exact add_nonneg (Real.log_nonneg hH) hE
  have hcoef0 : 0 ≤ eta⁻¹ + A := add_nonneg hinv hA
  calc
    c * E ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) * (Real.log H + E) ≤
        c * (A * H ^ eta) ^ (4 : ℕ) * H ^ (1 / 2 : ℝ) *
          ((eta⁻¹ + A) * H ^ eta) := by
      gcongr
    _ = c * A ^ (4 : ℕ) * (eta⁻¹ + A) *
          H ^ ((1 / 2 : ℝ) + 5 * eta) := by
      rw [mul_pow]
      rw [show (H ^ eta) ^ (4 : ℕ) = H ^ (eta * 4) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hH0]
        norm_num]
      have hpowers : H ^ (eta * 4) * H ^ (1 / 2 : ℝ) * H ^ eta =
          H ^ ((1 / 2 : ℝ) + 5 * eta) := by
        rw [← Real.rpow_add hHpos (eta * 4) (1 / 2 : ℝ)]
        rw [← Real.rpow_add hHpos (eta * 4 + (1 / 2 : ℝ)) eta]
        congr 1
        ring
      rw [← hpowers]
      ring
    _ ≤ c * A ^ (4 : ℕ) * (eta⁻¹ + A) * H ^ (1 + epsilon) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH hexponent)
        (mul_nonneg (mul_nonneg hc (by positivity)) hcoef0)

/-- After summing the curve residual over at most one degree-mass factor
of persistent components, the fifth power of `E` costs six copies of
`eta`.  This is the numerical form used by the assembled surface count. -/
theorem effectiveSurfaceResidual_le_target
    (c A E H eta epsilon : ℝ)
    (hc : 0 ≤ c) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hH : 1 ≤ H) (heta : 0 < eta)
    (hEbound : E ≤ A * H ^ eta)
    (hexponent : (1 / 2 : ℝ) + 6 * eta ≤ 1 + epsilon) :
    c * E ^ (5 : ℕ) * H ^ (1 / 2 : ℝ) * (Real.log H + E) ≤
      c * A ^ (5 : ℕ) * (eta⁻¹ + A) * H ^ (1 + epsilon) := by
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hlog : Real.log H ≤ eta⁻¹ * H ^ eta := by
    have h := Real.log_le_rpow_div hH0 heta
    rw [div_eq_inv_mul] at h
    exact h
  have hsum : Real.log H + E ≤ (eta⁻¹ + A) * H ^ eta := by
    calc
      Real.log H + E ≤ eta⁻¹ * H ^ eta + A * H ^ eta :=
        add_le_add hlog hEbound
      _ = (eta⁻¹ + A) * H ^ eta := by ring
  have hEpow : E ^ (5 : ℕ) ≤ (A * H ^ eta) ^ (5 : ℕ) :=
    pow_le_pow_left₀ hE hEbound 5
  have hsum0 : 0 ≤ Real.log H + E := by
    exact add_nonneg (Real.log_nonneg hH) hE
  have hcoef0 : 0 ≤ eta⁻¹ + A := add_nonneg hinv hA
  calc
    c * E ^ (5 : ℕ) * H ^ (1 / 2 : ℝ) * (Real.log H + E) ≤
        c * (A * H ^ eta) ^ (5 : ℕ) * H ^ (1 / 2 : ℝ) *
          ((eta⁻¹ + A) * H ^ eta) := by
      gcongr
    _ = c * A ^ (5 : ℕ) * (eta⁻¹ + A) *
          H ^ ((1 / 2 : ℝ) + 6 * eta) := by
      rw [mul_pow]
      rw [show (H ^ eta) ^ (5 : ℕ) = H ^ (eta * 5) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hH0]
        norm_num]
      have hpowers : H ^ (eta * 5) * H ^ (1 / 2 : ℝ) * H ^ eta =
          H ^ ((1 / 2 : ℝ) + 6 * eta) := by
        rw [← Real.rpow_add hHpos (eta * 5) (1 / 2 : ℝ)]
        rw [← Real.rpow_add hHpos (eta * 5 + (1 / 2 : ℝ)) eta]
        congr 1
        ring
      rw [← hpowers]
      ring
    _ ≤ c * A ^ (5 : ℕ) * (eta⁻¹ + A) * H ^ (1 + epsilon) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH hexponent)
        (mul_nonneg (mul_nonneg hc (by positivity)) hcoef0)

end

end TranslatedDepthSeven
