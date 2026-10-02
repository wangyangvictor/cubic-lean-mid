import TranslatedDepthSeven.Salberger2023ProjectedBoxThreshold
import TranslatedDepthSeven.QuadraticFilteredPlaneCurveThreshold

/-! # Absorbing a bounded-degree affine projection in the half-power gap -/

namespace TranslatedDepthSeven
noncomputable section
open Filter
open scoped Topology

/-- With a degree cap fixed in advance, the projection enlarges the box by
one fixed factor. Every positive exponent gap absorbs it uniformly. -/
theorem eventually_boundedDegree_projectedCurve_boxPower_le
    (N D : ℕ) (r β : ℝ) (hr : 0 ≤ r) (hrβ : r < β) :
    ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ, δ ≤ D → (M : ℝ) ≤ V →
      (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^ r ≤ V ^ β := by
  let C : ℕ := (N + 1) * (D + 1) ^ (2 * (N + 1))
  have hCnat : 1 ≤ C := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      dsimp only [C]
      positivity)
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast hCnat
  have habs := eventually_polylog_mul_rpow_le_rpow
    ((C : ℝ) ^ r) r β 0 (by positivity) hrβ
  filter_upwards [habs, eventually_ge_atTop (1 : ℝ)] with V habsV hV
  intro δ M hδ hM
  have hmass : boundedAffineProjectionRowMassBound N δ ≤ C := by
    exact (boundedAffineProjectionRowMassBound_le_degreePower N δ).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hmaxM : ((max 1 M : ℕ) : ℝ) ≤ V := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hV hM
  have hbox : (salbergerProjectedCurveBoxRadius N δ M : ℝ) ≤ (C : ℝ) * V := by
    rw [salbergerProjectedCurveBoxRadius, Nat.cast_max, Nat.cast_one, Nat.cast_mul]
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le hC hV
    · exact mul_le_mul (by exact_mod_cast hmass) hmaxM (by positivity) (by positivity)
  calc
    (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^ r ≤ ((C : ℝ) * V) ^ r :=
      Real.rpow_le_rpow (by positivity) hbox hr
    _ = (C : ℝ) ^ r * V ^ r := Real.mul_rpow (by positivity) (by linarith)
    _ ≤ V ^ β := by simpa using habsV

end
end TranslatedDepthSeven
