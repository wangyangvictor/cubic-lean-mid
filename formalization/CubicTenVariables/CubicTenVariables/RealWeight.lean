import CubicTenVariables.RealPlace
import CubicTenVariables.WeightedCounting
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual smooth counting weights near the proved nonsingular real zero.
The weights are nonnegative, compactly supported away from the origin,
equal to one at the chosen point, and supported in a concrete integer-radius
box. Positivity of the singular integral is a separate remaining argument. -/

noncomputable section
namespace CubicTenVariables
open scoped Topology ContDiff
open Filter MvPolynomial HessianTheorem11

/-- An actual smooth weight with every support condition needed by the
localized counting functional. The next theorem constructs it. -/
structure SmoothCountingWeight {n : ℕ} (x : Fin n → ℝ) where
  weight : (Fin n → ℝ) → ℝ
  boxRadius : ℕ
  smooth : ContDiff ℝ ∞ weight
  compact : HasCompactSupport weight
  bounds : ∀ y, 0 ≤ weight y ∧ weight y ≤ 1
  value_at : weight x = 1
  origin_excluded : (0 : Fin n → ℝ) ∉ tsupport weight
  supported : WeightSupportedInBox weight boxRadius

theorem exists_smoothCountingWeight {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    Nonempty (SmoothCountingWeight x) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨w, hsupport, hcompact, hsmooth, hbounds, hwx⟩ :=
    exists_smooth_tsupport_subset (Metric.ball_mem_nhds x (half_pos hxpos))
  obtain ⟨A, hA⟩ := exists_nat_ge (‖x‖ + ‖x‖ / 2)
  refine ⟨⟨w, A, hsmooth, hcompact, ?_, hwx, ?_, ?_⟩⟩
  · intro y
    exact hbounds (Set.mem_range_self y)
  · intro hz
    have hb := Metric.mem_ball.mp (hsupport hz)
    simp only [dist_zero_left] at hb
    linarith
  · intro y hy i
    have hyt : y ∈ tsupport w := subset_tsupport w hy
    have hyball := Metric.mem_ball.mp (hsupport hyt)
    have htri := dist_triangle y x 0
    simp only [dist_zero_right] at htri
    have hnorm : ‖y‖ ≤ (A : ℝ) := by linarith
    have hi := norm_le_pi_norm y i
    simpa only [Real.norm_eq_abs] using hi.trans hnorm

theorem SmoothCountingWeight.zero_at_origin {n : ℕ} {x : Fin n → ℝ}
    (w : SmoothCountingWeight x) : w.weight 0 = 0 := by
  by_contra h
  exact w.origin_excluded (subset_tsupport w.weight h)

/-- The weight is positive throughout a real neighborhood of the selected
point, not only at that one point. -/
theorem SmoothCountingWeight.eventually_pos {n : ℕ} {x : Fin n → ℝ}
    (w : SmoothCountingWeight x) : ∀ᶠ y in 𝓝 x, 0 < w.weight y := by
  apply w.smooth.continuous.continuousAt.tendsto.eventually_const_lt
  rw [w.value_at]
  norm_num

/-- The real point and the analytic counting weight are both constructed
from rational anisotropy; neither is a local-solubility input. -/
theorem exists_nonsingular_real_zero_with_weight {n : ℕ}
    (F : AnisotropicCubic n) (hn : 2 ≤ n) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧
      eval x (map (algebraMap ℚ ℝ) F.polynomial) = 0 ∧
      gradient (map (algebraMap ℚ ℝ) F.polynomial) x ≠ 0 ∧
      Nonempty (SmoothCountingWeight x) := by
  obtain ⟨x, hx, hF, hgrad⟩ := RealPlace.exists_nonsingular_real_zero F hn
  exact ⟨x, hx, hF, hgrad, exists_smoothCountingWeight x hx⟩

end CubicTenVariables
