import CubicTenVariables.ChartIntegral
import CubicTenVariables.CoordinateMarginal
import CubicTenVariables.CompactMarginal
import CubicTenVariables.FourierMarginal

/-! Positivity of the actual singular integral near a nonsingular real zero.

The weight, coordinate chart, Jacobian density, and marginal are all actual
functions. Smoothness and compact support of the marginal are proved, and
Fourier inversion then supplies frequency integrability and the exact value
of the iterated integral. No positivity or analytic input is assumed.
-/

noncomputable section
namespace CubicTenVariables
open MvPolynomial MeasureTheory Filter HessianTheorem11
open PolynomialCoordinateChart ChartDensity CoordinateMarginal FourierMarginal
open scoped Topology ContDiff

/-- The actual coordinate marginal of a smooth compact density, bundled as
a Schwartz function using proved regularity and support bounds. -/
def schwartzCoordinateMarginal {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    SchwartzMap ℝ ℝ :=
  (CompactMarginal.hasCompactSupport_marginal (splitDensity i a)
    (hasCompactSupport_splitDensity i a hc)).toSchwartzMap
      (CompactMarginal.contDiff_marginal (splitDensity i a)
        (contDiff_splitDensity i a ha) (hasCompactSupport_splitDensity i a hc))

@[simp] theorem schwartzCoordinateMarginal_apply {m : ℕ} (i : Fin (m + 1))
    (a : (Fin (m + 1) → ℝ) → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (t : ℝ) :
    schwartzCoordinateMarginal i a ha hc t = coordinateMarginal i a t := rfl

/-- A weight supported inside the actual nonsingular chart has an integrable
frequency integral, a strictly positive real singular integral, and the
corresponding limit of the actual truncated integrals. -/
theorem positive_singularIntegral_of_chart_weight {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℝ) (i : Fin (m + 1))
    (x : Fin (m + 1) → ℝ) (hi : eval x (pderiv i F) ≠ 0)
    (hFx : eval x F = 0) (w : SmoothCountingWeight x)
    (hw : tsupport w.weight ⊆ (coordinateChart F i x hi).source) :
    Integrable (cubicOscillatoryIntegral F w.weight) ∧
      ∃ J : ℝ, 0 < J ∧ cubicSingularIntegral F w.weight = (J : ℂ) ∧
        Tendsto (cubicSingularIntegralTruncated F w.weight) atTop (𝓝 (J : ℂ)) := by
  let a := transformedDensity F i x hi w
  have ha : ContDiff ℝ ∞ a := contDiff_transformedDensity F i x hi w hw
  have hc : HasCompactSupport a := hasCompactSupport_transformedDensity F i x hi w
  let g := schwartzCoordinateMarginal i a ha hc
  have heq : cubicOscillatoryIntegral F w.weight = positiveFourier g := by
    funext β
    rw [ChartIntegral.oscillatoryIntegral_eq_transformed F i x hi w hw β]
    simpa only [cubicOscillatoryIntegral, cubicOscillatoryIntegrand, eval_X,
      positiveFourier, g, schwartzCoordinateMarginal_apply] using
      coordinate_integral_eq_marginal i a ha.continuous hc β
  have hg : 0 < g 0 := by
    apply coordinateMarginal_zero_pos i a ha.continuous hc
      (transformedDensity_nonneg F i x hi w) ((coordinateChart F i x hi) x)
    · simpa only [coordinateChart_coe, coordinateMap_apply_same] using hFx
    · exact transformedDensity_pos_at_chart_point F i x hi w
  refine ⟨?_, g 0, hg, ?_, ?_⟩
  · rw [heq]
    exact positiveFourier_integrable g
  · unfold cubicSingularIntegral
    rw [heq]
    exact integral_positiveFourier g
  · unfold cubicSingularIntegralTruncated
    simpa only [heq] using
      tendsto_intervalIntegral_positiveFourier g

/-- Every nonzero nonsingular real polynomial zero admits an actual smooth
counting weight with strictly positive singular integral. This theorem does
not require the polynomial to be homogeneous or cubic. -/
theorem exists_smoothCountingWeight_positive_singularIntegral {m : ℕ}
    (F : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin (m + 1) → ℝ)
    (hx : x ≠ 0) (hFx : eval x F = 0) (hgrad : gradient F x ≠ 0) :
    ∃ w : SmoothCountingWeight x,
      Integrable (cubicOscillatoryIntegral F w.weight) ∧
        ∃ J : ℝ, 0 < J ∧ cubicSingularIntegral F w.weight = (J : ℂ) ∧
          Tendsto (cubicSingularIntegralTruncated F w.weight) atTop (𝓝 (J : ℂ)) := by
  classical
  have hex : ∃ i : Fin (m + 1), eval x (pderiv i F) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hgrad (funext h)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨w, hw⟩ := exists_smoothCountingWeight_tsupport_subset x hx
    (coordinateChart F i x hi).source
    ((coordinateChart F i x hi).open_source.mem_nhds (mem_coordinateChart_source F i x hi))
  exact ⟨w, positive_singularIntegral_of_chart_weight F i x hi hFx w hw⟩

end CubicTenVariables
