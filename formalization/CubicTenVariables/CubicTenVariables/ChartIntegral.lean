import CubicTenVariables.ChartDensity
import CubicTenVariables.SingularIntegral
import Mathlib.MeasureTheory.Function.Jacobian

/-! The actual change of variables at each fixed frequency. This does not
interchange a double integral over the full frequency line and physical
space; such an absolute Fubini interchange would be invalid. -/

noncomputable section
namespace CubicTenVariables.ChartIntegral
open MvPolynomial MeasureTheory PolynomialCoordinateChart ChartDensity
open scoped Topology

theorem oscillatoryIntegral_eq_transformed {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hi : eval x (pderiv i F) ≠ 0) (w : SmoothCountingWeight x)
    (hw : tsupport w.weight ⊆ (coordinateChart F i x hi).source) (β : ℝ) :
    cubicOscillatoryIntegral F w.weight β =
      cubicOscillatoryIntegral (X i) (transformedDensity F i x hi w) β := by
  let e := coordinateChart F i x hi
  let g := cubicOscillatoryIntegrand (X i) (transformedDensity F i x hi w) β
  have hderiv : ∀ y ∈ e.source,
      HasFDerivAt e (fderiv ℝ (coordinateMap F i) y) y := by
    intro y _
    simpa only [e, coordinateChart_coe, fderiv_coordinateMap] using
      hasFDerivAt_coordinateMap F i y
  have hchange := integral_target_eq_integral_abs_det_fderiv_smul
    (μ := (volume : Measure (Fin n → ℝ))) hderiv g
  have hpoint : ∀ y ∈ e.source,
      cubicOscillatoryIntegrand F w.weight β y =
        |(fderiv ℝ (coordinateMap F i) y).det| • g (e y) := by
    intro y hy
    have hcancel := congrArg (fun t : ℝ ↦ (t : ℂ))
      (abs_partial_mul_transformedDensity F i x hi w hy)
    simp only [Complex.ofReal_mul] at hcancel
    have heval : eval (e y) (X i) = eval y F := by simp [e]
    dsimp only [g]
    rw [fderiv_coordinateMap_det]
    unfold cubicOscillatoryIntegrand
    rw [heval]
    change (w.weight y : ℂ) * _ =
      ((|eval y (pderiv i F)| : ℝ) : ℂ) *
        ((transformedDensity F i x hi w (e y) : ℂ) * _)
    rw [← mul_assoc, hcancel]
  unfold cubicOscillatoryIntegral
  calc
    (∫ y, cubicOscillatoryIntegrand F w.weight β y) =
        ∫ y in e.source, cubicOscillatoryIntegrand F w.weight β y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hwy : w.weight y = 0 := by
        by_contra hn
        exact hy (hw (subset_tsupport w.weight hn))
      simp [cubicOscillatoryIntegrand, hwy]
    _ = ∫ y in e.source, |(fderiv ℝ (coordinateMap F i) y).det| • g (e y) :=
      setIntegral_congr_fun e.open_source.measurableSet hpoint
    _ = ∫ z in e.target, g z := hchange.symm
    _ = ∫ z, g z := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp only [g, cubicOscillatoryIntegrand,
        transformedDensity_of_notMem_target F i x hi w hz,
        Complex.ofReal_zero, zero_mul]

end CubicTenVariables.ChartIntegral
