import CubicTenVariables.PolynomialCoordinateChart
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! The literal density after the polynomial coordinate change.

Inside the actual chart target this is the weight composed with the inverse,
divided by the absolute value of the selected partial derivative. Outside
the target it is zero. Compactness of the weight's closed support makes
the zero extension smooth when that support lies inside the chart source.
No singular integral or Fourier identity is assumed or asserted here. -/

noncomputable section
namespace CubicTenVariables.ChartDensity
open scoped Topology ContDiff
open MvPolynomial PolynomialCalculus PolynomialCoordinateChart

variable {n : ℕ} (F : MvPolynomial (Fin n) ℝ) (i : Fin n)
  (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) (w : SmoothCountingWeight x)

/-- The actual transformed density, extended by zero outside the chart. -/
def transformedDensity (z : Fin n → ℝ) : ℝ := by
  classical
  exact if z ∈ (coordinateChart F i x hi).target then
    w.weight ((coordinateChart F i x hi).symm z) /
      |eval ((coordinateChart F i x hi).symm z) (pderiv i F)|
  else 0

theorem transformedDensity_of_mem_target {z : Fin n → ℝ}
    (hz : z ∈ (coordinateChart F i x hi).target) :
    transformedDensity F i x hi w z =
      w.weight ((coordinateChart F i x hi).symm z) /
        |eval ((coordinateChart F i x hi).symm z) (pderiv i F)| := by
  simp only [transformedDensity, if_pos hz]

theorem transformedDensity_of_notMem_target {z : Fin n → ℝ}
    (hz : z ∉ (coordinateChart F i x hi).target) :
    transformedDensity F i x hi w z = 0 := by
  simp only [transformedDensity, if_neg hz]

/-- On the chart source the density is the literal Jacobian quotient. -/
theorem transformedDensity_at_source {y : Fin n → ℝ}
    (hy : y ∈ (coordinateChart F i x hi).source) :
    transformedDensity F i x hi w ((coordinateChart F i x hi) y) =
      w.weight y / |eval y (pderiv i F)| := by
  rw [transformedDensity_of_mem_target F i x hi w
    ((coordinateChart F i x hi).map_source hy), (coordinateChart F i x hi).left_inv hy]

/-- Multiplication by the actual absolute Jacobian recovers the weight. -/
theorem abs_partial_mul_transformedDensity {y : Fin n → ℝ}
    (hy : y ∈ (coordinateChart F i x hi).source) :
    |eval y (pderiv i F)| * transformedDensity F i x hi w ((coordinateChart F i x hi) y) =
      w.weight y := by
  rw [transformedDensity_at_source F i x hi w hy, mul_comm,
    div_mul_cancel₀ _ (abs_ne_zero.mpr (coordinateChart_partial_ne_zero F i x hi hy))]

theorem transformedDensity_nonneg (z : Fin n → ℝ) :
    0 ≤ transformedDensity F i x hi w z := by
  unfold transformedDensity
  split_ifs
  · exact div_nonneg (w.bounds _).1 (abs_nonneg _)
  · exact le_rfl

/-- Even before taking the closure, every nonzero density value comes
from the weight's support under this same chart. -/
theorem support_transformedDensity_subset_image :
    Function.support (transformedDensity F i x hi w) ⊆
      (coordinateChart F i x hi) '' tsupport w.weight := by
  intro z hz
  have ht : z ∈ (coordinateChart F i x hi).target := by
    by_contra h
    exact hz (transformedDensity_of_notMem_target F i x hi w h)
  have hw : w.weight ((coordinateChart F i x hi).symm z) ≠ 0 := by
    intro hw
    apply hz
    rw [transformedDensity_of_mem_target F i x hi w ht, hw, zero_div]
  exact ⟨(coordinateChart F i x hi).symm z, subset_tsupport w.weight hw,
    (coordinateChart F i x hi).right_inv ht⟩

theorem isCompact_chart_image_tsupport :
    IsCompact ((coordinateChart F i x hi) '' tsupport w.weight) := by
  simpa only [coordinateChart_coe] using
    w.compact.isCompact.image (contDiff_coordinateMap F i).continuous

/-- The density's entire closed support lies in the compact image of the
weight's closed support. -/
theorem tsupport_transformedDensity_subset_image :
    tsupport (transformedDensity F i x hi w) ⊆
      (coordinateChart F i x hi) '' tsupport w.weight :=
  closure_minimal (support_transformedDensity_subset_image F i x hi w)
    (isCompact_chart_image_tsupport F i x hi w).isClosed

theorem hasCompactSupport_transformedDensity :
    HasCompactSupport (transformedDensity F i x hi w) :=
  (isCompact_chart_image_tsupport F i x hi w).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_transformedDensity_subset_image F i x hi w)

theorem chart_image_tsupport_subset_target
    (hw : tsupport w.weight ⊆ (coordinateChart F i x hi).source) :
    (coordinateChart F i x hi) '' tsupport w.weight ⊆ (coordinateChart F i x hi).target := by
  rintro z ⟨y, hy, rfl⟩
  exact (coordinateChart F i x hi).map_source (hw hy)

theorem tsupport_transformedDensity_subset_target
    (hw : tsupport w.weight ⊆ (coordinateChart F i x hi).source) :
    tsupport (transformedDensity F i x hi w) ⊆ (coordinateChart F i x hi).target :=
  (tsupport_transformedDensity_subset_image F i x hi w).trans
    (chart_image_tsupport_subset_target F i x hi w hw)

/-- Smoothness inside the target uses the proved smooth inverse and the
nonzero selected partial on the chart source. -/
theorem contDiffAt_transformedDensity_of_mem_target {z : Fin n → ℝ}
    (hz : z ∈ (coordinateChart F i x hi).target) :
    ContDiffAt ℝ ∞ (transformedDensity F i x hi w) z := by
  let e := coordinateChart F i x hi
  have hinv : ContDiffAt ℝ ∞ e.symm z :=
    (contDiffOn_coordinateChart_symm F i x hi).contDiffAt (e.open_target.mem_nhds hz)
  have hpartial : eval (e.symm z) (pderiv i F) ≠ 0 :=
    coordinateChart_partial_ne_zero F i x hi (e.map_target hz)
  have hnum := w.smooth.contDiffAt.comp z hinv
  have hden := (contDiff_eval (pderiv i F)).contDiffAt.comp z hinv
  apply (hnum.div (hden.abs hpartial) (abs_ne_zero.mpr hpartial)).congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hz] with y hy
  exact transformedDensity_of_mem_target F i x hi w hy

/-- The compact-image support argument makes the zero extension smooth
also at every boundary point of the chart target. -/
theorem contDiff_transformedDensity
    (hw : tsupport w.weight ⊆ (coordinateChart F i x hi).source) :
    ContDiff ℝ ∞ (transformedDensity F i x hi w) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ (coordinateChart F i x hi).target
  · exact contDiffAt_transformedDensity_of_mem_target F i x hi w hz
  · have hnot : z ∉ tsupport (transformedDensity F i x hi w) := by
      intro hs
      exact hz (tsupport_transformedDensity_subset_target F i x hi w hw hs)
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hnot)

/-- At the selected chart point the numerator is exactly one. -/
theorem transformedDensity_at_chart_point :
    transformedDensity F i x hi w ((coordinateChart F i x hi) x) =
      1 / |eval x (pderiv i F)| := by
  have hx : x ∈ (coordinateChart F i x hi).source := mem_coordinateChart_source F i x hi
  rw [transformedDensity_of_mem_target F i x hi w
    ((coordinateChart F i x hi).map_source hx), (coordinateChart F i x hi).left_inv hx,
    w.value_at]

theorem transformedDensity_pos_at_chart_point :
    0 < transformedDensity F i x hi w ((coordinateChart F i x hi) x) := by
  rw [transformedDensity_at_chart_point]
  exact one_div_pos.mpr (abs_pos.mpr hi)

end CubicTenVariables.ChartDensity
