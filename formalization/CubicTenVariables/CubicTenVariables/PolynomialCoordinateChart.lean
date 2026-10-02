import CubicTenVariables.PolynomialCalculus
import CubicTenVariables.CoordinateReplacement
import CubicTenVariables.RealChartWeight
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Actual polynomial coordinate charts at nonsingular real points.

The map replaces coordinate `i` by the evaluated polynomial. Its derivative
is the proved row-replacement map. The inverse function theorem therefore
constructs a genuine open partial homeomorphism when the selected partial
derivative is nonzero. Its source is further restricted to the open set
where that partial is nonzero, and actual counting weights are constructed
with closed support inside this source. -/

noncomputable section
namespace CubicTenVariables.PolynomialCoordinateChart
open scoped Topology ContDiff
open MvPolynomial HessianTheorem11 PolynomialCalculus CoordinateReplacement

/-- Replace one actual coordinate by the polynomial value. -/
def coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) ℝ) (i : Fin n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  Function.update x i (eval x F)

@[simp]
theorem coordinateMap_apply_same {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) : coordinateMap F i x i = eval x F := by
  simp [coordinateMap]

theorem coordinateMap_apply_ne {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (j : Fin n) (hji : j ≠ i) :
    coordinateMap F i x j = x j := by
  simp [coordinateMap, hji]

theorem contDiff_coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) : ContDiff ℝ ∞ (coordinateMap F i) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [coordinateMap_apply_same] using contDiff_eval F
  · simpa only [coordinateMap_apply_ne F i _ j hji] using contDiff_apply ℝ ℝ j

theorem coordinateReplacement_proj_same {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    (ContinuousLinearMap.proj i).comp (coordinateReplacementCLM i (gradient F x)) =
      evalDerivative F x := by
  ext v
  simp [gradient]

theorem coordinateReplacement_proj_ne {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (j : Fin n) (hji : j ≠ i) :
    (ContinuousLinearMap.proj j).comp (coordinateReplacementCLM i (gradient F x)) =
      ContinuousLinearMap.proj j := by
  ext v
  simp [hji]

/-- The actual derivative is exactly the coordinate-replacement linear map. -/
theorem hasFDerivAt_coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (coordinateMap F i) (coordinateReplacementCLM i (gradient F x)) x := by
  apply hasFDerivAt_pi'.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [coordinateMap_apply_same, coordinateReplacement_proj_same] using
      hasFDerivAt_eval F x
  · simpa only [coordinateMap_apply_ne F i _ j hji,
      coordinateReplacement_proj_ne F i x j hji] using hasFDerivAt_apply j x

theorem fderiv_coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (coordinateMap F i) x = coordinateReplacementCLM i (gradient F x) :=
  (hasFDerivAt_coordinateMap F i x).fderiv

/-- The Jacobian determinant of the actual coordinate map is the selected
formal partial derivative. -/
theorem fderiv_coordinateMap_det {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    (fderiv ℝ (coordinateMap F i) x).det = eval x (pderiv i F) := by
  rw [fderiv_coordinateMap, coordinateReplacementCLM_det]
  rfl

theorem isOpen_partial_ne_zero {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) : IsOpen {y : Fin n → ℝ | eval y (pderiv i F) ≠ 0} :=
  isOpen_ne.preimage (MvPolynomial.continuous_eval (pderiv i F))

/-- The direct inverse-function chart, before restricting its source. -/
def localCoordinateChart {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
  (contDiff_coordinateMap F i).contDiffAt.toOpenPartialHomeomorph
    (coordinateMap F i) (f' := coordinateReplacementCLE i (gradient F x) hi)
    (by simpa using hasFDerivAt_coordinateMap F i x) (by simp)

@[simp]
theorem localCoordinateChart_coe {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    (localCoordinateChart F i x hi : (Fin n → ℝ) → (Fin n → ℝ)) = coordinateMap F i :=
  rfl

theorem mem_localCoordinateChart_source {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    x ∈ (localCoordinateChart F i x hi).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

/-- A genuine local coordinate chart whose chosen partial derivative is
nonzero everywhere on its source. -/
def coordinateChart {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ) :=
  (localCoordinateChart F i x hi).restr {y | eval y (pderiv i F) ≠ 0}

@[simp]
theorem coordinateChart_coe {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    (coordinateChart F i x hi : (Fin n → ℝ) → (Fin n → ℝ)) = coordinateMap F i :=
  rfl

theorem mem_coordinateChart_source {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    x ∈ (coordinateChart F i x hi).source := by
  rw [coordinateChart, OpenPartialHomeomorph.restr_source' _ _ (isOpen_partial_ne_zero F i)]
  exact ⟨mem_localCoordinateChart_source F i x hi, hi⟩

theorem coordinateChart_partial_ne_zero {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0)
    {y : Fin n → ℝ} (hy : y ∈ (coordinateChart F i x hi).source) :
    eval y (pderiv i F) ≠ 0 := by
  rw [coordinateChart, OpenPartialHomeomorph.restr_source' _ _ (isOpen_partial_ne_zero F i)] at hy
  exact hy.2

/-- The inverse of the constructed chart is smooth throughout its target. -/
theorem contDiffOn_coordinateChart_symm {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hi : eval x (pderiv i F) ≠ 0) :
    ContDiffOn ℝ ∞ (coordinateChart F i x hi).symm (coordinateChart F i x hi).target := by
  intro y hy
  let e := coordinateChart F i x hi
  have hpartial : eval (e.symm y) (pderiv i F) ≠ 0 :=
    coordinateChart_partial_ne_zero F i x hi (e.map_target hy)
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm (f₀' := coordinateReplacementCLE i (gradient F (e.symm y)) hpartial) hy
  · simpa only [e, coordinateChart_coe, coordinateReplacementCLE_toContinuousLinearMap] using
      hasFDerivAt_coordinateMap F i (e.symm y)
  · simpa only [e, coordinateChart_coe] using (contDiff_coordinateMap F i).contDiffAt

/-- An actual chart and an actual counting weight with closed support in
its nonsingular source; the forward map is the literal coordinate update. -/
theorem exists_coordinateChart_with_weight {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (x : Fin n → ℝ) (hx : x ≠ 0) (hi : eval x (pderiv i F) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
      (e : (Fin n → ℝ) → (Fin n → ℝ)) = coordinateMap F i ∧ x ∈ e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∃ w : SmoothCountingWeight x, tsupport w.weight ⊆ e.source ∧
        ∀ y ∈ tsupport w.weight, eval y (pderiv i F) ≠ 0 := by
  let e := coordinateChart F i x hi
  have hxe : x ∈ e.source := mem_coordinateChart_source F i x hi
  obtain ⟨w, hw⟩ := exists_smoothCountingWeight_tsupport_subset x hx e.source
    (e.open_source.mem_nhds hxe)
  exact ⟨e, coordinateChart_coe F i x hi, hxe, contDiffOn_coordinateChart_symm F i x hi,
    w, hw, fun y hy => coordinateChart_partial_ne_zero F i x hi (hw hy)⟩

end CubicTenVariables.PolynomialCoordinateChart
