import TranslatedDepthSeven.EffectiveFixedRelativeSurfaceCover

/-!
# Finite relative charts for rational curve components

This is the relative-dimension-one analogue of
`EffectiveFixedRelativeSurfaceCover`.  It reuses the same fixed finite-cover
component models and their internally proved monic-coordinate height bounds.
Only the standard-smooth chart shape changes: a curve in `N` affine
variables has `N-1` local equations.

The two explicit standard algebraic-geometry inputs are the dimension-one
specializations of finite-etale component-union spreading and finite
standard-smooth chart extraction.  They contain no height or counting
conclusion.  Catalogue and certificate exponents are chosen from the fixed
equation family before any fibre, point, prime, or epsilon.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance effectiveFixedRelativeCurveCoverPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Component-model coverage specialized to rational prime projective
curves.  The underlying model catalogue is the existing dimension-generic
finite-cover structure. -/
def RelativeRationalSurfaceComponentModelCatalogue.CoversPrimeCurves
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ)) : Prop :=
  ∀ (baseParameter : Fin M → ℤ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I ∈ finiteMinimalPrimes
      (finiteEquationIdeal (fibreEquations baseParameter)) →
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    (∃ d : ℕ, HasProjectiveDimensionDegree I 1 d) →
      Nonempty
        (RelativeRationalSurfaceComponentModelWitness
          models baseParameter I)

/-- A finite catalogue of integral relative curve charts.  Each chart has
`N-1` local equations and one principal-open clearing polynomial. -/
structure RelativeRationalCurveChartCatalogue (M N : ℕ) where
  liftedParameterCount : ℕ
  baseCoordinate : Fin M → Fin liftedParameterCount
  baseCoordinate_injective : Function.Injective baseCoordinate
  chartCount : ℕ
  componentGeneratorCount : ℕ
  stratumEquationCount : ℕ
  chart : Fin chartCount →
    RelativePersistentSurfaceStratumSyzygy
      liftedParameterCount N (N - 1) 1 componentGeneratorCount
        stratumEquationCount

/-- One actual denominator-localized curve chart at a smooth integral
point of a rational projective curve. -/
structure RelativeRationalCurveChartWitness
    {M N : ℕ} (catalogue : RelativeRationalCurveChartCatalogue M N)
    (baseParameter : Fin M → ℤ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (point : Fin N → ℤ) where
  liftedParameter : Fin catalogue.liftedParameterCount → ℤ
  chartIndex : Fin catalogue.chartCount
  base_specialization : ∀ j,
    liftedParameter (catalogue.baseCoordinate j) = baseParameter j
  onStratum : (catalogue.chart chartIndex).OnStratum liftedParameter
  inDenominatorOpen :
    (catalogue.chart chartIndex).InDenominatorOpen liftedParameter
  componentIdeal_le :
    (catalogue.chart chartIndex).specializedComponentIdeal
        liftedParameter ≤
      Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I)
  denominator_power_clears_componentModel :
    ∀ f ∈ Ideal.map integralDehomogenizeAtZeroHom
        (projectiveIntegralClosureIdeal I),
      ∃ e : ℕ,
        MvPolynomial.C
            (MvPolynomial.eval liftedParameter
              (catalogue.chart chartIndex).parameterDenominator) ^ e * f ∈
          (catalogue.chart chartIndex).specializedComponentIdeal
            liftedParameter
  clearing_nonzero :
    MvPolynomial.eval point
      ((catalogue.chart chartIndex).toRelativePersistentSurfaceChart.specializedClearingPolynomial
        liftedParameter 0) ≠ 0
  jacobian_nonzero :
    MvPolynomial.eval point
      (selectedJacobianDeterminant
        ((catalogue.chart chartIndex).toRelativePersistentSurfaceChart.specializedEquations
          liftedParameter)
        (catalogue.chart chartIndex).toRelativePersistentSurfaceChart.selectedVar) ≠ 0

/-- The curve chart catalogue refines the same fixed component models and
uses a bijective renaming of their enlarged parameter coordinates. -/
structure RelativeRationalCurveSmoothChartRefinement
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (catalogue : RelativeRationalCurveChartCatalogue M N) where
  modelParameterCoordinate :
    Fin models.liftedParameterCount → Fin catalogue.liftedParameterCount
  modelParameterCoordinate_injective :
    Function.Injective modelParameterCoordinate
  modelParameterCoordinate_surjective :
    Function.Surjective modelParameterCoordinate
  baseCoordinate_compatibility : ∀ j,
    modelParameterCoordinate (models.baseCoordinate j) =
      catalogue.baseCoordinate j
  smoothPointCover :
    ∀ (baseParameter : Fin M → ℤ)
      (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (point : Fin N → ℤ),
      ∀ modelWitness :
        RelativeRationalSurfaceComponentModelWitness models baseParameter I,
      I.IsPrime →
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
      (∃ d : ℕ, HasProjectiveDimensionDegree I 1 d) →
      IsSmoothAffineIdealRationalPoint
        (Ideal.map rationalDehomogenizeAtZeroHom I)
        (fun j ↦ (point j : ℚ)) →
      ∃ w : RelativeRationalCurveChartWitness
          catalogue baseParameter I point,
        ∀ j, w.liftedParameter (modelParameterCoordinate j) =
          modelWitness.liftedParameter j

/-- Literal fixed-family coverage of smooth integral points on rational
prime projective curve components. -/
def RelativeRationalCurveChartCatalogue.CoversPrimeCurveSmoothPoints
    {M N : ℕ} (catalogue : RelativeRationalCurveChartCatalogue M N)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1))) : Prop :=
  ∀ (baseParameter : Fin M → ℤ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I ∈ finiteMinimalPrimes
      (finiteEquationIdeal
        (rationalRelativeIntegralFibreEquationFinset family baseParameter)) →
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
    (∃ d : ℕ, HasProjectiveDimensionDegree I 1 d) →
    ∀ point : Fin N → ℤ,
      IsSmoothAffineIdealRationalPoint
        (Ideal.map rationalDehomogenizeAtZeroHom I)
        (fun j ↦ (point j : ℚ)) →
      Nonempty
        (RelativeRationalCurveChartWitness catalogue baseParameter I point)

namespace StandardAG

/-- **Finite-etale spreading of rational prime curve component unions.**

Dimension-one specialization of generic component splitting after finite
etale cover, Galois-stable union descent, generic flatness/reducedness, and
Noetherian induction (Stacks Tags `054V`, `0553`, `052B`, `01UA`). -/
def FiniteEtaleRationalPrimeCurveComponentUnionSpreading : Prop :=
  ∀ (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ)),
    1 ≤ N →
    (∀ parameter, fibreEquations parameter =
      (family.image
        (specializeRelativeIntegralAffinePolynomial parameter)).image
          (MvPolynomial.map (Int.castRingHom ℚ))) →
      ∃ models : RelativeRationalSurfaceComponentModelCatalogue M N,
        models.CoversPrimeCurves fibreEquations

/-- **Finite standard-smooth chart extraction for fixed curve models.**

First stratify the enlarged integral parameter space so that the fixed
component models are flat (generic flatness and Noetherian induction).
Over each flat stratum, the fibrewise smoothness criterion identifies the
smooth points of the qualified one-dimensional prime fibres with the
relative smooth locus.  Quasi-compactness and standard-smooth presentations
(Stacks Tags `0H3Z`, `01V9`, `00TA`) then give finitely many
principal opens with `N-1` equations.  The existing stratum equations and
parameter denominator record the flattening strata, so no new parameter
coordinates are hidden here.  This premise has no height, degree, or
counting conclusion. -/
def FiniteRelativeCurveComponentModelStandardSmoothChartExtraction : Prop :=
  ∀ (M N : ℕ)
    (models : RelativeRationalSurfaceComponentModelCatalogue M N),
    1 ≤ N →
      ∃ catalogue : RelativeRationalCurveChartCatalogue M N,
        Nonempty
          (RelativeRationalCurveSmoothChartRefinement models catalogue)

end StandardAG

/-- Lean-checked assembly of fixed curve component models and their
same-parameter smooth chart refinement. -/
theorem exists_finiteRationalPrimeCurveModelsAndSmoothCharts
    (hComponents :
      StandardAG.FiniteEtaleRationalPrimeCurveComponentUnionSpreading)
    (hSmoothCharts :
      StandardAG.FiniteRelativeCurveComponentModelStandardSmoothChartExtraction)
    (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (hN : 1 ≤ N) :
    ∃ models : RelativeRationalSurfaceComponentModelCatalogue M N,
      ∃ catalogue : RelativeRationalCurveChartCatalogue M N,
        models.CoversPrimeCurves
          (fun parameter ↦
            rationalRelativeIntegralFibreEquationFinset family parameter) ∧
        Nonempty
          (RelativeRationalCurveSmoothChartRefinement models catalogue) := by
  let fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ) :=
    rationalRelativeIntegralFibreEquationFinset family
  have hfibre : ∀ parameter, fibreEquations parameter =
      (family.image
        (specializeRelativeIntegralAffinePolynomial parameter)).image
          (MvPolynomial.map (Int.castRingHom ℚ)) := by
    intro parameter
    rfl
  obtain ⟨models, hmodels⟩ :=
    hComponents M N family fibreEquations hN hfibre
  obtain ⟨catalogue, hrefinement⟩ :=
    hSmoothCharts M N models hN
  exact ⟨models, catalogue, hmodels, hrefinement⟩

/-- Same-parameter refinement transfers the fixed monic model-coordinate
bound to every coordinate of a curve chart witness. -/
theorem RelativeRationalCurveSmoothChartRefinement.chartParameter_natAbs_le
    {M N Y : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {catalogue : RelativeRationalCurveChartCatalogue M N}
    (refinement :
      RelativeRationalCurveSmoothChartRefinement models catalogue)
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (modelWitness :
      RelativeRationalSurfaceComponentModelWitness models baseParameter I)
    (chartWitness :
      RelativeRationalCurveChartWitness catalogue baseParameter I point)
    (hcompatibility : ∀ j,
      chartWitness.liftedParameter (refinement.modelParameterCoordinate j) =
        modelWitness.liftedParameter j)
    (hbase : ∀ j, (baseParameter j).natAbs ≤ Y) :
    ∀ j, (chartWitness.liftedParameter j).natAbs ≤
      models.liftedParameterBound Y := by
  intro j
  obtain ⟨i, hi⟩ := refinement.modelParameterCoordinate_surjective j
  subst j
  rw [hcompatibility i]
  exact modelWitness.liftedParameter_natAbs_le hbase i

/-- The fixed catalogue supplies a curve chart witness at every covered
smooth point. -/
theorem exists_finiteRationalPrimeCurveSmoothChartCatalogue
    (hComponents :
      StandardAG.FiniteEtaleRationalPrimeCurveComponentUnionSpreading)
    (hSmoothCharts :
      StandardAG.FiniteRelativeCurveComponentModelStandardSmoothChartExtraction)
    (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (hN : 1 ≤ N) :
    ∃ catalogue : RelativeRationalCurveChartCatalogue M N,
      catalogue.CoversPrimeCurveSmoothPoints family := by
  let fibreEquations :
      (Fin M → ℤ) → Finset (MvPolynomial (Fin (N + 1)) ℚ) :=
    rationalRelativeIntegralFibreEquationFinset family
  have hfibre : ∀ parameter, fibreEquations parameter =
      (family.image
        (specializeRelativeIntegralAffinePolynomial parameter)).image
          (MvPolynomial.map (Int.castRingHom ℚ)) := by
    intro parameter
    rfl
  obtain ⟨models, hmodels⟩ :=
    hComponents M N family fibreEquations hN hfibre
  obtain ⟨catalogue, ⟨hrefinement⟩⟩ :=
    hSmoothCharts M N models hN
  refine ⟨catalogue, ?_⟩
  intro baseParameter I hminimal hprime hhomogeneous hchart hdimension
    point hsmooth
  obtain ⟨modelWitness⟩ := hmodels baseParameter I hminimal hprime
    hhomogeneous hchart hdimension
  obtain ⟨chartWitness, _hcompatibility⟩ :=
    hrefinement.smoothPointCover baseParameter I point modelWitness hprime
      hhomogeneous hchart hdimension hsmooth
  exact ⟨chartWitness⟩

/-- A curve chart witness gives the explicit nonzero integer and
dimension-one Hilbert--Samuel multiplicity at every prime avoiding it. -/
theorem RelativeRationalCurveChartWitness.multiplicityOne
    {M N : ℕ} (hN : 1 ≤ N)
    {catalogue : RelativeRationalCurveChartCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (w : RelativeRationalCurveChartWitness
      catalogue baseParameter I point)
    (hsmooth : IsSmoothAffineIdealRationalPoint
      (Ideal.map rationalDehomogenizeAtZeroHom I)
      (fun j ↦ (point j : ℚ))) :
    let data := catalogue.chart w.chartIndex
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      (data.denominatorAugmentedChart.specializedEquations
        w.liftedParameter)
      data.denominatorAugmentedChart.selectedVar
      (data.denominatorAugmentedChart.specializedClearingPolynomial
        w.liftedParameter 0) point
    Δ ≠ 0 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (projectiveSpecialFiberIdeal I)
          (fun j ↦ (integralAffineProjectivePoint point j : ZMod p)) 1 1 := by
  obtain ⟨hpointZero, _hsmoothPoint⟩ := hsmooth
  have hpoint : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun j ↦ (point j : ℚ)) f = 0 := by
    intro f hf
    exact hpointZero f hf
  have hcertificate :=
    (catalogue.chart w.chartIndex).specialized_multiplicityOne_of_denominatorModel_dimension
      w.liftedParameter w.onStratum w.inDenominatorOpen I
      w.componentIdeal_le w.denominator_power_clears_componentModel point
      hpoint 0 w.clearing_nonzero w.jacobian_nonzero
  simpa only [show N - (N - 1) = 1 by omega] using hcertificate

/-- Largest certificate exponent of the fixed curve chart catalogue. -/
def RelativeRationalCurveChartCatalogue.certificateHeightExponent
    {M N : ℕ} (catalogue : RelativeRationalCurveChartCatalogue M N)
    (coordinateExponent : ℕ) : ℕ :=
  Finset.univ.sup fun c : Fin catalogue.chartCount ↦
    (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
      coordinateExponent

theorem RelativeRationalCurveChartCatalogue.chart_certificateHeightExponent_le
    {M N : ℕ} (catalogue : RelativeRationalCurveChartCatalogue M N)
    (coordinateExponent : ℕ) (c : Fin catalogue.chartCount) :
    (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
        coordinateExponent ≤
      catalogue.certificateHeightExponent coordinateExponent := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun c : Fin catalogue.chartCount ↦
      (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
        coordinateExponent)
    (Finset.mem_univ c)

/-- Elementary fixed-polynomial certificate bound for one curve chart
witness once its parameter and point coordinates share a common bound. -/
theorem RelativeRationalCurveChartWitness.certificate_natAbs_cast_le_rpow
    {M N coordinateExponent Y : ℕ}
    {catalogue : RelativeRationalCurveChartCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (w : RelativeRationalCurveChartWitness
      catalogue baseParameter I point)
    (hparameter : ∀ j, (w.liftedParameter j).natAbs ≤ Y)
    (hpoint : ∀ j, (point j).natAbs ≤ Y)
    (H : ℝ) (hH : 2 ≤ H)
    (hY : (Y : ℝ) ≤ H ^ coordinateExponent) :
    let data := catalogue.chart w.chartIndex
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      (data.denominatorAugmentedChart.specializedEquations
        w.liftedParameter)
      data.denominatorAugmentedChart.selectedVar
      (data.denominatorAugmentedChart.specializedClearingPolynomial
        w.liftedParameter 0) point
    (Δ.natAbs : ℝ) ≤
      H ^ (catalogue.certificateHeightExponent coordinateExponent : ℝ) := by
  let data := catalogue.chart w.chartIndex
  let X : Finset (Fin N → ℤ) := {point}
  let markOf : (Fin N → ℤ) → Fin 1 := fun _ ↦ 0
  have hpointX : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ Y := by
    intro z hz j
    have hz' : z = point := by
      simpa only [X, Finset.mem_singleton] using hz
    subst z
    exact hpoint j
  have hA :
      (data.denominatorAugmentedChart.certificateHeightExponent
          coordinateExponent : ℝ) ≤
        (catalogue.certificateHeightExponent coordinateExponent : ℝ) := by
    exact_mod_cast
      catalogue.chart_certificateHeightExponent_le coordinateExponent
        w.chartIndex
  have hbound := data.augmentedCertificateSize_for_mark
    w.liftedParameter X markOf hparameter hpointX H
    (catalogue.certificateHeightExponent coordinateExponent : ℝ)
    hH hY hA point (by simp [X])
  simpa only [data, markOf] using hbound

/-- The same-parameter curve refinement plus the monic-root bound yields a
certificate exponent fixed by the two catalogues and input coordinate
exponents. -/
theorem RelativeRationalCurveSmoothChartRefinement.chartCertificate_natAbs_cast_le_rpow
    {M N baseBound pointBound baseCoordinateExponent
      pointCoordinateExponent : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {catalogue : RelativeRationalCurveChartCatalogue M N}
    (refinement :
      RelativeRationalCurveSmoothChartRefinement models catalogue)
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (modelWitness :
      RelativeRationalSurfaceComponentModelWitness models baseParameter I)
    (chartWitness :
      RelativeRationalCurveChartWitness catalogue baseParameter I point)
    (hcompatibility : ∀ j,
      chartWitness.liftedParameter (refinement.modelParameterCoordinate j) =
        modelWitness.liftedParameter j)
    (hbase : ∀ j, (baseParameter j).natAbs ≤ baseBound)
    (hpoint : ∀ j, (point j).natAbs ≤ pointBound)
    (H : NNReal) (hH : 2 ≤ H)
    (hbaseBound : (baseBound : ℝ) ≤
      (H : ℝ) ^ baseCoordinateExponent)
    (hpointBound : (pointBound : ℝ) ≤
      (H : ℝ) ^ pointCoordinateExponent) :
    let data := catalogue.chart chartWitness.chartIndex
    let Δ : ℤ := integralSelectedJacobianChartCertificate
      (data.denominatorAugmentedChart.specializedEquations
        chartWitness.liftedParameter)
      data.denominatorAugmentedChart.selectedVar
      (data.denominatorAugmentedChart.specializedClearingPolynomial
        chartWitness.liftedParameter 0) point
    (Δ.natAbs : ℝ) ≤
      (H : ℝ) ^
        (catalogue.certificateHeightExponent
          (models.jointChartCoordinateHeightExponent
            baseCoordinateExponent pointCoordinateExponent) : ℝ) := by
  let Y := models.jointChartCoordinateBound baseBound pointBound
  let E := models.jointChartCoordinateHeightExponent
    baseCoordinateExponent pointCoordinateExponent
  have hparameter : ∀ j,
      (chartWitness.liftedParameter j).natAbs ≤ Y := by
    intro j
    exact (refinement.chartParameter_natAbs_le modelWitness chartWitness
      hcompatibility hbase j).trans (Nat.le_max_left _ _)
  have hpoint' : ∀ j, (point j).natAbs ≤ Y := by
    intro j
    exact (hpoint j).trans (Nat.le_max_right _ _)
  have hHreal : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ (H : ℝ) := by linarith
  have hmodel := models.liftedParameterBound_cast_le_heightPower
    H hH hbaseBound
  have hmodelReal : (models.liftedParameterBound baseBound : ℝ) ≤
      (H : ℝ) ^ models.liftedParameterHeightExponent
        baseCoordinateExponent := by
    exact_mod_cast hmodel
  have hmodelE : (models.liftedParameterBound baseBound : ℝ) ≤
      (H : ℝ) ^ E := by
    calc
      (models.liftedParameterBound baseBound : ℝ) ≤
          (H : ℝ) ^ models.liftedParameterHeightExponent
            baseCoordinateExponent := hmodelReal
      _ ≤ (H : ℝ) ^ models.liftedParameterHeightExponent
              baseCoordinateExponent *
            (H : ℝ) ^ pointCoordinateExponent := by
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hHone)
      _ = (H : ℝ) ^ E := by
        simp only [E,
          RelativeRationalSurfaceComponentModelCatalogue.jointChartCoordinateHeightExponent,
          pow_add]
  have hpointE : (pointBound : ℝ) ≤ (H : ℝ) ^ E := by
    calc
      (pointBound : ℝ) ≤ (H : ℝ) ^ pointCoordinateExponent := hpointBound
      _ ≤ (H : ℝ) ^ models.liftedParameterHeightExponent
              baseCoordinateExponent *
            (H : ℝ) ^ pointCoordinateExponent := by
        exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hHone)
      _ = (H : ℝ) ^ E := by
        simp only [E,
          RelativeRationalSurfaceComponentModelCatalogue.jointChartCoordinateHeightExponent,
          pow_add]
  have hY : (Y : ℝ) ≤ (H : ℝ) ^ E := by
    dsimp only [Y,
      RelativeRationalSurfaceComponentModelCatalogue.jointChartCoordinateBound]
    norm_num only [Nat.cast_max]
    exact max_le hmodelE hpointE
  exact chartWitness.certificate_natAbs_cast_le_rpow hparameter hpoint'
    (H : ℝ) hHreal hY

end

end TranslatedDepthSeven
