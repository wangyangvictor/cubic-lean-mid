import TranslatedDepthSeven.RelativePersistentStratumSyzygy
import TranslatedDepthSeven.FiniteRelativeRationalComponentModels
import TranslatedDepthSeven.RankSevenPersistentSurfaceSmoothDevissage

/-!
# Finite relative charts for rational surface components

This file gives the exact qualitative relative-algebraic-geometry input
needed by the persistent-surface argument.  It deliberately does **not**
assert that multiplying once by a specialized denominator produces the full
contracted ideal over `\mathbb Z`.  Such an assertion does not follow from
localization and is false in general.  Instead every chart records the exact
pointwise denominator-power condition consumed by
`RelativePersistentSurfaceStratumSyzygy.specialized_multiplicityOne_of_denominatorModel`.

The standard construction is as follows.  Over the generic point of an
integral parameter stratum, the geometric components split after a finite
etale cover.  This is the content used from the Stacks Project, Lemma
37.24.8 (Tag `054V`) and Section 37.27, in particular Lemma 37.27.6
(Tag `055A`).  A rational irreducible component is the reduced union of a
Galois-stable subset of the geometric components.  All such subsets form a
finite etale cover (equivalently, the Weil restriction of the two-point
scheme along the splitting cover).  On that cover one forms the reduced
unions, and then shrinks so that flat base change commutes with their
formation and their fibres are geometrically reduced with the asserted
support.  The image of the omitted locus is closed because the cover is
finite.  Noetherian induction on that closed complement gives finitely many
parameter strata.

Apply finite flat stratification (Tag `0H3Z`) before passing from fibrewise
smoothness to relative smoothness (Tag `01V9`).  The relative smooth locus
of each resulting union is quasi-compact.  The
standard-smooth presentation theorems (Stacks Tags `00TA`, `00TS`, and
`00TT`) therefore give finitely many affine principal opens in the original
ambient affine space, each with `N-2` equations and a nonzero Jacobian
minor.  This refinement introduces no new parameter coordinates: it merely
duplicates the finitely many component models to record finitely many
principal opens.  Noetherianity supplies finite syzygies for the two
localized ideal containments.  After specialization, equality away from the
evaluated base denominator has precisely the pointwise-power integral form
stored below.  Noetherianity supplies a common exponent only after a fibre
is fixed; that exponent is used internally and is not part of the catalogue
or its height estimate.

Thus `FiniteRationalPrimeSurfaceSmoothChartSpreading` is a narrow derived
corollary of the cited standard results.  It is stated separately from all
height estimates.  In particular it contains no point count, surface count,
degree bound, coefficient bound, or conclusion from Salberger or Pila.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance effectiveFixedRelativeSurfaceCoverPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Rational equations obtained by specializing one fixed integral relative
family and extending coefficients to `\mathbb Q`. -/
def rationalRelativeIntegralFibreEquationFinset
    {M N : ℕ}
    (family : Finset (RelativeIntegralAffinePolynomial M N))
    (parameter : Fin M → ℤ) :
    Finset (MvPolynomial (Fin N) ℚ) :=
  (family.image
      (specializeRelativeIntegralAffinePolynomial parameter)).image
    (MvPolynomial.map (Int.castRingHom ℚ))

/-- A finite catalogue of integral relative surface charts.  The first `M`
base parameters occur at the displayed coordinates of one common enlarged
parameter vector.  Auxiliary coordinates encode finite-cover points after
homogenization.  All numerical fields are part of one fixed finite object;
none is selected after a fibre or a point is given. -/
structure RelativeRationalSurfaceChartCatalogue (M N : ℕ) where
  liftedParameterCount : ℕ
  baseCoordinate : Fin M → Fin liftedParameterCount
  baseCoordinate_injective : Function.Injective baseCoordinate
  chartCount : ℕ
  componentGeneratorCount : ℕ
  stratumEquationCount : ℕ
  chart : Fin chartCount →
    RelativePersistentSurfaceStratumSyzygy
      liftedParameterCount N (N - 2) 1 componentGeneratorCount
        stratumEquationCount

/-- The actual denominator-localized chart data for one rational prime
component and one smooth integral point.  The ideal on the right of the two
containments is the literal contracted integral affine model of `I`.

The containment and pointwise-power condition, rather than equality before
localization, are the
important integral formulation.  They say that the displayed specialized
generator ideal agrees with the contracted model after the evaluated
parameter denominator is inverted. -/
structure RelativeRationalSurfaceChartWitness
    {M N : ℕ} (catalogue : RelativeRationalSurfaceChartCatalogue M N)
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

/-- A finite smooth-chart catalogue refines a finite component-model
catalogue when it uses exactly the same enlarged parameter coordinates and
every smooth point represented by a component-model witness receives an
actual chart witness.  Standard-smooth principal opens require more chart
indices, not more finite-cover coordinates. -/
structure RelativeRationalSurfaceSmoothChartRefinement
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (catalogue : RelativeRationalSurfaceChartCatalogue M N) where
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
      (∃ d : ℕ, HasProjectiveDimensionDegree I 2 d) →
      IsSmoothAffineIdealRationalPoint
        (Ideal.map rationalDehomogenizeAtZeroHom I)
        (fun j ↦ (point j : ℚ)) →
      ∃ w : RelativeRationalSurfaceChartWitness
          catalogue baseParameter I point,
        ∀ j, w.liftedParameter (modelParameterCoordinate j) =
          modelWitness.liftedParameter j

/-- Literal coverage property for one fixed projective equation family.
Every rational prime surface component of every integral fibre, and every
smooth integral point on its standard affine chart, is represented by one
member of the fixed catalogue. -/
def RelativeRationalSurfaceChartCatalogue.CoversPrimeSurfaceSmoothPoints
    {M N : ℕ} (catalogue : RelativeRationalSurfaceChartCatalogue M N)
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
    (∃ d : ℕ, HasProjectiveDimensionDegree I 2 d) →
    ∀ point : Fin N → ℤ,
      IsSmoothAffineIdealRationalPoint
        (Ideal.map rationalDehomogenizeAtZeroHom I)
        (fun j ↦ (point j : ℚ)) →
      Nonempty
        (RelativeRationalSurfaceChartWitness catalogue baseParameter I point)

namespace StandardAG

/-- **Finite standard-smooth chart extraction from fixed relative models.**

For a fixed finite catalogue of denominator-localized relative component
models, first apply generic flatness and Noetherian induction to obtain a
finite flat stratification of the base.  On each stratum, fibrewise
smoothness agrees with relative smoothness, and quasi-compactness of the
relative smooth locus gives a finite catalogue of standard-smooth
principal-open charts.  The stratum equations and denominator opens already
present in the catalogue record this finite stratification.  The conclusion
records a bijection between the old and new parameter coordinates; only the
finite chart index is enlarged.

This is the standard-smooth/open-cover half of the construction only.  It
contains no component-existence assertion and no height or counting
conclusion. -/
def FiniteRelativeComponentModelStandardSmoothChartExtraction : Prop :=
  ∀ (M N : ℕ)
    (models : RelativeRationalSurfaceComponentModelCatalogue M N),
    2 ≤ N →
      ∃ catalogue : RelativeRationalSurfaceChartCatalogue M N,
        Nonempty
          (RelativeRationalSurfaceSmoothChartRefinement models catalogue)

end StandardAG

/-- Lean-checked assembly retaining both the component models and their
same-parameter smooth refinement.  This is the form needed for transferring
the internally proved monic-coordinate height bound to chart certificates. -/
theorem exists_finiteRationalPrimeSurfaceModelsAndSmoothCharts
    (hComponents :
      StandardAG.FiniteEtaleRationalPrimeComponentUnionSpreading)
    (hSmoothCharts :
      StandardAG.FiniteRelativeComponentModelStandardSmoothChartExtraction)
    (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (hN : 2 ≤ N) :
    ∃ models : RelativeRationalSurfaceComponentModelCatalogue M N,
      ∃ catalogue : RelativeRationalSurfaceChartCatalogue M N,
        models.CoversPrimeSurfaces
          (fun parameter ↦
            rationalRelativeIntegralFibreEquationFinset family parameter) ∧
        Nonempty
          (RelativeRationalSurfaceSmoothChartRefinement models catalogue) := by
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

/-- A same-parameter smooth refinement transfers the fixed model-coordinate
bound to every coordinate used by its chart witness. -/
theorem RelativeRationalSurfaceSmoothChartRefinement.chartParameter_natAbs_le
    {M N Y : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {catalogue : RelativeRationalSurfaceChartCatalogue M N}
    (refinement :
      RelativeRationalSurfaceSmoothChartRefinement models catalogue)
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (modelWitness :
      RelativeRationalSurfaceComponentModelWitness models baseParameter I)
    (chartWitness :
      RelativeRationalSurfaceChartWitness catalogue baseParameter I point)
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

/-- The desired finite smooth catalogue follows formally from the two
separate standard inputs: finite-etale rational component-union spreading,
and finite standard-smooth chart extraction for those fixed models.  This
theorem is the Lean-checked assembly; the desired conclusion is not itself
introduced as an additional external premise. -/
theorem exists_finiteRationalPrimeSurfaceSmoothChartCatalogue
    (hComponents :
      StandardAG.FiniteEtaleRationalPrimeComponentUnionSpreading)
    (hSmoothCharts :
      StandardAG.FiniteRelativeComponentModelStandardSmoothChartExtraction)
    (M N : ℕ)
    (family : Finset (RelativeIntegralAffinePolynomial M (N + 1)))
    (hN : 2 ≤ N) :
    ∃ catalogue : RelativeRationalSurfaceChartCatalogue M N,
      catalogue.CoversPrimeSurfaceSmoothPoints family := by
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
  have hminimal' : I ∈ finiteMinimalPrimes
      (finiteEquationIdeal (fibreEquations baseParameter)) := by
    exact hminimal
  obtain ⟨modelWitness⟩ := hmodels baseParameter I hminimal' hprime
    hhomogeneous hchart hdimension
  obtain ⟨chartWitness, _hcompatibility⟩ :=
    hrefinement.smoothPointCover baseParameter I point modelWitness
      hprime hhomogeneous hchart hdimension hsmooth
  exact ⟨chartWitness⟩

/-- A qualitative relative chart produces the exact nonzero integer used
for multiplicity one in every residue characteristic outside its prime
divisors.  This theorem is entirely internal: the potentially delicate
integral-model issue is handled by the witness's two denominator-localized
conditions. -/
theorem RelativeRationalSurfaceChartWitness.multiplicityOne
    {M N : ℕ} (hN : 2 ≤ N)
    {catalogue : RelativeRationalSurfaceChartCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (w : RelativeRationalSurfaceChartWitness
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
          (fun j ↦ (integralAffineProjectivePoint point j : ZMod p)) 2 1 := by
  obtain ⟨hpointZero, _hsmoothPoint⟩ := hsmooth
  have hpoint : ∀ f ∈ Ideal.map rationalDehomogenizeAtZeroHom I,
      MvPolynomial.eval (fun j ↦ (point j : ℚ)) f = 0 := by
    intro f hf
    exact hpointZero f hf
  exact (catalogue.chart w.chartIndex).specialized_multiplicityOne_of_denominatorModel hN
      w.liftedParameter w.onStratum w.inDenominatorOpen I
      w.componentIdeal_le w.denominator_power_clears_componentModel point
      hpoint 0 w.clearing_nonzero w.jacobian_nonzero

/-- The largest certificate-height exponent in one fixed finite catalogue.
It is selected from the catalogue before any fibre, point, or epsilon. -/
def RelativeRationalSurfaceChartCatalogue.certificateHeightExponent
    {M N : ℕ} (catalogue : RelativeRationalSurfaceChartCatalogue M N)
    (coordinateExponent : ℕ) : ℕ :=
  Finset.univ.sup fun c : Fin catalogue.chartCount ↦
    (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
      coordinateExponent

theorem RelativeRationalSurfaceChartCatalogue.chart_certificateHeightExponent_le
    {M N : ℕ} (catalogue : RelativeRationalSurfaceChartCatalogue M N)
    (coordinateExponent : ℕ) (c : Fin catalogue.chartCount) :
    (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
        coordinateExponent ≤
      catalogue.certificateHeightExponent coordinateExponent := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun c : Fin catalogue.chartCount ↦
      (catalogue.chart c).denominatorAugmentedChart.certificateHeightExponent
        coordinateExponent)
    (Finset.mem_univ c)

/-- Once the joint integral parameter vector and the affine point have a
common power bound, the exceptional integer attached to any chart in the
catalogue has one fixed power bound.  This is the elementary height step;
it uses no relative component theorem. -/
theorem RelativeRationalSurfaceChartWitness.certificate_natAbs_cast_le_rpow
    {M N coordinateExponent Y : ℕ}
    {catalogue : RelativeRationalSurfaceChartCatalogue M N}
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (w : RelativeRationalSurfaceChartWitness
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
    have hz' : z = point := by simpa only [X, Finset.mem_singleton] using hz
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

/-- One natural-number bound controlling both the auxiliary finite-cover
coordinates and the affine coordinates of a marked point. -/
def RelativeRationalSurfaceComponentModelCatalogue.jointChartCoordinateBound
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (baseBound pointBound : ℕ) : ℕ :=
  max (models.liftedParameterBound baseBound) pointBound

/-- A fixed exponent absorbing the two parts of the preceding joint bound.
It is defined from the finite catalogue and the two already chosen input
exponents, hence before any fibre, point, prime, or epsilon. -/
def RelativeRationalSurfaceComponentModelCatalogue.jointChartCoordinateHeightExponent
    {M N : ℕ}
    (models : RelativeRationalSurfaceComponentModelCatalogue M N)
    (baseCoordinateExponent pointCoordinateExponent : ℕ) : ℕ :=
  models.liftedParameterHeightExponent baseCoordinateExponent +
    pointCoordinateExponent

/-- The same-parameter refinement and the internally proved monic-root
bound give a fixed-power estimate for the literal Jacobian certificate.
This is dimension-independent arithmetic: it uses only the finite model
coordinates, the fixed chart polynomials, and the displayed point box. -/
theorem RelativeRationalSurfaceSmoothChartRefinement.chartCertificate_natAbs_cast_le_rpow
    {M N baseBound pointBound baseCoordinateExponent
      pointCoordinateExponent : ℕ}
    {models : RelativeRationalSurfaceComponentModelCatalogue M N}
    {catalogue : RelativeRationalSurfaceChartCatalogue M N}
    (refinement :
      RelativeRationalSurfaceSmoothChartRefinement models catalogue)
    {baseParameter : Fin M → ℤ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    {point : Fin N → ℤ}
    (modelWitness :
      RelativeRationalSurfaceComponentModelWitness models baseParameter I)
    (chartWitness :
      RelativeRationalSurfaceChartWitness catalogue baseParameter I point)
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
