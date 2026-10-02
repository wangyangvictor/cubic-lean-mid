import CubicTenVariables.StandardBertiniBoundarySlicing
import CubicTenVariables.GoodSurfaceFibreAffineFourStaticProjection
import TranslatedDepthSeven.BoundedSimultaneousAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.BoundedSimultaneousAffineChartProjectionSaturatedBoundaryInternal

/-!
# Downstream adapter for simultaneous source--boundary projections

This file fixes the interface between the standard Bertini boundary
certificate and the internal simultaneous source--boundary projection
theorem.  It specializes the enlarged finite matrix menu to projective
closures of affine threefolds in ten variables and derives the static
four-variable models consumed by the counting argument.

`SimultaneousAffineFourProjectionMenuProvider` records the exact internal API
boundary.  It is implemented below by the bounded simultaneous affine-chart
projection theorem, so it is not an additional literature assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace CubicTenVariables.GoodSurfaceFibreSimultaneousBoundaryProjection

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSlicingReduction
open ExactDegreeRationalSurfaceSlicing
open StandardBertiniBoundarySlicing
open GoodSurfaceFibreAffineFourStaticProjection

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The enlarged fixed menu specialized to projections of affine
threefolds in ten variables. -/
def affineFourSimultaneousProjectionMenu (degreeBound : ℕ) :
    Finset (Matrix (Fin 5) (Fin 11) ℤ) :=
  boundedIntegralSimultaneousAffineProjectionMatrices 10 3 degreeBound

/-- Uniform coefficient bound of the enlarged simultaneous menu. -/
def affineFourSimultaneousProjectionCoefficientBound
    (degreeBound : ℕ) : ℕ :=
  max 1 ((affineFourSimultaneousProjectionMenu degreeBound).sup fun A ↦
    integerProjectionCoefficientBound (affineChartProjectionTailMatrix A))

theorem affineFourSimultaneousProjectionCoefficientBound_pos
    (degreeBound : ℕ) :
    1 ≤ affineFourSimultaneousProjectionCoefficientBound degreeBound :=
  Nat.le_max_left _ _

theorem integerProjectionCoefficientBound_tail_le_simultaneousMenu
    {degreeBound : ℕ} {A : Matrix (Fin 5) (Fin 11) ℤ}
    (hA : A ∈ affineFourSimultaneousProjectionMenu degreeBound) :
    integerProjectionCoefficientBound (affineChartProjectionTailMatrix A) ≤
      affineFourSimultaneousProjectionCoefficientBound degreeBound := by
  exact (Finset.le_sup
    (f := fun B ↦ integerProjectionCoefficientBound
      (affineChartProjectionTailMatrix B)) hA).trans (Nat.le_max_right _ _)

/-- Type-valued output of one simultaneous source--boundary projection.
Keeping the witness in `Nonempty` allows the downstream static model to be
chosen without eliminating an existential proposition into data. -/
structure SimultaneousSourceBoundaryMenuProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ)) (degree : ℕ) where
  source_prime : J.IsPrime
  boundary_prime :
    (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)).IsPrime
  matrix : Matrix (Fin 5) (Fin 11) ℤ
  matrix_mem : matrix ∈ affineFourSimultaneousProjectionMenu degree
  sourceEquation : MvPolynomial (Fin 5) ℚ
  source_projection :
    StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
      (affineIdealProjectiveClosure_isPrime J source_prime)
      matrix sourceEquation
  boundaryEquation : MvPolynomial (Fin 4) ℚ
  boundary_projection :
    StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree)
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J))
      boundary_prime
      (affineChartProjectionBoundaryMatrix
        (matrix.map (Int.castRingHom ℚ))) boundaryEquation

/-- Exact output signature needed from the internal simultaneous projection
theorem.  The source is the projective closure of `J`; the second projection
uses the tail of the same integral matrix on its boundary. -/
def SimultaneousAffineFourProjectionMenuProvider : Prop :=
  ∀ (degree : ℕ) (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (_hJ : J.IsPrime)
    (_hJdegree : HasAffineDimensionDegree J 3 degree)
    (_hboundaryPrime :
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)).IsPrime)
    (_hboundaryDegree : HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)) 2 degree),
    Nonempty (SimultaneousSourceBoundaryMenuProjection J degree)

/-- The internal simultaneous affine-chart projection theorem implements
the provider interface.  Projective closure supplies the homogeneous source,
and the source and boundary are projected by one literal matrix from the
enlarged finite menu. -/
theorem simultaneousAffineFourProjectionMenuProvider :
    SimultaneousAffineFourProjectionMenuProvider := by
  intro degree J hJ hJdegree hboundaryPrime hboundaryDegree
  have hclosurePrime : (affineIdealProjectiveClosure J).IsPrime :=
    affineIdealProjectiveClosure_isPrime J hJ
  obtain ⟨A, hA, G, H, hsource, hboundary, _hsourceDegree,
      _hboundaryImageDegree⟩ :=
    exists_bounded_simultaneousAffineChartProjection
      (N := 9) (r := 2) (degreeBound := degree)
      (affineIdealProjectiveClosure J)
      hclosurePrime
      (affineIdealProjectiveClosure_isHomogeneous J)
      (affineIdealProjectiveClosure_X_zero_not_mem J hJ)
      (affineIdealProjectiveClosure_hasProjectiveDimensionDegree J hJdegree)
      hboundaryPrime hboundaryDegree le_rfl
  exact ⟨{
    source_prime := hJ
    boundary_prime := hboundaryPrime
    matrix := A
    matrix_mem := hA
    sourceEquation := G
    source_projection := hsource
    boundaryEquation := H
    boundary_projection := hboundary
  }⟩

/-! ## Correct saturated-boundary provider -/

/-- Type-valued output when the boundary is a prime homogeneous
saturation containing the literal boundary at infinity. -/
structure SimultaneousSourceSaturatedBoundaryMenuProjection
    (J B : Ideal (MvPolynomial (Fin 10) ℚ)) (degree : ℕ) where
  source_prime : J.IsPrime
  boundary_prime : B.IsPrime
  matrix : Matrix (Fin 5) (Fin 11) ℤ
  matrix_mem : matrix ∈ affineFourSimultaneousProjectionMenu degree
  sourceEquation : MvPolynomial (Fin 5) ℚ
  source_projection :
    StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) (affineIdealProjectiveClosure J)
      (affineIdealProjectiveClosure_isPrime J source_prime)
      matrix sourceEquation
  boundaryEquation : MvPolynomial (Fin 4) ℚ
  boundary_projection :
    StandardAG.IsHomogeneousFiniteBirationalLinearProjection
      (degree := degree) B boundary_prime
      (affineChartProjectionBoundaryMatrix
        (matrix.map (Int.castRingHom ℚ))) boundaryEquation

/-- Exact source--saturated-boundary interface used downstream. -/
def SimultaneousAffineFourSaturatedBoundaryMenuProvider : Prop :=
  ∀ (degree : ℕ) (J B : Ideal (MvPolynomial (Fin 10) ℚ))
    (_hJ : J.IsPrime)
    (_hJdegree : HasAffineDimensionDegree J 3 degree)
    (_hboundaryLe : projectiveBoundaryIdeal
      (affineIdealProjectiveClosure J) ≤ B)
    (_hBprime : B.IsPrime)
    (_hBhomogeneous :
      B.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (_hBdegree : HasProjectiveDimensionDegree B 2 degree),
    Nonempty
      (SimultaneousSourceSaturatedBoundaryMenuProjection J B degree)

/-- The internal BHB--Marmon construction implements the saturated
provider.  No Bertini or counting theorem is used here. -/
theorem simultaneousAffineFourSaturatedBoundaryMenuProvider :
    SimultaneousAffineFourSaturatedBoundaryMenuProvider := by
  intro degree J B hJ hJdegree hboundaryLe hBprime hBhom hBdegree
  obtain ⟨A, hA, G, H, hsource, hboundary, _hsourceDegree,
      _hboundaryImageDegree⟩ :=
    exists_bounded_simultaneousAffineChartProjection_saturatedBoundary
      (N := 9) (r := 2) (degreeBound := degree)
      (affineIdealProjectiveClosure J) B hboundaryLe
      (affineIdealProjectiveClosure_isPrime J hJ)
      (affineIdealProjectiveClosure_isHomogeneous J)
      (affineIdealProjectiveClosure_X_zero_not_mem J hJ)
      (affineIdealProjectiveClosure_hasProjectiveDimensionDegree J hJdegree)
      hBprime hBhom hBdegree le_rfl
  exact ⟨{
    source_prime := hJ
    boundary_prime := hBprime
    matrix := A
    matrix_mem := hA
    sourceEquation := G
    source_projection := hsource
    boundaryEquation := H
    boundary_projection := hboundary
  }⟩

/-- One fixed geometrically integral saturated boundary, together with
exact degree and boundary containment for every good affine fibre, gives
the complete static projection family. -/
def staticModelsOfSaturatedBoundary
    (provider : SimultaneousAffineFourSaturatedBoundaryMenuProvider)
    {r d : ℕ}
    {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I)
    (B : Ideal (MvPolynomial (Fin 10) ℚ))
    (hBprime : B.IsPrime)
    (hBgeometric : GeometricallyPrimeMvPolynomialIdeal B)
    (hBhom : B.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hBdegree : HasProjectiveDimensionDegree B 2 d)
    (hgoodDegree : ∀ (y : Fin (r - 2) → ℚ),
      eval y cert.discriminant ≠ 0 →
        HasAffineDimensionDegree
          (rationalSliceIdeal I cert.matrix y) 3 d)
    (hboundaryLe : ∀ (y : Fin (r - 2) → ℚ),
      eval y cert.discriminant ≠ 0 →
        projectiveBoundaryIdeal
          (affineIdealProjectiveClosure
            (rationalSliceIdeal I cert.matrix y)) ≤ B)
    (hd : 4 ≤ d) :
    GoodFibreStaticAffineFourProjectionModels I cert where
  degreeBound := d
  coefficientBound := affineFourSimultaneousProjectionCoefficientBound d
  fibreBound := d
  coefficientBound_pos := affineFourSimultaneousProjectionCoefficientBound_pos d
  models y hy := by
    let J := rationalSliceIdeal I cert.matrix y
    have hJdegree : HasAffineDimensionDegree J 3 d := hgoodDegree y hy
    let witness := Classical.choice
      (provider d J B hJdegree.1 hJdegree (hboundaryLe y hy)
        hBprime hBhom hBdegree)
    let data : BoundaryIrreducibleAffineFourProjection J d :=
      BoundaryIrreducibleAffineFourProjection.ofSimultaneousSaturatedBoundaryProjection
          J d witness.source_prime B (hboundaryLe y hy)
          witness.boundary_prime hBgeometric witness.matrix
          witness.sourceEquation witness.source_projection
          witness.boundaryEquation witness.boundary_projection
    exact data.toStatic hd le_rfl
      (integerProjectionCoefficientBound_tail_le_simultaneousMenu
        witness.matrix_mem)
      le_rfl

/-- A boundary-good projection chosen from the enlarged simultaneous menu. -/
structure SimultaneousMenuBoundaryAffineFourProjection
    (J : Ideal (MvPolynomial (Fin 10) ℚ)) (degree : ℕ) where
  data : BoundaryIrreducibleAffineFourProjection J degree
  matrix_mem : data.matrix ∈ affineFourSimultaneousProjectionMenu degree

/-- An enlarged-menu witness gives the same static model as before, with
its coefficient bound computed from the enlarged menu. -/
def SimultaneousMenuBoundaryAffineFourProjection.toStatic
    {J : Ideal (MvPolynomial (Fin 10) ℚ)} {degree : ℕ}
    (witness : SimultaneousMenuBoundaryAffineFourProjection J degree)
    (hdegree4 : 4 ≤ degree) :
    StaticAffineFourHypersurfaceProjectionModel J degree
      (affineFourSimultaneousProjectionCoefficientBound degree) degree :=
  witness.data.toStatic hdegree4 le_rfl
    (integerProjectionCoefficientBound_tail_le_simultaneousMenu
      witness.matrix_mem)
    le_rfl

/-- Apply the simultaneous provider to every good fibre of one Bertini
boundary certificate.  The boundary hypotheses are transported from the
single fixed boundary by the closure and boundary-independence theorems. -/
def staticModelsOfBertiniBoundaryCertificate
    (provider : SimultaneousAffineFourProjectionMenuProvider)
    {r d : ℕ} (hr : r = 4 ∨ r = 5)
    {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I r d)
    (hd : 4 ≤ d)
    (cert : RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I) :
    GoodFibreStaticAffineFourProjectionModels I cert.slicing where
  degreeBound := d
  coefficientBound := affineFourSimultaneousProjectionCoefficientBound d
  fibreBound := d
  coefficientBound_pos := affineFourSimultaneousProjectionCoefficientBound_pos d
  models y hy := by
    let J := rationalSliceIdeal I cert.slicing.matrix y
    have hJdegree : HasAffineDimensionDegree J 3 d :=
      good_fibre_hasAffineDimensionDegree_exact hr I hIprime hIhom hIdegree
        cert.slicing cert.primeFlags y hy
    have hboundaryPrime :
        (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)).IsPrime :=
      good_fibre_projectiveBoundary_isPrime hIprime cert y hy
    have hboundaryGeometric : GeometricallyPrimeMvPolynomialIdeal
        (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)) :=
      good_fibre_projectiveBoundary_geometricallyPrime hIprime cert y hy
    have hboundaryDegree : HasProjectiveDimensionDegree
        (projectiveBoundaryIdeal (affineIdealProjectiveClosure J)) 2 d :=
      good_fibre_projectiveBoundary_dimension_degree
        hr hIprime hIhom hIdegree cert y hy
    let witness := Classical.choice
      (provider d J hJdegree.1 hJdegree hboundaryPrime hboundaryDegree)
    let data : BoundaryIrreducibleAffineFourProjection J d :=
      BoundaryIrreducibleAffineFourProjection.ofSimultaneousBoundaryProjection
        J d witness.source_prime witness.matrix witness.sourceEquation
        witness.source_projection witness.boundary_prime hboundaryGeometric
        witness.boundaryEquation witness.boundary_projection
    exact (SimultaneousMenuBoundaryAffineFourProjection.mk data
      witness.matrix_mem).toStatic hd

/-- Standard Bertini boundary existence plus the internal simultaneous-menu
provider supplies the static projection premise used downstream. -/
theorem staticAffineFourProjectionModelsN10_of_bertiniBoundary
    (provider : SimultaneousAffineFourProjectionMenuProvider)
    (bertini : StandardAGBertiniBoundarySlicingN10) :
    StaticAffineFourProjectionModelsN10 := by
  intro I r d hr hprime hgeometric hhom hdegree hd
  obtain ⟨cert⟩ := bertini I r d hr hprime hgeometric hhom hdegree hd
  exact ⟨cert.slicing, ⟨staticModelsOfBertiniBoundaryCertificate
    provider hr hprime hhom hdegree hd cert⟩⟩

/-- The standard Bertini boundary premise alone now supplies the static
projection family: the simultaneous provider is a proved internal theorem. -/
theorem staticAffineFourProjectionModelsN10_of_standardBertiniBoundary
    (bertini : StandardAGBertiniBoundarySlicingN10) :
    StaticAffineFourProjectionModelsN10 :=
  staticAffineFourProjectionModelsN10_of_bertiniBoundary
    simultaneousAffineFourProjectionMenuProvider bertini

end CubicTenVariables.GoodSurfaceFibreSimultaneousBoundaryProjection
