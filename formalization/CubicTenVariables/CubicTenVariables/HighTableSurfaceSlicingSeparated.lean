import CubicTenVariables.MicrolocalPromotionTable
import CubicTenVariables.MicrolocalRationalPartitionSurfaceSlicing

/-!
# Constructing the high surface-slicing table from separated inputs

The previous `HighTableSurfaceSlicing` boundary packages two mathematically
different assertions: existence of rational surface slices, and a uniform
progression estimate on their good fibres.  This file separates them.

The algebraic-geometric input below returns only a concrete
`RationalSurfaceSlicingCertificate`.  In particular it contains no point
count.  The analytic input is exactly `GoodSurfaceFibreProgressionEstimate`
for a supplied certificate.  `MicrolocalPromotionTable.exists_table` then
constructs the actual high-row tables, and the two inputs are combined only
on their finitely many concrete components.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace CubicTenVariables.HighTableSurfaceSlicingSeparated

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open PolynomialExponentialFamily
open FixedConeSurfaceSlicingReduction
open ConeComponentSurfaceSlicingEndpoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard-algebraic-geometry input in precisely the ambient space and
dimension range used by the two high rows of the ten-variable argument.

Starting from a homogeneous geometrically integral projective variety of
dimension `r = 4` or `r = 5` and degree `d ≥ 4`, it produces the literal
rational matrix, discriminant, exceptional locus, and geometrically integral
surface fibres recorded by `RationalSurfaceSlicingCertificate`.

This is deliberately an existence proposition rather than an axiom or an
asserted theorem.  It contains no finite-field or integral point-count
estimate.

The closest precise references for its standard ingredients are Jouanolou,
*Théorèmes de Bertini et Applications*, Theorem 6.3(4), as reproduced in the
Stacks Project, Lemma 37.32.3 (Tag 0G4F), for geometric irreducibility of a
general linear section; Stacks Lemmas 37.27.5 (Tag 0559) and 37.26.4
(Tag 0578) for spreading geometric irreducibility and reducedness from the
generic fibre to a principal open; Stacks Lemma 33.6.3 (Tag 035U) for
geometric reducedness in characteristic zero; and generic flatness,
Stacks Proposition 29.28.1 (Tag 052A).  The degree bound is the usual
degree preservation for proper linear sections (Bézout, Hartshorne,
*Algebraic Geometry*, Theorem I.7.7, specialized to a hyperplane).  These references cover the
mathematical ingredients, but no single cited theorem states the entire
coordinate-ring package below verbatim; the rational choice of one matrix,
the homogeneous exceptional ideal, and the conversion to the local
`HasAffineDimensionDegree` predicate therefore remain explicitly unproved. -/
def StandardAGRationalSurfaceSlicingCertificateExistenceN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) →
    Published.HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    Nonempty (RationalSurfaceSlicingCertificate (r := r) (d := d) I)

/-- The remaining analytic input, restricted to the actual dimensions of the
ten-variable high rows.  Its argument is an already constructed, literal
surface-slicing certificate; consequently no slicing existence or projective
geometry is hidden in this proposition. -/
def GoodSurfaceFibreProgressionEstimatesN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    4 ≤ d →
    ∀ cert : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      GoodSurfaceFibreProgressionEstimate I cert

/-- Separated AG existence and good-fibre counting inputs give the exact
high-component datum consumed by the existing surface-slicing endpoint. -/
theorem highComponentSurfaceSlicingData_of_separated_inputs
    (slicingAG : StandardAGRationalSurfaceSlicingCertificateExistenceN10)
    (goodSurface : GoodSurfaceFibreProgressionEstimatesN10)
    {r : ℕ} (hr : r = 4 ∨ r = 5)
    (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) :
    HighComponentSurfaceSlicingData r I := by
  intro d hprime hgeometric hdegree hd
  obtain ⟨cert⟩ := slicingAG I r d hr hprime hgeometric hhom hdegree hd
  exact ⟨cert, goodSurface I r d hr hd cert⟩

/-- Construct `HighTableSurfaceSlicing` rather than assuming it.  The
promotion table itself comes from `MicrolocalPromotionTable.exists_table`;
the separated inputs are invoked only after a concrete table component and
an actual high-degree dimension--degree witness have been supplied. -/
theorem highTableSurfaceSlicing_of_separated_inputs
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (planeWeil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (slicingAG : StandardAGRationalSurfaceSlicingCertificateExistenceN10)
    (goodSurface : GoodSurfaceFibreProgressionEstimatesN10) :
    MicrolocalRationalPartition.HighTableSurfaceSlicing := by
  intro t N F f hgeo hF hAn j hj hnext
  obtain ⟨T⟩ := MicrolocalPromotionTable.exists_table
    degreeSpan smooth spread planeWeil dichotomy hgeo hF hAn
      (by omega : 1 ≤ j.val ∧ j.val ≤ 4) hnext
  refine ⟨T, ?_⟩
  intro i
  apply highComponentSurfaceSlicingData_of_separated_inputs
    slicingAG goodSurface (I := baseIdeal (T.G i))
  · omega
  · exact T.homogeneous i

end CubicTenVariables.HighTableSurfaceSlicingSeparated
