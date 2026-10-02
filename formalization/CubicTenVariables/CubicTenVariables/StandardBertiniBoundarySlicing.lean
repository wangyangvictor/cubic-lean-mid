import CubicTenVariables.ExactDegreeRationalSurfaceSlicing
import TranslatedDepthSeven.ProjectiveBoundaryDegreeInternal

/-!
# A standard Bertini boundary certificate for rational surface slices

The affine targets in one rational slicing family change only the constant
terms of the slice equations.  Their homogenizations therefore have one
common scheme-theoretic boundary at infinity.  This file packages the
remaining standard Bertini input as:

* one existing rational surface-slicing certificate;
* a proper prime flag for its homogenized slice equations on every good
  fibre; and
* geometric primeness of the one common boundary.

Its dimension and degree are consequences rather than input: the proper
prime flag gives the projective slice closure dimension three and degree
`d`; the common prime boundary is its proper `X₀ = 0` hyperplane section,
so the exact Hilbert-difference theorem gives dimension two and degree `d`.

No projection or point-count estimate is included in this certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

namespace CubicTenVariables.StandardBertiniBoundarySlicing

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSlicingReduction
open ExactDegreeRationalSurfaceSlicing

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Geometric primeness includes primeness over the ground field. -/
theorem isPrime_of_geometricallyPrime
    {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℚ)}
    (hJ : GeometricallyPrimeMvPolynomialIdeal J) : J.IsPrime := by
  have hground := hJ ℚ
  have hmap : MvPolynomial.map (algebraMap ℚ ℚ) =
      RingHom.id (MvPolynomial (Fin n) ℚ) := by
    ext <;> simp
  rw [hmap, Ideal.map_id] at hground
  exact hground

/-- The fixed boundary ideal of a rational affine slicing family.  It is
written without choosing a fibre parameter. -/
def rationalSurfaceSliceBoundaryIdeal
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I) :
    Ideal (MvPolynomial (Fin 10) ℚ) :=
  projectiveBoundaryIdeal (affineIdealProjectiveClosure I) ⊔
    Ideal.span (Set.range
      (rationalSliceBoundaryEquation slicing.matrix))

/-- The boundary of every explicit homogenized slice is the fixed family
boundary. -/
theorem projectiveBoundaryIdeal_rationalProjectiveSliceIdeal_eq_fixed
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I)
    (y : Fin (r - 2) → ℚ) :
    projectiveBoundaryIdeal
        (rationalProjectiveSliceIdeal I slicing.matrix y) =
      rationalSurfaceSliceBoundaryIdeal slicing := by
  simpa only [rationalSurfaceSliceBoundaryIdeal] using
    projectiveBoundaryIdeal_rationalProjectiveSliceIdeal
      I slicing.matrix y

/-- Standard Bertini data strengthened only by geometric integrality of the
single common boundary.  Its dimension and degree are derived below. -/
structure RationalSurfaceBertiniBoundaryCertificate
    {r d : ℕ} (I : Ideal (MvPolynomial (Fin 10) ℚ)) where
  slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I
  primeFlags : HasGoodFibreProjectivePrimeFlags I slicing
  boundary_geometricallyPrime :
    GeometricallyPrimeMvPolynomialIdeal
      (rationalSurfaceSliceBoundaryIdeal slicing)

/-- On a good fibre, the kernel-defined projective closure of the affine
slice has exactly the certificate's one fixed boundary. -/
theorem good_fibre_projectiveBoundary_eq_fixed
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hIprime : I.IsPrime)
    (cert : RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I)
    (y : Fin (r - 2) → ℚ)
    (hy : eval y cert.slicing.discriminant ≠ 0) :
    projectiveBoundaryIdeal
        (affineIdealProjectiveClosure
          (rationalSliceIdeal I cert.slicing.matrix y)) =
      rationalSurfaceSliceBoundaryIdeal cert.slicing := by
  have hclosure :=
    rationalProjectiveSliceIdeal_eq_affineIdealProjectiveClosure_of_primeFlag
      I hIprime cert.slicing.matrix y
      (cert.slicing.good_fibre_geometry y hy).1
      (cert.primeFlags y hy)
  rw [← hclosure]
  exact projectiveBoundaryIdeal_rationalProjectiveSliceIdeal_eq_fixed
    cert.slicing y

/-- The boundary of every good affine slice closure is prime. -/
theorem good_fibre_projectiveBoundary_isPrime
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hIprime : I.IsPrime)
    (cert : RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I)
    (y : Fin (r - 2) → ℚ)
    (hy : eval y cert.slicing.discriminant ≠ 0) :
    (projectiveBoundaryIdeal
      (affineIdealProjectiveClosure
        (rationalSliceIdeal I cert.slicing.matrix y))).IsPrime := by
  rw [good_fibre_projectiveBoundary_eq_fixed hIprime cert y hy]
  exact isPrime_of_geometricallyPrime cert.boundary_geometricallyPrime

/-- The boundary of every good affine slice closure is geometrically prime. -/
theorem good_fibre_projectiveBoundary_geometricallyPrime
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hIprime : I.IsPrime)
    (cert : RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I)
    (y : Fin (r - 2) → ℚ)
    (hy : eval y cert.slicing.discriminant ≠ 0) :
    GeometricallyPrimeMvPolynomialIdeal
      (projectiveBoundaryIdeal
        (affineIdealProjectiveClosure
          (rationalSliceIdeal I cert.slicing.matrix y))) := by
  rw [good_fibre_projectiveBoundary_eq_fixed hIprime cert y hy]
  exact cert.boundary_geometricallyPrime

/-- The boundary of every good affine slice closure has projective
dimension two and the original degree `d`. -/
theorem good_fibre_projectiveBoundary_dimension_degree
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (hr : r = 4 ∨ r = 5)
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I r d)
    (cert : RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I)
    (y : Fin (r - 2) → ℚ)
    (hy : eval y cert.slicing.discriminant ≠ 0) :
    HasProjectiveDimensionDegree
      (projectiveBoundaryIdeal
        (affineIdealProjectiveClosure
          (rationalSliceIdeal I cert.slicing.matrix y))) 2 d := by
  let J := rationalSliceIdeal I cert.slicing.matrix y
  let P := affineIdealProjectiveClosure J
  have hJprime : J.IsPrime := (cert.slicing.good_fibre_geometry y hy).1
  have hJdegree : HasAffineDimensionDegree J 3 d :=
    good_fibre_hasAffineDimensionDegree_exact hr I hIprime hIhom hIdegree
      cert.slicing cert.primeFlags y hy
  have hPdegree : HasProjectiveDimensionDegree P 3 d :=
    affineIdealProjectiveClosure_hasProjectiveDimensionDegree J hJdegree
  have hPprime : P.IsPrime := affineIdealProjectiveClosure_isPrime J hJprime
  have hPhom : P.IsHomogeneous
      (homogeneousSubmodule (Fin 11) ℚ) :=
    affineIdealProjectiveClosure_isHomogeneous J
  have hX : X (0 : Fin 11) ∉ P :=
    affineIdealProjectiveClosure_X_zero_not_mem J hJprime
  have hboundaryPrime : (projectiveBoundaryIdeal P).IsPrime := by
    dsimp only [P]
    exact good_fibre_projectiveBoundary_isPrime hIprime cert y hy
  exact projectiveBoundary_hasProjectiveDimensionDegree
    P hPprime hPhom hPdegree hX hboundaryPrime

/-- The corresponding standard-AG existence premise in the dimensions used
by the ten-variable theorem. -/
def StandardAGBertiniBoundarySlicingN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) →
    HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    Nonempty (RationalSurfaceBertiniBoundaryCertificate (r := r) (d := d) I)

end CubicTenVariables.StandardBertiniBoundarySlicing
