import HessianTheorem11.BinaryQuadraticCoordinates

/-! Classification of three independent quadrics with affine image
dimension at most two, derived from a dense binary slice and polynomial UFD
factorization. No curve-classification input is used. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n : ℕ}

theorem three_independent_quadrics_low_image
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (P : Fin 3 → GeometricPolynomial n) (hP : ∀ i, (P i).IsHomogeneous 2)
    (hli : LinearIndependent GeometricField P)
    (hdim : affineDimension (geometricClosure (polynomialMap P '' Set.univ)) ≤ 2) :
    ∃ A : Matrix (Fin 3) (Fin 3) GeometricField, IsUnit A ∧
      ∃ t : GeometricField, t ≠ 0 ∧ ∃ u v : GeometricPolynomial n,
        u.IsHomogeneous 1 ∧ v.IsHomogeneous 1 ∧
        combinePolynomials A P 0 = C t * u ^ 2 ∧
        combinePolynomials A P 1 = C t * u * v ∧
        combinePolynomials A P 2 = C t * v ^ 2 := by
  obtain ⟨x, y, hclosure⟩ := quadratic_low_image_has_twoPlane GR AD P hP
    ⟨0, hli.ne_zero 0⟩ hdim
  let B := twoPlaneMatrix x y
  let R : Fin 3 → GeometricPolynomial 2 := fun i => restrict B (P i)
  have hR : ∀ i, (R i).IsHomogeneous 2 := fun i => homogeneous_restrict B (P i) (hP i)
  have hRli : LinearIndependent GeometricField R :=
    linearIndependent_of_same_imageClosure P R hclosure.symm hli
  obtain ⟨A, hA, hnorm⟩ := binaryQuadratic_normalize R hR hRli
  let q := combinePolynomials A P
  have hq : ∀ i, (q i).IsHomogeneous 2 := combinePolynomials_homogeneous A P hP
  have hqli : LinearIndependent GeometricField q := combinePolynomials_linearIndependent A hA P hli
  let S : GeometricPolynomial 3 := X 0 * X 2 - X 1 ^ 2
  have hslice : aeval (combinePolynomials A R) S = 0 := by
    rw [hnorm]
    simp [S, binaryQuadraticMonomials]
    ring
  have hglobal := (combinePolynomials_relation_transfer A P R hclosure.symm S).mpr hslice
  have hrel : q 0 * q 2 = q 1 ^ 2 := by
    apply sub_eq_zero.mp
    simpa [S, q] using hglobal
  obtain ⟨t, ht, u, v, hu, hv, h0, h1, h2⟩ :=
    QuadricLowRank.three_independent_quadrics q hq hqli hrel
  exact ⟨A, hA, t, ht, u, v, hu, hv, h0, h1, h2⟩

end HessianTheorem11
