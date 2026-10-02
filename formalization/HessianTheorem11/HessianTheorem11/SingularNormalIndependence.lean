import HessianTheorem11.SingularTupleIndependence
import HessianTheorem11.SingularWittCoordinates

/-! Independence of the actual five normal quadrics at the smooth point
of a singular component. The formal-arc relation, nondegenerate normal
pairing, common-radical obstruction, adapted coordinates, UFD classification
and weight contradictions are all derived from the original cubic. -/
noncomputable section
set_option maxRecDepth 4000
namespace HessianTheorem11
open Module MvPolynomial Matrix PolynomialRestriction
open SingularRadialNormalForm SingularPositiveNormalForm SingularNormalEquations
open SingularNormalPairing NonzeroLimitTransport TangentHessianRank WittQuadraticTuple
variable {n s : ℕ}

theorem normal_tuple_independent
    (SA : FormalSmoothArcInput)
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (A : AdaptedFlagBasis (affineTangentSpace Z x) (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hgap : 2*n < 3*finrank GeometricField (affineTangentSpace Z x)+6)
    (C₀ : GradedIndexCoordinates A.tangentIndices A.radial 5 s) (hs : 5 ≤ s)
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField) (hq : q.IsHomogeneous 2)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hp : ∀ i, (p i).IsHomogeneous 2)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      normalQuadratic
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i) : LinearIndependent GeometricField p := by
  classical
  have hrel := typed_normal_quadratic_relation SA F hF Z hZ hirred hsing x hx hdim
    A hT htensor q p hqe hpe
  have hdet := typed_normal_det_ne_zero_in_adapted_flag F hF x _ A hT htensor q hqe
  have hcommon := normal_tuple_differentialRadical_eq_bot F hF hsemi x _ A hT htensor
    hgap p hpe C₀
  let Q := quadraticHessian (C₀.normalPolynomial q)
  have hQ : Q.det ≠ 0 := C₀.normalPolynomial_det_ne_zero q hdet
  have hQsym : Q.IsSymm := GradedCubic.quadraticHessian_symm _
  have hInvSym : (Q⁻¹).IsSymm := by
    rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hQsym.eq]
  have hInvDet : (Q⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact inv_ne_zero hQ
  let B := Matrix.toBilin' Q⁻¹
  have hB : B.IsSymm := CliffordNormalization.toBilin'_isSymm _ hInvSym
  have hnB : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hInvDet
  apply C₀.rawTuple_independent p
  apply singular_normal_tuple_independent_of_coordinates F hF hsemi (C₀.normalTuple p)
    (C₀.normalTuple_homogeneous p hp) B hB hnB
    (quadraticRelation_toBilin_value Q⁻¹ (C₀.normalTuple p) (C₀.normalTuple_relation q p hrel))
    hcommon hs
  intro r l k D ba
  exact SingularWittCoordinates.exists_coordinates F hF x _ A hT htensor q p hqe hpe C₀ D ba

end HessianTheorem11
