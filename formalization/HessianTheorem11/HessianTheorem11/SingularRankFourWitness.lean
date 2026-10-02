import HessianTheorem11.SingularNormalJacobian
import HessianTheorem11.QuadraticCoordinateTransport
import HessianTheorem11.FiveQuadricsDominance

/-! Independence of the actual five normal quadrics gives the intrinsic
rank-four tangent Hessian witness required by the eleven-variable sieve. -/

set_option maxRecDepth 4000

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module Matrix PolynomialRestriction
open SingularRadialNormalForm SingularPositiveNormalForm SingularNormalEquations
open SingularRadialEquality NonzeroLimitTransport TangentHessianRank SingularNormalPairing

namespace GradedIndexCoordinates
variable {n r s : ℕ} {T : Finset (Fin n)} {c : Fin n}

theorem normalTuple_jacobian (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) GeometricField)
    (a : GeometricPoint s) :
    polynomialJacobian (D.normalTuple p) a =
      (polynomialJacobian p (a ∘ D.tangent.symm)).submatrix D.normal D.tangent := by
  ext i j
  change eval a (pderiv j (rename D.tangent.symm (p (D.normal i)))) =
    eval (a ∘ D.tangent.symm) (pderiv (D.tangent j) (p (D.normal i)))
  have he := pderiv_rename D.tangent.symm.injective (D.tangent j) (p (D.normal i))
  simp only [D.tangent.symm_apply_apply] at he
  rw [he, eval_rename]

theorem normalTuple_jacobian_rank (D : GradedIndexCoordinates T c r s)
    (p : (↑Tᶜ : Type) → MvPolynomial (↑(T.erase c) : Type) GeometricField)
    (a : GeometricPoint s) :
    (polynomialJacobian (D.normalTuple p) a).rank =
      (polynomialJacobian p (a ∘ D.tangent.symm)).rank := by
  rw [D.normalTuple_jacobian, Matrix.rank_submatrix]

end GradedIndexCoordinates

/-- All geometric source-specific premises are actual tangent and
Hessian data; independence is the remaining local algebra premise. -/
theorem exists_tangent_rank_four_of_normal_independent
    (SA : FormalSmoothArcInput) (GR : GenericRankOpenInput)
    (AD : AffineHypersurfaceDimensionInput) {n s : ℕ}
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (A : AdaptedFlagBasis (affineTangentSpace Z x) (LinearMap.ker (hessian F x).mulVecLin) x)
    (hT : affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (D : GradedIndexCoordinates A.tangentIndices A.radial 5 s)
    (q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField)
    (p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField)
    (hp : ∀ i, (p i).IsHomogeneous 2) (hlin : LinearIndependent GeometricField p)
    (hqe : rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      normalQuadratic
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial)
    (hpe : ∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent
        (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis) F)
          (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i) :
    ∃ v ∈ affineTangentSpace Z x, 4 ≤ finrank GeometricField
      (LinearMap.range ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x))) := by
  classical
  have hrel := typed_normal_quadratic_relation SA F hF Z hZ hirred hsing x hx hdim
    A hT htensor q p hqe hpe
  have hdet := typed_normal_det_ne_zero_in_adapted_flag F hF x _ A hT htensor q hqe
  have hDdet := D.normalPolynomial_det_ne_zero q hdet
  have hDsym : ((quadraticHessian (D.normalPolynomial q))⁻¹).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_nonsing_inv, (GradedCubic.quadraticHessian_symm _).eq]
  have hDinvdet : ((quadraticHessian (D.normalPolynomial q))⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero hDdet
  obtain ⟨a, _, ha⟩ := five_quadrics_exists_rank_four GR AD (D.normalTuple p)
    (D.normalTuple_homogeneous p hp) (D.normalTuple_independent p hlin)
    (quadraticHessian (D.normalPolynomial q))⁻¹ hDsym hDinvdet (D.normalTuple_relation q p hrel)
  rw [D.normalTuple_jacobian_rank] at ha
  let u := a ∘ D.tangent.symm
  let v := (HessianTheorem11.basisMatrix A.basis).mulVec
    (blockExtension (A.tangentIndices.erase A.radial) u)
  refine ⟨v, blockExtension_in_tangent _ _ x A u, ?_⟩
  have hb := normal_jacobian_rank_le_tangent_hessian F hF x _ A hT htensor p hpe u
  rw [show (polynomialJacobian p u).rank = 4 from ha] at hb
  exact hb

end HessianTheorem11
