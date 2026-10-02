import HessianTheorem11.QuadraticCombination
import HessianTheorem11.GradedSchurIdentities
import HessianTheorem11.RankClosure
import HessianTheorem11.AffineSubspaces

/-! Dominance transfers the proved Jacobian Gram rank bound to the
actual normal Hessian pencil on the entire quadric. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix
variable {s r : ℕ}

def pairedQuadraticTuple (R : Matrix (Fin r) (Fin r) GeometricField)
    (p : Fin r → GeometricPolynomial s) : Fin r → GeometricPolynomial s :=
  fun i => ∑ j, C (R i j) * p j

@[simp] theorem polynomialMap_pairedQuadraticTuple
    (R : Matrix (Fin r) (Fin r) GeometricField)
    (p : Fin r → GeometricPolynomial s) (a : GeometricPoint s) :
    polynomialMap (pairedQuadraticTuple R p) a = R.mulVec (polynomialMap p a) := by
  ext i
  simp [polynomialMap, pairedQuadraticTuple, Matrix.mulVec, dotProduct]

def normalCombinationPolynomial (p : Fin r → GeometricPolynomial s)
    (a : GeometricPoint s) : Matrix (Fin s) (Fin s) (GeometricPolynomial r) :=
  fun i j => ∑ k, X k * C (eval a (pderiv j (pderiv i (p k))))

@[simp] theorem eval_normalCombinationPolynomial
    (p : Fin r → GeometricPolynomial s) (a : GeometricPoint s) (d : GeometricPoint r) :
    (normalCombinationPolynomial p a).map (eval d) = normalCombination p a d := by
  ext i j
  simp [normalCombinationPolynomial, normalCombination, Matrix.map_apply]

theorem normalCombination_rank_on_image_closure
    (MR : GenericMatrixRankInput)
    (R : Matrix (Fin r) (Fin r) GeometricField) (hR : R.IsSymm) (hdet : R.det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (a : GeometricPoint s) (d : GeometricPoint r)
    (hd : d ∈ geometricClosure (polynomialMap (pairedQuadraticTuple R p) '' Set.univ)) :
    (normalCombination p a d).rank ≤ r - 2 := by
  have hb : ∀ z ∈ polynomialMap (pairedQuadraticTuple R p) '' Set.univ,
      ((normalCombinationPolynomial p a).map (eval z)).rank ≤ r - 2 := by
    rintro _ ⟨x, _, rfl⟩
    rw [eval_normalCombinationPolynomial, polynomialMap_pairedQuadraticTuple,
      normalCombination_constant p hp a x]
    by_cases hz : polynomialMap p x = 0
    · simp [hz]
    · simpa only [Fintype.card_fin] using
        normalCombination_rank_at_pairing_value R hR hdet p hp hrel x hz
  simpa only [eval_normalCombinationPolynomial] using
    polynomialMatrix_rank_le_on_closure MR _
      (geometricallyIrreducible_univ.polynomialMap_image (pairedQuadraticTuple R p))
      (normalCombinationPolynomial p a) (r - 2) hb d hd

theorem paired_image_dense_on_quadric
    (Q R : Matrix (Fin r) (Fin r) GeometricField) (hRQ : R * Q = 1)
    (p : Fin r → GeometricPolynomial s)
    (hdom : ∀ v, dotProduct v (R.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (d : GeometricPoint r) (hd : dotProduct d (Q.mulVec d) = 0) :
    d ∈ geometricClosure (polynomialMap (pairedQuadraticTuple R p) '' Set.univ) := by
  let L : Fin r → GeometricPolynomial r := fun i => ∑ j, C (R i j) * X j
  have hL (v : GeometricPoint r) : polynomialMap L v = R.mulVec v := by
    ext i
    simp [L, polynomialMap, Matrix.mulVec, dotProduct]
  have hc : R.mulVec (Q.mulVec d) = d := by
    rw [Matrix.mulVec_mulVec, hRQ, Matrix.one_mulVec]
  have hv : Q.mulVec d ∈ geometricClosure (polynomialMap p '' Set.univ) := by
    apply hdom
    rw [hc, dotProduct_comm]
    exact hd
  have hh := polynomialMap_image_closure_subset L (polynomialMap p '' Set.univ)
    ⟨Q.mulVec d, hv, rfl⟩
  have he : polynomialMap L '' (polynomialMap p '' Set.univ) =
      polynomialMap (pairedQuadraticTuple R p) '' Set.univ := by
    rw [Set.image_image]
    congr 1
    funext x
    exact (hL _).trans (polynomialMap_pairedQuadraticTuple R p x).symm
  rw [he, hL, hc] at hh
  exact hh

theorem normalCombination_rank_on_quadric
    (MR : GenericMatrixRankInput)
    (Q R : Matrix (Fin r) (Fin r) GeometricField) (hRQ : R * Q = 1)
    (hR : R.IsSymm) (hdet : R.det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (hdom : ∀ v, dotProduct v (R.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (a : GeometricPoint s) (d : GeometricPoint r) (hd : dotProduct d (Q.mulVec d) = 0) :
    (normalCombination p a d).rank ≤ r - 2 :=
  normalCombination_rank_on_image_closure MR R hR hdet p hp hrel a d
    (paired_image_dense_on_quadric Q R hRQ p hdom d hd)

theorem graded_matrix_rank_le_of_dominance
    (MR : GenericMatrixRankInput)
    (Q R : Matrix (Fin r) (Fin r) GeometricField)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (hdet : R.det ≠ 0)
    (p : Fin r → GeometricPolynomial s) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (hdom : ∀ v, dotProduct v (R.mulVec v) = 0 →
      v ∈ geometricClosure (polynomialMap p '' Set.univ))
    (X : GeometricField) (hX : X ≠ 0) (a : GeometricPoint s) (d : GeometricPoint r)
    (hzero : X / 2 * dotProduct d (Q.mulVec d) + dotProduct d (polynomialMap p a) = 0) :
    (GradedSchurMatrix.full (X • Q) (normalCombination p a d)
      (TangentHessianRank.polynomialJacobian p a) (Q.mulVec d)).rank ≤ r + (r - 2) :=
  GradedSchurIdentities.rank_graded_matrix_le Q R hQ hR hQR hRQ p hp hrel X hX a d hzero
    (r - 2) (normalCombination_rank_on_quadric MR Q R hRQ hR hdet p hp hrel hdom a)

end HessianTheorem11
