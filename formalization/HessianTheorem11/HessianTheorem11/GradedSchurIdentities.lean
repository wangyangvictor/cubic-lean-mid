import HessianTheorem11.GradedSchurMatrix
import HessianTheorem11.QuadraticCombination

/-! The exact shifted-normal-variable identities for a graded singular
cubic with an arbitrary nondegenerate symmetric normal form. -/
noncomputable section
namespace HessianTheorem11.GradedSchurIdentities
open MvPolynomial Matrix
variable {K : Type*} [Field K] [CharZero K] {s r : ℕ}

theorem pairing_swap {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q.IsSymm)
    (u v : Fin n → K) : dotProduct u (Q.mulVec v) = dotProduct (Q.mulVec u) v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQ]

theorem relation_eval (R : Matrix (Fin r) (Fin r) K)
    (p : Fin r → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation R p = 0) (a : Fin s → K) :
    dotProduct (fun i => eval a (p i)) (R.mulVec (fun i => eval a (p i))) = 0 := by
  have h := congrArg (eval a) hrel
  simpa only [TangentHessianRank.quadraticRelation, map_sum, map_mul, eval_C,
    map_zero, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc] using h

def shift (R : Matrix (Fin r) (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K)
    (X : K) (a : Fin s → K) (d : Fin r → K) : Fin r → K :=
  d + X⁻¹ • R.mulVec (fun i => eval a (p i))

theorem shift_pairing
    (R : Matrix (Fin r) (Fin r) K) (p : Fin r → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (a : Fin s → K) (d : Fin r → K) :
    dotProduct (shift R p X a d) (fun i => eval a (p i)) =
      dotProduct d (fun i => eval a (p i)) := by
  simp only [shift, add_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm (R.mulVec _), relation_eval R p hrel a, mul_zero, add_zero]

theorem shift_quadric
    (Q R : Matrix (Fin r) (Fin r) K) (hQ : Q.IsSymm) (hQR : Q * R = 1)
    (p : Fin r → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (a : Fin s → K) (d : Fin r → K) :
    dotProduct (shift R p X a d) (Q.mulVec (shift R p X a d)) =
      dotProduct d (Q.mulVec d) + 2 * X⁻¹ * dotProduct d (fun i => eval a (p i)) := by
  have hcancel : Q.mulVec (R.mulVec (fun i => eval a (p i))) =
      (fun i => eval a (p i)) := by
    rw [Matrix.mulVec_mulVec, hQR, Matrix.one_mulVec]
  have hcross : dotProduct (R.mulVec (fun i => eval a (p i))) (Q.mulVec d) =
      dotProduct d (fun i => eval a (p i)) := by
    rw [pairing_swap Q hQ, hcancel, dotProduct_comm]
  simp only [shift, Matrix.mulVec_add, Matrix.mulVec_smul, hcancel,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hcross, dotProduct_comm (R.mulVec _), relation_eval R p hrel a]
  ring

theorem shift_on_quadric
    (Q R : Matrix (Fin r) (Fin r) K) (hQ : Q.IsSymm) (hQR : Q * R = 1)
    (p : Fin r → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (hX : X ≠ 0) (a : Fin s → K) (d : Fin r → K)
    (hzero : X / 2 * dotProduct d (Q.mulVec d) + dotProduct d (fun i => eval a (p i)) = 0) :
    dotProduct (shift R p X a d) (Q.mulVec (shift R p X a d)) = 0 := by
  rw [shift_quadric Q R hQ hQR p hrel]
  field_simp
  linear_combination 2 * hzero

theorem shifted_combination
    (R : Matrix (Fin r) (Fin r) K) (hR : R.IsSymm)
    (p : Fin r → MvPolynomial (Fin s) K)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (a : Fin s → K) (d : Fin r → K) :
    normalCombination p a (shift R p X a d) = normalCombination p a d -
      (TangentHessianRank.polynomialJacobian p a).transpose * (X⁻¹ • R) *
        TangentHessianRank.polynomialJacobian p a := by
  rw [shift, normalCombination_add, normalCombination_smul,
    normalCombination_at_pairing_value R hR p hrel]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_neg, sub_eq_add_neg]

theorem shifted_cross
    (Q R : Matrix (Fin r) (Fin r) K) (hRQ : R * Q = 1) (hR : R.IsSymm)
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (a : Fin s → K) (d : Fin r → K) :
    (TangentHessianRank.polynomialJacobian p a).transpose.mulVec
        ((X⁻¹ • R).mulVec (Q.mulVec d)) =
      (normalCombination p a (shift R p X a d)).mulVec (X⁻¹ • a) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, hRQ, Matrix.one_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_smul, normalCombination_mulVec p hp]
  rw [shift, Matrix.mulVec_add, Matrix.mulVec_smul,
    TangentHessianRank.quadratic_relation_jacobian_annihilator R hR p hrel a,
    smul_zero, add_zero]

theorem shifted_scalar
    (Q R : Matrix (Fin r) (Fin r) K) (hQ : Q.IsSymm) (hRQ : R * Q = 1)
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (a : Fin s → K) (d : Fin r → K)
    (hzero : X / 2 * dotProduct d (Q.mulVec d) + dotProduct d (fun i => eval a (p i)) = 0) :
    dotProduct (Q.mulVec d) ((X⁻¹ • R).mulVec (Q.mulVec d)) =
      -dotProduct (X⁻¹ • a)
        ((normalCombination p a (shift R p X a d)).mulVec (X⁻¹ • a)) := by
  rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec, hRQ, Matrix.one_mulVec,
    Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_smul,
    normalCombination_quadratic p hp, shift_pairing R p hrel]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (Q.mulVec d)]
  by_cases hX : X = 0
  · simp [hX]
  · field_simp
    linear_combination 2 * hzero

/-- The actual graded Hessian matrix is bounded using only the rank of
the normal Hessian pencil on its quadric. -/
theorem rank_graded_matrix_le
    (Q R : Matrix (Fin r) (Fin r) K) (hQ : Q.IsSymm) (hR : R.IsSymm)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation R p = 0)
    (X : K) (hX : X ≠ 0) (a : Fin s → K) (d : Fin r → K)
    (hzero : X / 2 * dotProduct d (Q.mulVec d) + dotProduct d (fun i => eval a (p i)) = 0)
    (b : ℕ) (hbound : ∀ z, dotProduct z (Q.mulVec z) = 0 → (normalCombination p a z).rank ≤ b) :
    (GradedSchurMatrix.full (X • Q) (normalCombination p a d)
      (TangentHessianRank.polynomialJacobian p a) (Q.mulVec d)).rank ≤ r + b := by
  have hAR : (X • Q) * (X⁻¹ • R) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQR, smul_smul, mul_inv_cancel₀ hX, one_smul]
  have hRA : (X⁻¹ • R) * (X • Q) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hRQ, smul_smul, inv_mul_cancel₀ hX, one_smul]
  have hRs : (X⁻¹ • R).IsSymm := by
    change (X⁻¹ • R).transpose = _
    rw [Matrix.transpose_smul, hR]
  have hh := GradedSchurMatrix.rank_full_le (X • Q) (X⁻¹ • R) hAR hRA hRs
    (normalCombination p a d) (normalCombination_symmetric p a d)
    (TangentHessianRank.polynomialJacobian p a) (Q.mulVec d)
    (normalCombination p a (shift R p X a d)) (shifted_combination R hR p hrel X a d)
    (X⁻¹ • a) (shifted_cross Q R hRQ hR p hp hrel X a d)
    (shifted_scalar Q R hQ hRQ p hp hrel X a d hzero)
  simpa only [Fintype.card_fin] using hh.trans
    (Nat.add_le_add_left (hbound _ (shift_on_quadric Q R hQ hQR p hrel X hX a d hzero)) _)

end HessianTheorem11.GradedSchurIdentities
