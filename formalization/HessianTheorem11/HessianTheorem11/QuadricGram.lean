import HessianTheorem11.QuadraticIrreducibility
import HessianTheorem11.TangentHessianRank

noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial TangentHessianRank
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual quadratic polynomial with Gram matrix `A`. -/
def gramPolynomial (A : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin n) K :=
  quadraticRelation A X

theorem gramPolynomial_homogeneous (A : Matrix (Fin n) (Fin n) K) :
    (gramPolynomial A).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  apply IsHomogeneous.sum
  intro j hj
  exact (isHomogeneous_C_mul_X (A i j) i).mul (isHomogeneous_X K j)

theorem pderiv_gramPolynomial (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    pderiv i (gramPolynomial A) = ∑ j, C (A i j + A j i) * X j := by
  classical
  simp [gramPolynomial, quadraticRelation, Derivation.leibniz, smul_eq_mul,
    Pi.single_apply, mul_ite, Finset.sum_add_distrib, add_mul]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem hessian_gramPolynomial (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm)
    (x : Fin n → K) : hessian (gramPolynomial A) x = (2 : K) • A := by
  classical
  ext i j
  simp [hessian, hessianPolynomial, pderiv_gramPolynomial, Derivation.leibniz,
    smul_eq_mul, Pi.single_apply, mul_ite]
  rw [hA.apply i j]
  ring

theorem gramPolynomial_irreducible [CharZero K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hn : 2 < n) : Irreducible (gramPolynomial A) := by
  apply homogeneous_quadratic_irreducible_of_hessian_rank _ (gramPolynomial_homogeneous A) 0
  rw [hessian_gramPolynomial A hA]
  have hdet' : ((2 : K) • A).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have hr := Matrix.rank_of_isUnit ((2 : K) • A)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet'))
  simpa only [hr, Fintype.card_fin] using hn

theorem eval_gramPolynomial (A : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    eval x (gramPolynomial A) = dotProduct x (A.mulVec x) := by
  simp only [gramPolynomial, quadraticRelation, map_sum, map_mul, eval_C, eval_X,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HessianTheorem11
