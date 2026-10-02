import HessianTheorem11.TernaryQuadricKernel
import Mathlib.Algebra.MvPolynomial.Funext
import HessianTheorem11.TangentHessianRank

noncomputable section
namespace HessianTheorem11.FiveTernaryQuadrics
open Matrix MvPolynomial Module TangentHessianRank
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

/-- Coefficients in `(x²,y²,z²,xy,xz,yz)`. -/
def quadraticCoefficients (p : MvPolynomial (Fin 3) K) : Fin 6 → K :=
  let H := LocalCubicNormalForm.quadraticMatrix p
  ![H 0 0 / 2, H 1 1 / 2, H 2 2 / 2, H 0 1, H 0 2, H 1 2]

def monomialValues (x : Fin 3 → K) : Fin 6 → K :=
  ![x 0 ^ 2, x 1 ^ 2, x 2 ^ 2, x 0 * x 1, x 0 * x 2, x 1 * x 2]

theorem quadratic_eval (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 2)
    (x : Fin 3 → K) :
    eval x p = dotProduct (quadraticCoefficients p) (monomialValues x) := by
  have he := LocalCubicNormalForm.quadratic_eval_identity p hp x
  have hs := LocalCubicNormalForm.quadraticMatrix_symmetric p
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 1) hs
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hs
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 2) hs
  simp only [Matrix.transpose_apply] at h01 h02 h12
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h01, h02, h12] at he
  simp [quadraticCoefficients, monomialValues, dotProduct, Fin.sum_univ_succ]
  linear_combination (-1/2 : K) * he

def basisQuadrics : Fin 6 → MvPolynomial (Fin 3) K :=
  ![X 0 ^ 2, X 1 ^ 2, X 2 ^ 2, X 0 * X 1, X 0 * X 2, X 1 * X 2]

theorem eval_basisQuadrics (x : Fin 3 → K) :
    (fun i => eval x (basisQuadrics i)) = monomialValues x := by
  ext i
  fin_cases i <;> simp [basisQuadrics, monomialValues]

theorem quadratic_representation (p : MvPolynomial (Fin 3) K)
    (hp : p.IsHomogeneous 2) :
    Fintype.linearCombination K (basisQuadrics (K := K)) (quadraticCoefficients p) = p := by
  apply MvPolynomial.funext
  intro x
  rw [quadratic_eval p hp]
  simp only [Fintype.linearCombination_apply, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  change (∑ i, quadraticCoefficients p i * eval x (basisQuadrics i)) = _
  simp_rw [show ∀ i, eval x (basisQuadrics i) = monomialValues x i from
    fun i => congrFun (eval_basisQuadrics x) i]
  rfl

theorem coefficient_rows_independent {m : ℕ}
    (p : Fin m → MvPolynomial (Fin 3) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent K p) :
    LinearIndependent K (fun i => quadraticCoefficients (p i)) := by
  apply LinearIndependent.of_comp (Fintype.linearCombination K (basisQuadrics (K := K)))
  convert hlin using 1
  funext i
  exact quadratic_representation (p i) (hp i)

/-- Every matrix with independent rows has an actual right inverse. -/
theorem exists_right_inverse {m n : ℕ} (B : Matrix (Fin m) (Fin n) K)
    (hB : LinearIndependent K B.row) :
    ∃ D : Matrix (Fin n) (Fin m) K, B * D = 1 := by
  have hr : B.rank = m := by simpa using hB.rank_matrix
  have hsurj : Function.Surjective B.mulVecLin := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    change B.rank = finrank K (Fin m → K)
    simpa using hr
  choose u hu using fun i : Fin m => hsurj (Pi.single i 1)
  refine ⟨fun j i => u i j, ?_⟩
  ext i j
  have he := congrFun (hu j) i
  simpa [Matrix.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Pi.single_apply, eq_comm] using he

theorem rank_congruence_of_independent_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (hA : A.det ≠ 0)
    (B : Matrix (Fin m) (Fin n) K) (hB : LinearIndependent K B.row) :
    (B.transpose * A * B).rank = m := by
  obtain ⟨D,hD⟩ := exists_right_inverse B hB
  have hback : D.transpose * (B.transpose * A * B) * D = A := by
    calc
      _ = (B * D).transpose * A * (B * D) := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hD, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hra : A.rank = m := by
    simpa using Matrix.rank_of_isUnit A
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA))
  have hlo : m ≤ (B.transpose * A * B).rank := by
    calc
      m = A.rank := hra.symm
      _ = (D.transpose * (B.transpose * A * B) * D).rank := congrArg Matrix.rank hback.symm
      _ ≤ (B.transpose * A * B).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  apply le_antisymm _ hlo
  simpa using (Matrix.rank_mul_le_right (B.transpose*A) B).trans (Matrix.rank_le_card_height B)

theorem basisQuadrics_eq_veronese :
    basisQuadrics (K := K) = TernaryQuadricKernel.veronese := by
  funext i
  fin_cases i <;>
    simp [basisQuadrics, TernaryQuadricKernel.veronese,
      TernaryQuadricKernel.veroneseExponent, ← X_pow_eq_monomial,
      monomial_single_add]

theorem eval_bind_matrixForm (M : Matrix (Fin 6) (Fin 6) K) (x : Fin 3 → K) :
    eval x (bind₁ TernaryQuadricKernel.veronese (TernaryQuadricKernel.matrixForm M)) =
      dotProduct (monomialValues x) (M.mulVec (monomialValues x)) := by
  simp only [TernaryQuadricKernel.matrixForm, map_sum, map_mul,
    bind₁_C_right, bind₁_X_right, eval_C]
  rw [← basisQuadrics_eq_veronese]
  simp_rw [show ∀ i, eval x (basisQuadrics i) = monomialValues x i from
    fun i => congrFun (eval_basisQuadrics x) i]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Five independent ternary quadrics cannot satisfy a nondegenerate
quadratic relation. Every coefficient and matrix in the proof is actual. -/
theorem five_independent_no_relation
    (p : Fin 5 → MvPolynomial (Fin 3) K)
    (hp : ∀ i, (p i).IsHomogeneous 2) (hlin : LinearIndependent K p)
    (A : Matrix (Fin 5) (Fin 5) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) : False := by
  let B : Matrix (Fin 5) (Fin 6) K := fun i => quadraticCoefficients (p i)
  have hB : LinearIndependent K B.row := coefficient_rows_independent p hp hlin
  let M := B.transpose * A * B
  have hM : M.transpose = M := by
    simp only [M, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
      Matrix.mul_assoc]
  have hMrank : M.rank = 5 := rank_congruence_of_independent_rows A hdet B hB
  apply TernaryQuadricKernel.matrix_rank_ne_five M hM _ hMrank
  apply MvPolynomial.funext
  intro x
  rw [eval_bind_matrixForm, map_zero]
  have hx : B.mulVec (monomialValues x) = fun i => eval x (p i) := by
    funext i
    exact (quadratic_eval (p i) (hp i) x).symm
  have he := congrArg (eval x) hrel
  have he' : dotProduct (fun i => eval x (p i)) (A.mulVec (fun i => eval x (p i))) = 0 := by
    simpa [quadraticRelation, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_left_comm] using he
  change dotProduct (monomialValues x)
    ((B.transpose * A * B).mulVec (monomialValues x)) = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hx]
  exact he'

end HessianTheorem11.FiveTernaryQuadrics
