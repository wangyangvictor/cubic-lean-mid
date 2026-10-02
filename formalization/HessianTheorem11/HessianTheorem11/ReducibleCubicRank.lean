import HessianTheorem11.HessianDeterminant
import HessianTheorem11.LocalCubicNormalForm
import HessianTheorem11.MatrixRankBounds

/-! Actual Hessian ranks on a cubic with a linear factor. The proof uses
product derivatives and a kernel injection into one dimension, without
classifying the quadratic factor. -/
noncomputable section
namespace HessianTheorem11.ReducibleCubicRank
open MvPolynomial Module LocalCubicNormalForm
open scoped BigOperators

variable {K : Type*} [Field K] {n : ℕ}

def linearCoefficient (L : MvPolynomial (Fin n) K) : Fin n → K :=
  fun i => coeff 0 (pderiv i L)

theorem linear_partial (L : MvPolynomial (Fin n) K) (hL : L.IsHomogeneous 1)
    (i : Fin n) : pderiv i L = C (linearCoefficient L i) :=
  HessianTheorem11.homogeneous_zero_eq_constant hL.pderiv

theorem eval_linear (L : MvPolynomial (Fin n) K) (hL : L.IsHomogeneous 1)
    (x : Fin n → K) : eval x L = dotProduct (linearCoefficient L) x := by
  simpa [linearCoefficient, dotProduct, mul_comm] using eval_homogeneous_one hL x

theorem gradient_quadratic (Q : MvPolynomial (Fin n) K) (hQ : Q.IsHomogeneous 2)
    (x : Fin n → K) : gradient Q x = (quadraticMatrix Q).mulVec x := by
  ext i
  simp [gradient, quadratic_first_partial Q hQ, Matrix.mulVec, dotProduct]

theorem hessian_linear_product (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2) (x : Fin n → K) :
    hessian (L*Q) x = eval x L • quadraticMatrix Q +
      Matrix.vecMulVec (linearCoefficient L) (gradient Q x) +
      Matrix.vecMulVec (gradient Q x) (linearCoefficient L) := by
  apply Matrix.ext
  intro i j
  simp [hessian, hessianPolynomial, Derivation.leibniz, smul_eq_mul,
    linear_partial L hL, quadratic_second_partial Q hQ, gradient,
    Matrix.vecMulVec_apply]
  ring

theorem symmetric_dot_mulVec (M : Matrix (Fin n) (Fin n) K) (hM : M.transpose = M)
    (u v : Fin n → K) : dotProduct (M.mulVec u) v = dotProduct u (M.mulVec v) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hM]

/-- At a zero of the linear factor the actual Hessian is a sum of two
matrices of rank at most one. -/
theorem rank_le_two_on_linear_factor (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (x : Fin n → K) (hx : eval x L = 0) : (hessian (L*Q) x).rank ≤ 2 := by
  rw [hessian_linear_product L Q hL hQ, hx, zero_smul, zero_add]
  exact (MatrixRankBounds.rank_add_le _ _).trans (by
    have h1 := Matrix.rank_vecMulVec_le (linearCoefficient L) (gradient Q x)
    have h2 := Matrix.rank_vecMulVec_le (gradient Q x) (linearCoefficient L)
    omega)

/-- A common radical direction of the quadratic factor and the linear
factor kills the Hessian everywhere. -/
theorem common_radical_kills_hessian (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (u : Fin n → K) (huQ : (quadraticMatrix Q).mulVec u = 0)
    (huL : dotProduct (linearCoefficient L) u = 0) (x : Fin n → K) :
    (hessian (L*Q) x).mulVec u = 0 := by
  have hgrad : dotProduct (gradient Q x) u = 0 := by
    rw [gradient_quadratic Q hQ, symmetric_dot_mulVec _ (quadraticMatrix_symmetric Q), huQ]
    simp
  rw [hessian_linear_product L Q hL hQ]
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    huQ, huL, hgrad]

variable [Infinite K]

/-- Nonzero actual Hessian determinant rules out a common radical
of the two factors, over any infinite field. -/
theorem common_radical_eq_zero (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (hdet : hessianDeterminantPolynomial (L*Q) ≠ 0)
    (u : Fin n → K) (huQ : (quadraticMatrix Q).mulVec u = 0)
    (huL : dotProduct (linearCoefficient L) u = 0) : u = 0 := by
  have hex : ∃ x : Fin n → K, (hessian (L*Q) x).det ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdet
    apply MvPolynomial.funext
    intro x
    simpa [eval_hessianDeterminantPolynomial] using h x
  obtain ⟨x, hx⟩ := hex
  have hi : Function.Injective (hessian (L*Q) x).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
  apply hi
  simpa using common_radical_kills_hessian L Q hL hQ u huQ huL x

variable [CharZero K]

theorem gradient_linear_product (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (x : Fin n → K) :
    gradient (L*Q) x = eval x Q • linearCoefficient L + eval x L • gradient Q x := by
  ext i
  simp [gradient, Derivation.leibniz, smul_eq_mul, linear_partial L hL, mul_comm]
  ring

/-- On the quadratic component, a Hessian-kernel vector annihilates the
differential of the quadratic factor. -/
theorem kernel_annihilates_quadratic_differential (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (x u : Fin n → K) (hxQ : eval x Q = 0) (hxL : eval x L ≠ 0)
    (hu : (hessian (L*Q) x).mulVec u = 0) : dotProduct (gradient Q x) u = 0 := by
  have he := symmetric_dot_mulVec (hessian (L*Q) x) (hessian_symmetric (L*Q) x) x u
  rw [hu, hessian_mulVec_self (hL.mul hQ), gradient_linear_product L Q hL,
    hxQ, zero_smul, zero_add] at he
  have he' : 2 * eval x L * dotProduct (gradient Q x) u = 0 := by
    simpa [dotProduct, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc] using he
  exact (mul_eq_zero.mp he').resolve_left (mul_ne_zero (by norm_num) hxL)

/-- The linear-factor differential injects the Hessian kernel into the
one-dimensional base field at every point of the other component. -/
theorem kernel_and_linear_eq_zero (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (hdet : hessianDeterminantPolynomial (L*Q) ≠ 0)
    (x u : Fin n → K) (hxQ : eval x Q = 0) (hxL : eval x L ≠ 0)
    (hu : (hessian (L*Q) x).mulVec u = 0)
    (huL : dotProduct (linearCoefficient L) u = 0) : u = 0 := by
  have hg := kernel_annihilates_quadratic_differential L Q hL hQ x u hxQ hxL hu
  have hz : eval x L • (quadraticMatrix Q).mulVec u = 0 := by
    rw [hessian_linear_product L Q hL hQ] at hu
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, huL, hg] using hu
  exact common_radical_eq_zero L Q hL hQ hdet u
    ((smul_eq_zero.mp hz).resolve_left hxL) huL

/-- Dot product with a fixed coefficient vector, as an actual functional. -/
def coefficientFunctional (a : Fin n → K) : (Fin n → K) →ₗ[K] K where
  toFun u := dotProduct a u
  map_add' u v := by simp [dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by simp [dotProduct, ← Finset.mul_sum, mul_left_comm]

theorem rank_ge_n_sub_one_on_quadratic_factor (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (hdet : hessianDeterminantPolynomial (L*Q) ≠ 0)
    (x : Fin n → K) (hxQ : eval x Q = 0) (hxL : eval x L ≠ 0) :
    n - 1 ≤ (hessian (L*Q) x).rank := by
  let S := LinearMap.ker (hessian (L*Q) x).mulVecLin
  let f : S →ₗ[K] K := (coefficientFunctional (linearCoefficient L)).domRestrict S
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    apply Subtype.ext
    apply kernel_and_linear_eq_zero L Q hL hQ hdet x u hxQ hxL u.property
    exact hu
  have hdim : finrank K S ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  have hr := (hessian (L*Q) x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian (L*Q) x).rank + finrank K S = finrank K (Fin n → K) at hr
  simp only [Module.finrank_pi, Fintype.card_fin] at hr
  omega

/-- A cubic with a linear factor and nonzero Hessian determinant has no
intermediate Hessian ranks on its zero set. -/
theorem rank_dichotomy_on_linear_times_quadratic (L Q : MvPolynomial (Fin n) K)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (hdet : hessianDeterminantPolynomial (L*Q) ≠ 0)
    (x : Fin n → K) (hx : eval x (L*Q) = 0) :
    (hessian (L*Q) x).rank ≤ 2 ∨ n - 1 ≤ (hessian (L*Q) x).rank := by
  by_cases hxL : eval x L = 0
  · exact Or.inl (rank_le_two_on_linear_factor L Q hL hQ x hxL)
  · have hxQ : eval x Q = 0 := (mul_eq_zero.mp (by simpa using hx)).resolve_left hxL
    exact Or.inr (rank_ge_n_sub_one_on_quadratic_factor L Q hL hQ hdet x hxQ hxL)

end HessianTheorem11.ReducibleCubicRank
