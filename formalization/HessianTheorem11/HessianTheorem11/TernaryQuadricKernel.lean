import HessianTheorem11.TernaryQuadricRelations

set_option linter.unusedSimpArgs false
noncomputable section
namespace HessianTheorem11.TernaryQuadricKernel
open Matrix MvPolynomial
open scoped BigOperators
variable {K : Type*} [CommRing K]

def veroneseExponent : Fin 6 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 0 2, Finsupp.single 1 2, Finsupp.single 2 2,
    Finsupp.single 0 1 + Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 2 1]

def veronese : Fin 6 → MvPolynomial (Fin 3) K :=
  fun i => monomial (veroneseExponent i) 1

def matrixForm (M : Matrix (Fin 6) (Fin 6) K) : MvPolynomial (Fin 6) K :=
  ∑ i, ∑ j, C (M i j) * X i * X j

theorem bind_matrixForm (M : Matrix (Fin 6) (Fin 6) K) :
    bind₁ veronese (matrixForm M) =
      ∑ i, ∑ j, monomial (veroneseExponent i + veroneseExponent j) (M i j) := by
  simp only [matrixForm, map_sum, map_mul, bind₁_C_right, bind₁_X_right, veronese]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [C_mul_monomial, monomial_mul, mul_one]

section Field
variable {L : Type*} [Field L] [CharZero L]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 0 in
theorem matrix_eq_relationMatrix (M : Matrix (Fin 6) (Fin 6) L)
    (hM : M.transpose = M) (h : bind₁ veronese (matrixForm M) = 0) :
    M = TernaryQuadricRelations.relationMatrix
      (M 1 2) (M 0 2) (M 0 1) (-(M 2 3)/2) (-(M 1 4)/2) (-(M 0 5)/2) := by
  have hs (i j : Fin 6) : M j i = M i j :=
    congrArg (fun N : Matrix (Fin 6) (Fin 6) L => N i j) hM
  have hs10 := hs 0 1
  have hs20 := hs 0 2
  have hs30 := hs 0 3
  have hs40 := hs 0 4
  have hs50 := hs 0 5
  have hs21 := hs 1 2
  have hs31 := hs 1 3
  have hs41 := hs 1 4
  have hs51 := hs 1 5
  have hs32 := hs 2 3
  have hs42 := hs 2 4
  have hs52 := hs 2 5
  have hs43 := hs 3 4
  have hs53 := hs 3 5
  have hs54 := hs 4 5
  have h00 : M 0 0 = 0 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 4)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 0 = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h11 : M 1 1 = 0 := by
    have he := congrArg (coeff (Finsupp.single (1 : Fin 3) 4)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 1 1 = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h22 : M 2 2 = 0 := by
    have he := congrArg (coeff (Finsupp.single (2 : Fin 3) 4)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 2 2 = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h03 : M 0 3 = 0 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 3 + Finsupp.single (1 : Fin 3) 1)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 3 + (M 3 0) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h04 : M 0 4 = 0 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 3 + Finsupp.single (2 : Fin 3) 1)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 4 + (M 4 0) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h13 : M 1 3 = 0 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 3)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 1 3 + (M 3 1) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h15 : M 1 5 = 0 := by
    have he := congrArg (coeff (Finsupp.single (1 : Fin 3) 3 + Finsupp.single (2 : Fin 3) 1)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 1 5 + (M 5 1) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h24 : M 2 4 = 0 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 3)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 2 4 + (M 4 2) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h25 : M 2 5 = 0 := by
    have he := congrArg (coeff (Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 3)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 2 5 + (M 5 2) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h33 : M 3 3 = -2 * M 0 1 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 2 + Finsupp.single (1 : Fin 3) 2)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 1 + (M 1 0 + (M 3 3)) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h44 : M 4 4 = -2 * M 0 2 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 2 + Finsupp.single (2 : Fin 3) 2)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 2 + (M 2 0 + (M 4 4)) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h55 : M 5 5 = -2 * M 1 2 := by
    have he := congrArg (coeff (Finsupp.single (1 : Fin 3) 2 + Finsupp.single (2 : Fin 3) 2)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 1 2 + (M 2 1 + (M 5 5)) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination he
  have h34 : M 3 4 = -M 0 5 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 2 + Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 0 5 + (M 3 4 + (M 4 3 + (M 5 0))) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h35 : M 3 5 = -M 1 4 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 2 + Finsupp.single (2 : Fin 3) 1)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 1 4 + (M 3 5 + (M 4 1 + (M 5 3))) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  have h45 : M 4 5 = -M 2 3 := by
    have he := congrArg (coeff (Finsupp.single (0 : Fin 3) 1 + Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 2)) h
    rw [bind_matrixForm] at he
    simp only [Fin.sum_univ_succ, coeff_add, coeff_monomial, veroneseExponent,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.add_apply, Finsupp.single_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_succ] at he
    norm_num [Fin.succ] at he -- normalized
    change M 2 3 + (M 3 2 + (M 4 5 + (M 5 4))) = 0 at he
    try simp only [hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54] at he
    linear_combination (1/2 : L) * he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TernaryQuadricRelations.relationMatrix, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      hs10, hs20, hs30, hs40, hs50, hs21, hs31, hs41, hs51, hs32, hs42, hs52, hs43, hs53, hs54, h00, h11, h22, h03, h04, h13, h15, h24, h25, h33, h44, h55, h34, h35, h45] <;> ring

theorem matrix_rank_ne_five (M : Matrix (Fin 6) (Fin 6) L)
    (hM : M.transpose = M) (h : bind₁ veronese (matrixForm M) = 0) : M.rank ≠ 5 := by
  rw [matrix_eq_relationMatrix M hM h]
  exact TernaryQuadricRelations.relationMatrix_rank_ne_five _ _ _ _ _ _

end Field
end HessianTheorem11.TernaryQuadricKernel
