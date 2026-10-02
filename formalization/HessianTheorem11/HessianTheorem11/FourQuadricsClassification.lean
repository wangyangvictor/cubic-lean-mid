import HessianTheorem11.BinaryQuadraticCoordinates
import HessianTheorem11.CliffordNormalization
import HessianTheorem11.TangentHessianRank

/-! Normalizing an arbitrary nonsingular four-coordinate quadratic relation
and applying polynomial unique factorization. All coordinate changes are
actual invertible matrices. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial TangentHessianRank
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

/-- An actual full orthonormal frame gives an invertible congruence. -/
theorem exists_matrix_congruence_neg_one [IsAlgClosed K] {m : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (hA : A.IsSymm) (hdet : A.det ≠ 0) :
    ∃ B : Matrix (Fin m) (Fin m) K, IsUnit B ∧ B.transpose * A * B = -1 := by
  classical
  have hr : A.rank = m := by
    simpa using Matrix.rank_of_isUnit A
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨v,hv⟩ := CliffordNormalization.exists_negative_orthonormal_frame A hA hr.ge
  let B : Matrix (Fin m) (Fin m) K := fun i j => v j i
  have hGram : B.transpose * A * B = -1 := by
    ext i j
    have he := hv i j
    simp only [Matrix.toBilin'_apply] at he
    simp only [Matrix.mul_apply, Matrix.transpose_apply, B, Finset.sum_mul]
    rw [Finset.sum_comm]
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using he
  have hB : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det B).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he := congrArg Matrix.det hGram
    simp [Matrix.det_mul, Matrix.det_transpose, hz, Matrix.det_neg] at he
    exact (pow_ne_zero m (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))) he.symm
  exact ⟨B,hB,hGram⟩

theorem quadraticRelation_eq_dot {r : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin r) K) (p : Fin r → MvPolynomial σ K) :
    quadraticRelation A p = dotProduct p ((A.map C).mulVec p) := by
  simp only [quadraticRelation, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadraticRelation_combine {r s : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin s) K)
    (p : Fin s → MvPolynomial σ K) :
    quadraticRelation A (combinePolynomials B p) =
      quadraticRelation (B.transpose * A * B) p := by
  rw [quadraticRelation_eq_dot, quadraticRelation_eq_dot]
  have ht : B.transpose.map (C : K →+* MvPolynomial σ K) = (B.map C).transpose := rfl
  simp only [combinePolynomials, Matrix.map_mul, ht,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem quadraticRelation_neg_one {r : ℕ} {σ : Type*}
    (p : Fin r → MvPolynomial σ K) :
    quadraticRelation (-1 : Matrix (Fin r) (Fin r) K) p = -(∑ i, p i ^ 2) := by
  simp [quadraticRelation, Matrix.one_apply, mul_ite, pow_two]

/-- An arbitrary nondegenerate relation on four independent quadrics can be
put into the literal determinant relation by an actual coordinate matrix. -/
theorem four_quadrics_relation_normalization [IsAlgClosed K] {σ : Type*}
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (p : Fin 4 → MvPolynomial σ K) (hrel : quadraticRelation A p = 0) :
    ∃ E : Matrix (Fin 4) (Fin 4) K, IsUnit E ∧
      combinePolynomials E p 0 * combinePolynomials E p 3 =
        combinePolynomials E p 1 * combinePolynomials E p 2 := by
  classical
  obtain ⟨B,hB,hGram⟩ := exists_matrix_congruence_neg_one A hA hdet
  let q := combinePolynomials B⁻¹ p
  have hq : combinePolynomials B q = p := by
    rw [combinePolynomials_comp, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det B).mp hB), combinePolynomials_one]
  have hsum : ∑ i, q i ^ 2 = 0 := by
    have he := quadraticRelation_combine A B q
    rw [hq,hGram,hrel,quadraticRelation_neg_one] at he
    exact neg_eq_zero.mp he.symm
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_eq_mul_self (-1 : K)
  have ht' : t^2 = -1 := by simpa [pow_two] using ht.symm
  let J : Matrix (Fin 4) (Fin 4) K :=
    !![1,t,0,0; 0,0,1,t; 0,0,-1,t; 1,-t,0,0]
  have hJdet : J.det = 4 := by
    simp [J, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply,
      Fin.succAbove]
    linear_combination -4 * ht'
  have hJ : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr
    (isUnit_iff_ne_zero.mpr (by rw [hJdet]; norm_num))
  refine ⟨J * B⁻¹, hJ.mul (Matrix.isUnit_nonsing_inv_iff.mpr hB), ?_⟩
  rw [← combinePolynomials_comp]
  change combinePolynomials J q 0 * combinePolynomials J q 3 =
    combinePolynomials J q 1 * combinePolynomials J q 2
  have htC : (C t : MvPolynomial σ K)^2 = -1 := by
    simpa using congrArg (C : K →+* MvPolynomial σ K) ht'
  simp [combinePolynomials_apply, J, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change q 0^2 + (q 1^2 + (q 2^2 + q 3^2)) = 0 at hsum
  linear_combination hsum - (q 1^2 + q 3^2) * htC

theorem four_quadrics_linear_factorization [IsAlgClosed K] {σ : Type*} [Fintype σ]
    (p : Fin 4 → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent K p)
    (A : Matrix (Fin 4) (Fin 4) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) :
    ∃ E : Matrix (Fin 4) (Fin 4) K, IsUnit E ∧
      ∃ u₁ u₂ v₁ v₂ : MvPolynomial σ K,
        u₁.IsHomogeneous 1 ∧ u₂.IsHomogeneous 1 ∧
        v₁.IsHomogeneous 1 ∧ v₂.IsHomogeneous 1 ∧
        combinePolynomials E p 0 = u₁ * v₁ ∧
        combinePolynomials E p 1 = u₁ * v₂ ∧
        combinePolynomials E p 2 = u₂ * v₁ ∧
        combinePolynomials E p 3 = u₂ * v₂ := by
  obtain ⟨E,hE,hrelE⟩ := four_quadrics_relation_normalization A hA hdet p hrel
  refine ⟨E,hE,?_⟩
  exact QuadricLowRank.four_independent_quadrics (combinePolynomials E p)
    (combinePolynomials_homogeneous E p hp)
    (combinePolynomials_linearIndependent E hE p hlin) hrelE

end HessianTheorem11
