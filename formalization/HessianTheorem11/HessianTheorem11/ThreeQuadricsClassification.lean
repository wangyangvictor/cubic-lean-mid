import HessianTheorem11.FourQuadricsClassification

/-! Three independent quadrics satisfying an arbitrary nonsingular relation
are actual squares and products of two linear forms after a coordinate change. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial TangentHessianRank
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem three_quadrics_relation_normalization {σ : Type*}
    (A : Matrix (Fin 3) (Fin 3) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (p : Fin 3 → MvPolynomial σ K) (hrel : quadraticRelation A p = 0) :
    ∃ E : Matrix (Fin 3) (Fin 3) K, IsUnit E ∧
      combinePolynomials E p 0 * combinePolynomials E p 2 =
        combinePolynomials E p 1 ^ 2 := by
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
  let J : Matrix (Fin 3) (Fin 3) K := !![1,t,0; 0,0,t; 1,-t,0]
  have hJdet : J.det = -2 := by
    simp [J, Matrix.det_fin_three]
    linear_combination 2 * ht'
  have hJ : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr
    (isUnit_iff_ne_zero.mpr (by rw [hJdet]; norm_num))
  refine ⟨J * B⁻¹, hJ.mul (Matrix.isUnit_nonsing_inv_iff.mpr hB), ?_⟩
  rw [← combinePolynomials_comp]
  change combinePolynomials J q 0 * combinePolynomials J q 2 =
    combinePolynomials J q 1 ^ 2
  have htC : (C t : MvPolynomial σ K)^2 = -1 := by
    simpa using congrArg (C : K →+* MvPolynomial σ K) ht'
  simp [combinePolynomials_apply, J, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change q 0^2 + (q 1^2 + q 2^2) = 0 at hsum
  linear_combination hsum - (q 1^2 + q 2^2) * htC

theorem three_quadrics_linear_factorization {σ : Type*} [Fintype σ]
    (p : Fin 3 → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hlin : LinearIndependent K p)
    (A : Matrix (Fin 3) (Fin 3) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) :
    ∃ E : Matrix (Fin 3) (Fin 3) K, IsUnit E ∧
      ∃ c : K, c ≠ 0 ∧ ∃ u v : MvPolynomial σ K,
        u.IsHomogeneous 1 ∧ v.IsHomogeneous 1 ∧
        combinePolynomials E p 0 = C c * u^2 ∧
        combinePolynomials E p 1 = C c * u*v ∧
        combinePolynomials E p 2 = C c * v^2 := by
  obtain ⟨E,hE,hrelE⟩ := three_quadrics_relation_normalization A hA hdet p hrel
  refine ⟨E,hE,?_⟩
  exact QuadricLowRank.three_independent_quadrics (combinePolynomials E p)
    (combinePolynomials_homogeneous E p hp)
    (combinePolynomials_linearIndependent E hE p hlin) hrelE

end HessianTheorem11
