import HessianTheorem11.ThreeQuadricsClassification

/-! A nonsingular quadratic relation in one or two coordinates forces
linear dependence. The proof factors the binary relation over the field. -/
noncomputable section
namespace HessianTheorem11
open Matrix MvPolynomial TangentHessianRank
variable {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem one_independent_no_quadratic_relation
    (p : Fin 1 → MvPolynomial σ K) (hlin : LinearIndependent K p)
    (A : Matrix (Fin 1) (Fin 1) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) : False := by
  obtain ⟨B,hB,hGram⟩ := exists_matrix_congruence_neg_one A hA hdet
  let q := combinePolynomials B⁻¹ p
  have hq : combinePolynomials B q = p := by
    rw [combinePolynomials_comp, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det B).mp hB), combinePolynomials_one]
  have he := quadraticRelation_combine A B q
  rw [hq,hGram,hrel,quadraticRelation_neg_one] at he
  have hz : q 0 = 0 := by
    simpa using he
  exact (combinePolynomials_linearIndependent B⁻¹
    (Matrix.isUnit_nonsing_inv_iff.mpr hB) p hlin).ne_zero 0 hz

theorem two_independent_no_quadratic_relation
    (p : Fin 2 → MvPolynomial σ K) (hlin : LinearIndependent K p)
    (A : Matrix (Fin 2) (Fin 2) K) (hA : A.IsSymm) (hdet : A.det ≠ 0)
    (hrel : quadraticRelation A p = 0) : False := by
  obtain ⟨B,hB,hGram⟩ := exists_matrix_congruence_neg_one A hA hdet
  let q := combinePolynomials B⁻¹ p
  have hq : combinePolynomials B q = p := by
    rw [combinePolynomials_comp, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det B).mp hB), combinePolynomials_one]
  have hli : LinearIndependent K q := combinePolynomials_linearIndependent B⁻¹
    (Matrix.isUnit_nonsing_inv_iff.mpr hB) p hlin
  have hsum : q 0 ^ 2 + q 1 ^ 2 = 0 := by
    have he := quadraticRelation_combine A B q
    rw [hq,hGram,hrel,quadraticRelation_neg_one] at he
    have hz := neg_eq_zero.mp he.symm
    simpa only [Fin.sum_univ_two] using hz
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_eq_mul_self (-1 : K)
  have ht' : t^2 = -1 := by simpa [pow_two] using ht.symm
  have htC : (C t : MvPolynomial σ K)^2 = -1 := by
    simpa using congrArg (C : K →+* MvPolynomial σ K) ht'
  have hprod : (q 0 - C t*q 1) * (q 0 + C t*q 1) = 0 := by
    linear_combination hsum - q 1^2 * htC
  have hn := (linearIndependent_fin2.mp hli).2
  rcases mul_eq_zero.mp hprod with hm | hp
  · exact hn t (by rw [MvPolynomial.smul_eq_C_mul]; exact (sub_eq_zero.mp hm).symm)
  · exact hn (-t) (by
      rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]
      exact (eq_neg_of_add_eq_zero_left hp).symm)

end HessianTheorem11
