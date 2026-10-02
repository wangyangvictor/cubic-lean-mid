import HessianTheorem11.WittQuadraticTuple
import HessianTheorem11.QuadraticCommonRadical

/-! Pairing the actual tuple with a Witt basis: radical and residual
normal coordinates vanish; regular coordinates are explicit linear combinations. -/
noncomputable section
namespace HessianTheorem11.WittQuadraticTuple
open Module Submodule MvPolynomial TangentHessianRank WittSubspaceBasis
variable {K σ τ : Type*} [Field K] [CharZero K] [Fintype σ] [Fintype τ] [DecidableEq τ]
variable {r l k : ℕ} {B : LinearMap.BilinForm K (τ → K)} {U : Submodule K (τ → K)}

theorem scalarTuple_regular_pairing (D : Data B U r l k)
    (p : τ → MvPolynomial σ K) (hmem : ∀ x, value p x ∈ U) (i : Fin r) :
    scalarTuple (B (D.basis (regularIndex i))) p =
      combinePolynomials (regularGram D) (regularTuple D p) i := by
  apply MvPolynomial.funext
  intro x
  rw [eval_scalarTuple,value_expansion D p hmem x]
  simp only [map_add,map_sum,map_smul,smul_eq_mul,regular_radical_pair_zero,
    mul_zero,Finset.sum_const_zero,add_zero,combinePolynomials_apply,map_mul,eval_C,regularGram]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem scalarTuple_radical_pairing (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hmem : ∀ x, value p x ∈ U) (i : Fin l) :
    scalarTuple (B (D.basis (radicalIndex i))) p = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_scalarTuple,value_expansion D p hmem x]
  have hr (j : Fin r) : B (D.basis (radicalIndex i)) (D.basis (regularIndex j)) = 0 := by
    rw [hB.eq]
    exact regular_radical_pair_zero D j i
  simp only [map_add,map_sum,map_smul,smul_eq_mul,hr,radical_pair_zero,
    mul_zero,Finset.sum_const_zero,add_zero,map_zero]

theorem scalarTuple_residual_pairing (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (hmem : ∀ x, value p x ∈ U) (i : Fin k) :
    scalarTuple (B (D.basis (residualIndex i))) p = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_scalarTuple,value_expansion D p hmem x]
  have hr (j : Fin r) : B (D.basis (residualIndex i)) (D.basis (regularIndex j)) = 0 := by
    rw [hB.eq]
    exact D.regular_orthogonal j (Sum.inr i)
  have hw (j : Fin l) : B (D.basis (residualIndex i)) (D.basis (radicalIndex j)) = 0 := by
    by_contra h
    have he := D.gram_weight _ _ h
    norm_num [weight,residualIndex,radicalIndex] at he
  simp only [map_add,map_sum,map_smul,smul_eq_mul,hr,hw,
    mul_zero,Finset.sum_const_zero,add_zero,map_zero]

variable {s : ℕ}

theorem pairing_differential_zero_outside_dual
    (D : Data B U 0 l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial (Fin s) K) (hmem : ∀ x, value p x ∈ U)
    (i : WittSubspaceBasis.Index 0 l k) (hi : WittSubspaceBasis.weight i ≠ 6)
    (x v : Fin s → K) : polynomialDifferential (scalarTuple (B (D.basis i)) p) x v = 0 := by
  rcases i with i | ((i | i) | i)
  · exact Fin.elim0 i
  · change polynomialDifferential (scalarTuple (B (D.basis (radicalIndex i))) p) x v = 0
    rw [scalarTuple_radical_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]
  · exact (hi rfl).elim
  · change polynomialDifferential (scalarTuple (B (D.basis (residualIndex i))) p) x v = 0
    rw [scalarTuple_residual_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]

theorem pairing_differential_zero_of_regular_radical
    (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial (Fin s) K) (hmem : ∀ x, value p x ∈ U)
    (i : WittSubspaceBasis.Index r l k) (hi : WittSubspaceBasis.weight i ≠ 6)
    (x v : Fin s → K)
    (hv : v ∈ polynomialTupleDifferentialRadical (regularTuple D p)) :
    polynomialDifferential (scalarTuple (B (D.basis i)) p) x v = 0 := by
  rcases i with i | ((i | i) | i)
  · change polynomialDifferential (scalarTuple (B (D.basis (regularIndex i))) p) x v = 0
    rw [scalarTuple_regular_pairing D p hmem i, polynomialDifferential_combine]
    have he := (mem_polynomialTupleDifferentialRadical (regularTuple D p) v).mp hv
    simp only [he,mul_zero,Finset.sum_const_zero]
  · change polynomialDifferential (scalarTuple (B (D.basis (radicalIndex i))) p) x v = 0
    rw [scalarTuple_radical_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]
  · exact (hi rfl).elim
  · change polynomialDifferential (scalarTuple (B (D.basis (residualIndex i))) p) x v = 0
    rw [scalarTuple_residual_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]

theorem pairing_differential_nonzero_weight
    (D : Data B U r l k) (hB : B.IsSymm)
    (p : τ → MvPolynomial (Fin s) K) (hmem : ∀ x, value p x ∈ U)
    (i : WittSubspaceBasis.Index r l k) (x v : Fin s → K)
    (hne : polynomialDifferential (scalarTuple (B (D.basis i)) p) x v ≠ 0) :
    WittSubspaceBasis.weight i = 4 ∨ WittSubspaceBasis.weight i = 6 := by
  rcases i with i | ((i | i) | i)
  · exact Or.inl rfl
  · apply False.elim
    apply hne
    change polynomialDifferential (scalarTuple (B (D.basis (radicalIndex i))) p) x v = 0
    rw [scalarTuple_radical_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]
  · exact Or.inr rfl
  · apply False.elim
    apply hne
    change polynomialDifferential (scalarTuple (B (D.basis (residualIndex i))) p) x v = 0
    rw [scalarTuple_residual_pairing D hB p hmem i]
    simp [polynomialDifferential_apply]

theorem polynomialDifferential_scalarTuple
    (L : (τ → K) →ₗ[K] K) (p : τ → MvPolynomial (Fin s) K) (a u : Fin s → K) :
    polynomialDifferential (scalarTuple L p) a u = L ((polynomialJacobian p a).mulVec u) := by
  classical
  have hL : L ((polynomialJacobian p a).mulVec u) =
      ∑ i, L ((Pi.basisFun K τ) i) * ((polynomialJacobian p a).mulVec u) i := by
    have he := eval_scalarTuple L
      (fun i => (C (((polynomialJacobian p a).mulVec u) i) : MvPolynomial (Fin s) K)) 0
    have hv : value (fun i => (C (((polynomialJacobian p a).mulVec u) i) :
        MvPolynomial (Fin s) K)) 0 = (polynomialJacobian p a).mulVec u := by
      funext i
      simp [value]
    rw [hv] at he
    simpa only [scalarTuple,map_sum,map_mul,eval_C] using he.symm
  rw [hL]
  simp only [polynomialDifferential_apply,scalarTuple,map_sum,
    Derivation.leibniz,smul_eq_mul,pderiv_C,zero_mul,zero_add,map_mul,eval_C,
    Finset.sum_mul,Finset.mul_sum,polynomialJacobian,Matrix.mulVec,dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_zero,add_zero,map_mul,eval_C]
  ring

end HessianTheorem11.WittQuadraticTuple
