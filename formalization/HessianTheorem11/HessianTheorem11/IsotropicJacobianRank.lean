import HessianTheorem11.TangentHessianRank
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.Funext

/-! The Gram matrix of a quadratic map into a nondegenerate quadric has
rank at most the normal dimension minus two away from the vertex. This is
an actual Jacobian calculation; dominance is a separate geometric step. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module

variable {K : Type*} [Field K]

theorem finrank_range_comp_lt_of_range_kernel
    {V W U : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U]
    (A : V →ₗ[K] W) (B : W →ₗ[K] U)
    (p : W) (hp : p ∈ LinearMap.range A) (hp0 : p ≠ 0) (hBp : B p = 0) :
    finrank K (LinearMap.range (B.comp A)) < finrank K (LinearMap.range A) := by
  let L := B.domRestrict (LinearMap.range A)
  have he : LinearMap.range L = LinearMap.range (B.comp A) := by
    ext u
    constructor
    · rintro ⟨⟨w, hw⟩, hwu⟩
      obtain ⟨v, rfl⟩ := hw
      exact ⟨v, hwu⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨A v, ⟨v,rfl⟩⟩,rfl⟩
  have hk : 0 < finrank K (LinearMap.ker L) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨⟨p,hp⟩,hBp⟩,?_⟩
    intro hh
    exact hp0 (congrArg (fun v : LinearMap.ker L => v.1.1) hh)
  have hd := L.finrank_range_add_finrank_ker
  rw [he] at hd
  omega

theorem rank_gram_lt_rank_of_isotropic_range
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (J : Matrix τ σ K) (B : Matrix τ τ K) (p : τ → K)
    (hp : p ∈ LinearMap.range J.mulVecLin) (hp0 : p ≠ 0)
    (hJ : J.transpose.mulVec (B.mulVec p) = 0) :
    (J.transpose * B * J).rank < J.rank := by
  classical
  have h := finrank_range_comp_lt_of_range_kernel J.mulVecLin
    (J.transpose * B).mulVecLin p hp hp0 (by
      change (J.transpose * B).mulVec p = 0
      rw [← Matrix.mulVec_mulVec]
      exact hJ)
  change finrank K (LinearMap.range (J.transpose * B * J).mulVecLin) <
    finrank K (LinearMap.range J.mulVecLin)
  rw [Matrix.mulVecLin_mul]
  exact h

theorem quadratic_value_mem_jacobian_range [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (p : τ → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (x : σ → K) : (fun i => eval x (p i)) ∈
      LinearMap.range (TangentHessianRank.polynomialJacobian p x).mulVecLin := by
  classical
  have he : (TangentHessianRank.polynomialJacobian p x).mulVec x =
      (2 : K) • (fun i => eval x (p i)) := by
    ext i
    have hh := congrArg (eval x) (hp i).sum_X_mul_pderiv
    simpa only [TangentHessianRank.polynomialJacobian, Matrix.mulVec, dotProduct,
      map_sum, map_mul, eval_X, map_nsmul, Pi.smul_apply, smul_eq_mul,
      two_nsmul, two_mul, mul_comm, map_add] using hh
  refine ⟨(2 : K)⁻¹ • x, ?_⟩
  change (TangentHessianRank.polynomialJacobian p x).mulVec _ = _
  rw [Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul]

theorem quadratic_jacobian_gram_rank_le [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (B : Matrix τ τ K) (hB : B.IsSymm) (hdet : B.det ≠ 0)
    (p : τ → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation B p = 0)
    (x : σ → K) (hpx : (fun i => eval x (p i)) ≠ 0) :
    ((TangentHessianRank.polynomialJacobian p x).transpose * B *
      TangentHessianRank.polynomialJacobian p x).rank ≤ Fintype.card τ - 2 := by
  have h₁ := rank_gram_lt_rank_of_isotropic_range
    (TangentHessianRank.polynomialJacobian p x) B (fun i => eval x (p i))
    (quadratic_value_mem_jacobian_range p hp x) hpx
    (TangentHessianRank.quadratic_relation_jacobian_annihilator B hB p hrel x)
  have h₂ := TangentHessianRank.rank_polynomialJacobian_lt B hB hdet p hrel x hpx
  omega

/-- The evaluated Hessian of an actual linear combination of the component
polynomials. -/
def normalCombination {σ τ : Type*} [Fintype τ]
    (p : τ → MvPolynomial σ K) (x : σ → K) (d : τ → K) : Matrix σ σ K :=
  fun i j => ∑ k, d k * eval x (pderiv j (pderiv i (p k)))

theorem quadratic_relation_first_polynomial [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (B : Matrix τ τ K) (hB : B.IsSymm) (p : τ → MvPolynomial σ K)
    (hrel : TangentHessianRank.quadraticRelation B p = 0) (k : σ) :
    (∑ i, pderiv k (p i) * ∑ j, C (B i j) * p j) = 0 := by
  apply MvPolynomial.funext
  intro x
  have hh := congrFun (TangentHessianRank.quadratic_relation_jacobian_annihilator
    B hB p hrel x) k
  simpa only [TangentHessianRank.polynomialJacobian, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul, eval_C, map_zero, Pi.zero_apply] using hh

/-- Twice differentiating the actual quadratic relation identifies the
normal Hessian combination with the negative Jacobian Gram matrix. -/
theorem normalCombination_at_pairing_value [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (B : Matrix τ τ K) (hB : B.IsSymm) (p : τ → MvPolynomial σ K)
    (hrel : TangentHessianRank.quadraticRelation B p = 0) (x : σ → K) :
    normalCombination p x (B.mulVec (fun i => eval x (p i))) =
      -((TangentHessianRank.polynomialJacobian p x).transpose * B *
        TangentHessianRank.polynomialJacobian p x) := by
  ext k l
  apply eq_neg_of_add_eq_zero_left
  have hh := congrArg (eval x) (congrArg (pderiv l)
    (quadratic_relation_first_polynomial B hB p hrel k))
  have he : normalCombination p x (B.mulVec (fun i => eval x (p i))) k l +
      ((TangentHessianRank.polynomialJacobian p x).transpose * B *
        TangentHessianRank.polynomialJacobian p x) k l =
      eval x (pderiv l (∑ i, pderiv k (p i) * ∑ j, C (B i j) * p j)) := by
    rw [Matrix.mul_assoc]
    simp only [normalCombination, TangentHessianRank.polynomialJacobian,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      map_sum, Derivation.leibniz, smul_eq_mul, pderiv_C, zero_mul, zero_add,
      map_add, map_mul, eval_C, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero, Finset.sum_add_distrib]
    ac_rfl
  exact he.trans (by simpa only [map_zero] using hh)

theorem normalCombination_rank_at_pairing_value [CharZero K]
    {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (B : Matrix τ τ K) (hB : B.IsSymm) (hdet : B.det ≠ 0)
    (p : τ → MvPolynomial σ K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (hrel : TangentHessianRank.quadraticRelation B p = 0)
    (x : σ → K) (hpx : (fun i => eval x (p i)) ≠ 0) :
    (normalCombination p x (B.mulVec (fun i => eval x (p i)))).rank ≤ Fintype.card τ - 2 := by
  have hn (M : Matrix σ σ K) : (-M).rank = M.rank := by
    have hl : (-M).mulVecLin = -M.mulVecLin := by
      ext v i
      simp [Matrix.mulVecLin_apply, Matrix.neg_mulVec]
    rw [Matrix.rank, Matrix.rank, hl, LinearMap.range_neg]
  rw [normalCombination_at_pairing_value B hB p hrel x, hn]
  exact quadratic_jacobian_gram_rank_le B hB hdet p hp hrel x hpx

end HessianTheorem11
