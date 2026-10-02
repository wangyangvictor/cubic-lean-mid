import Mathlib.LinearAlgebra.Matrix.Symmetric
import HessianTheorem11.MatrixRankBounds
import HessianTheorem11.PolynomialSchurVanishing

/-! Rank bounds for a Hessian along a totally cubic-zero tangent space.
All matrix blocks and Jacobians in this module are actual linear maps. -/

noncomputable section
namespace HessianTheorem11.TangentHessianRank
open Matrix Module MvPolynomial

variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]

/-- A zero tangent-tangent block leaves at most the normal dimension plus
the rank of the normal-tangent block. No symmetry is needed. -/
theorem rank_zero_fromBlocks_le (B : Matrix σ τ K) (C : Matrix τ σ K)
    (D : Matrix τ τ K) :
    (Matrix.fromBlocks (0 : Matrix σ σ K) B C D).rank ≤ C.rank + Fintype.card τ := by
  classical
  let E : Matrix (σ ⊕ τ) τ K := Matrix.fromRows 0 1
  let P₁ : Matrix σ (σ ⊕ τ) K := Matrix.fromCols 1 0
  let P₂ : Matrix τ (σ ⊕ τ) K := Matrix.fromCols 0 1
  have he : Matrix.fromBlocks (0 : Matrix σ σ K) B C D =
      E * C * P₁ + Matrix.fromRows B D * P₂ := by
    dsimp [E, P₁, P₂]
    simp only [Matrix.fromRows_mul,
      Matrix.mul_fromCols, Matrix.zero_mul, Matrix.one_mul,
      Matrix.mul_zero, Matrix.mul_one]
    ext i j
    cases i <;> cases j <;> simp
  rw [he]
  have hC : (E * C * P₁).rank ≤ C.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hD : (Matrix.fromRows B D * P₂).rank ≤ Fintype.card τ :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.fromRows B D).rank_le_card_width
  exact (MatrixRankBounds.rank_add_le _ _).trans (Nat.add_le_add hC hD)

/-- A nonzero left-annihilator lowers the rank of a rectangular matrix. -/
theorem rank_lt_of_left_annihilator (J : Matrix τ σ K) (v : τ → K)
    (hv : v ≠ 0) (hJ : J.transpose.mulVec v = 0) : J.rank < Fintype.card τ := by
  have hk : 0 < finrank K (LinearMap.ker J.transpose.mulVecLin) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v, hJ⟩, ?_⟩
    intro he
    exact hv (congrArg Subtype.val he)
  have hd := J.transpose.mulVecLin.finrank_range_add_finrank_ker
  change J.transpose.rank + finrank K (LinearMap.ker J.transpose.mulVecLin) =
    finrank K (τ → K) at hd
  rw [Matrix.rank_transpose, Module.finrank_pi] at hd
  omega

/-- In normal dimension five, a nonzero annihilator of the normal
Jacobian gives full Hessian rank at most nine. -/
theorem rank_le_nine_of_normal_jacobian
    (B : Matrix σ (Fin 5) K) (J : Matrix (Fin 5) σ K)
    (D : Matrix (Fin 5) (Fin 5) K)
    (v : Fin 5 → K) (hv : v ≠ 0) (hJ : J.transpose.mulVec v = 0) :
    (Matrix.fromBlocks (0 : Matrix σ σ K) B J D).rank ≤ 9 := by
  have h₁ := rank_zero_fromBlocks_le B J D
  have h₂ := rank_lt_of_left_annihilator J v hv hJ
  simp only [Fintype.card_fin] at h₁ h₂
  omega

/-- The actual evaluated Jacobian of a polynomial tuple. -/
def polynomialJacobian (p : τ → MvPolynomial σ K) (x : σ → K) : Matrix τ σ K :=
  fun i j => eval x (pderiv j (p i))

/-- The polynomial obtained by substituting a tuple into a quadratic form. -/
def quadraticRelation (B : Matrix τ τ K) (p : τ → MvPolynomial σ K) :
    MvPolynomial σ K := ∑ i, ∑ j, C (B i j) * p i * p j

theorem eval_pderiv_quadraticRelation (B : Matrix τ τ K) (hB : B.IsSymm)
    (p : τ → MvPolynomial σ K) (x : σ → K) (k : σ) :
    eval x (pderiv k (quadraticRelation B p)) =
      2 * ((polynomialJacobian p x).transpose.mulVec (B.mulVec (fun i => eval x (p i)))) k := by
  classical
  simp only [quadraticRelation, map_sum, Derivation.leibniz, pderiv_C,
    smul_eq_mul, mul_zero, map_zero, add_zero, map_add, map_mul, eval_C,
    polynomialJacobian, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_add_distrib]
  have hs : (∑ i, ∑ j, eval x (p j) * (B i j * eval x (pderiv k (p i)))) =
      ∑ i, ∑ j, B i j * eval x (p i) * eval x (pderiv k (p j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.apply]
    ring
  have ht : (∑ i, eval x (pderiv k (p i)) * ∑ j, B i j * eval x (p j)) =
      ∑ i, ∑ j, B i j * eval x (p i) * eval x (pderiv k (p j)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.apply]
    ring
  rw [hs, ht]
  ring

theorem quadratic_relation_jacobian_annihilator [CharZero K]
    (B : Matrix τ τ K) (hB : B.IsSymm) (p : τ → MvPolynomial σ K)
    (hp : quadraticRelation B p = 0) (x : σ → K) :
    (polynomialJacobian p x).transpose.mulVec (B.mulVec (fun i => eval x (p i))) = 0 := by
  ext k
  have he := eval_pderiv_quadraticRelation B hB p x k
  rw [hp, map_zero, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- Away from the vertex of a nondegenerate quadratic cone, the actual
Jacobian of a polynomial map into that cone has a nonzero annihilator. -/
theorem rank_polynomialJacobian_lt [CharZero K] [DecidableEq τ]
    (B : Matrix τ τ K) (hB : B.IsSymm) (hdet : B.det ≠ 0)
    (p : τ → MvPolynomial σ K) (hp : quadraticRelation B p = 0)
    (x : σ → K) (hpx : (fun i => eval x (p i)) ≠ 0) :
    (polynomialJacobian p x).rank < Fintype.card τ := by
  apply rank_lt_of_left_annihilator _ (B.mulVec (fun i => eval x (p i)))
  · intro hz
    apply hpx
    have he := congrArg B⁻¹.mulVec hz
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec, Matrix.mulVec_zero] using he
  · exact quadratic_relation_jacobian_annihilator B hB p hp x

theorem rank_block_quadraticJacobian_lt [CharZero K] [DecidableEq τ]
    (Q : Matrix τ τ K) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (p : τ → MvPolynomial σ K) (hp : quadraticRelation Q p = 0)
    (x : σ → K) (hpx : (fun i => eval x (p i)) ≠ 0)
    (B : Matrix σ τ K) (D : Matrix τ τ K) :
    (Matrix.fromBlocks (0 : Matrix σ σ K) B (polynomialJacobian p x) D).rank <
      2 * Fintype.card τ := by
  have h₁ := rank_zero_fromBlocks_le B (polynomialJacobian p x) D
  have h₂ := rank_polynomialJacobian_lt Q hQ hdet p hp x hpx
  omega

theorem rank_block_five_quadrics_le_nine [CharZero K]
    (Q : Matrix (Fin 5) (Fin 5) K) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (p : Fin 5 → MvPolynomial σ K) (hp : quadraticRelation Q p = 0)
    (x : σ → K) (hpx : (fun i => eval x (p i)) ≠ 0)
    (B : Matrix σ (Fin 5) K) (D : Matrix (Fin 5) (Fin 5) K) :
    (Matrix.fromBlocks (0 : Matrix σ σ K) B (polynomialJacobian p x) D).rank ≤ 9 := by
  have h := rank_block_quadraticJacobian_lt Q hQ hdet p hp x hpx B D
  simp only [Fintype.card_fin] at h
  omega

/-- Restriction to the actual tangent coordinate subspace, setting every
normal coordinate equal to zero. -/
def tangentRestriction : MvPolynomial (σ ⊕ τ) K →ₐ[K] MvPolynomial σ K :=
  aeval (Sum.elim X (C ∘ (0 : τ → K)))

theorem tangentRestriction_pderiv (F : MvPolynomial (σ ⊕ τ) K) (i : σ) :
    tangentRestriction (pderiv (Sum.inl i) F) = pderiv i (tangentRestriction F) :=
  aeval_sumElim_pderiv_inl F 0 i

theorem eval_tangentRestriction (F : MvPolynomial (σ ⊕ τ) K) (x : σ → K) :
    eval x (tangentRestriction F) = eval (Sum.elim x (0 : τ → K)) F := by
  have he := aeval_sumElim (R := K) (S := K) (T := K) F (0 : τ → K) x
  simpa only [tangentRestriction, Algebra.algebraMap_self, RingHom.id_apply,
    Function.comp_def, MvPolynomial.aeval_eq_eval] using he.symm

/-- Actual normal first derivatives, restricted to the tangent subspace. -/
def normalGradient (F : MvPolynomial (σ ⊕ τ) K) : τ → MvPolynomial σ K :=
  fun i => tangentRestriction (pderiv (Sum.inr i) F)

def evaluatedHessian (F : MvPolynomial (σ ⊕ τ) K) (x : (σ ⊕ τ) → K) :
    Matrix (σ ⊕ τ) (σ ⊕ τ) K := fun i j => eval x (pderiv j (pderiv i F))

theorem tangent_hessian_zero (F : MvPolynomial (σ ⊕ τ) K)
    (hF : tangentRestriction F = 0) (x : σ → K) :
    (evaluatedHessian F (Sum.elim x (0 : τ → K))).toBlocks₁₁ = 0 := by
  ext i j
  change eval (Sum.elim x (0 : τ → K)) (pderiv (Sum.inl j) (pderiv (Sum.inl i) F)) = 0
  rw [← eval_tangentRestriction, tangentRestriction_pderiv, tangentRestriction_pderiv, hF]
  simp

theorem normal_tangent_hessian (F : MvPolynomial (σ ⊕ τ) K) (x : σ → K) :
    (evaluatedHessian F (Sum.elim x (0 : τ → K))).toBlocks₂₁ =
      polynomialJacobian (normalGradient F) x := by
  ext i j
  change eval (Sum.elim x (0 : τ → K)) (pderiv (Sum.inl j) (pderiv (Sum.inr i) F)) =
    eval x (pderiv j (tangentRestriction (pderiv (Sum.inr i) F)))
  rw [← eval_tangentRestriction, tangentRestriction_pderiv]

/-- The exact polynomial and its actual restricted normal derivatives
give the tangent-point rank bound directly, without a block certificate. -/
theorem tangent_hessian_rank_le (F : MvPolynomial (σ ⊕ τ) K)
    (hF : tangentRestriction F = 0) (x : σ → K) :
    (evaluatedHessian F (Sum.elim x (0 : τ → K))).rank ≤
      (polynomialJacobian (normalGradient F) x).rank + Fintype.card τ := by
  let H := evaluatedHessian F (Sum.elim x (0 : τ → K))
  have he := Matrix.fromBlocks_toBlocks H
  rw [tangent_hessian_zero F hF x, normal_tangent_hessian F x] at he
  change H.rank ≤ _
  rw [← he]
  exact rank_zero_fromBlocks_le _ _ _

theorem tangent_hessian_rank_le_nine [CharZero K]
    (F : MvPolynomial (σ ⊕ Fin 5) K) (hF : tangentRestriction F = 0)
    (Q : Matrix (Fin 5) (Fin 5) K) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hp : quadraticRelation Q (normalGradient F) = 0)
    (x : σ → K) (hx : (fun i => eval x (normalGradient F i)) ≠ 0) :
    (evaluatedHessian F (Sum.elim x (0 : Fin 5 → K))).rank ≤ 9 := by
  have h₁ := tangent_hessian_rank_le F hF x
  have h₂ := rank_polynomialJacobian_lt Q hQ hdet (normalGradient F) hp x hx
  simp only [Fintype.card_fin] at h₁ h₂
  omega

end HessianTheorem11.TangentHessianRank
