import HessianTheorem11.SchurRank
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! The actual block matrix in the graded singular Hessian. An explicit
normal inverse and two computed identities turn its Schur complement into
a bordered Gram matrix. No normal matrix is inverted after this step. -/
noncomputable section
namespace HessianTheorem11.GradedSchurMatrix
open Matrix Module

variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]

def cross (J : Matrix τ σ K) (q : τ → K) : Matrix τ (σ ⊕ Unit) K :=
  Matrix.fromCols J (fun i _ => q i)

def rest (B : Matrix σ σ K) : Matrix (σ ⊕ Unit) (σ ⊕ Unit) K :=
  Matrix.fromBlocks B 0 0 0

def full (A : Matrix τ τ K) (B : Matrix σ σ K) (J : Matrix τ σ K) (q : τ → K) :
    Matrix (τ ⊕ (σ ⊕ Unit)) (τ ⊕ (σ ⊕ Unit)) K :=
  Matrix.fromBlocks A (cross J q) (cross J q).transpose (rest B)

theorem schur_eq_borderedGram
    (R : Matrix τ τ K) (hR : R.IsSymm)
    (B : Matrix σ σ K) (hB : B.IsSymm) (J : Matrix τ σ K) (q : τ → K)
    (S : Matrix σ σ K) (hS : S = B - J.transpose * R * J) (v : σ → K)
    (hcross : J.transpose.mulVec (R.mulVec q) = S.mulVec v)
    (hscalar : dotProduct q (R.mulVec q) = -dotProduct v (S.mulVec v)) :
    rest B - (cross J q).transpose * R * cross J q = SchurRank.borderedGram S v := by
  have hs : S.IsSymm := by
    change S.transpose = S
    rw [hS, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hR, hB, Matrix.mul_assoc]
  have hl (j : σ) : (∑ k, q k * ∑ l, R k l * J l j) =
      J.transpose.mulVec (R.mulVec q) j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [hR.apply]
    ring
  have hleft (j : σ) : Matrix.vecMul v S j = S.mulVec v j := by
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs.apply]
    ring
  rw [Matrix.mul_assoc]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := congrArg (fun M : Matrix σ σ K => M i j) hS.symm
      simpa only [cross, rest, SchurRank.borderedGram, Matrix.sub_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.mul_assoc, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.fromCols_apply_inl] using hh
    | inr j =>
      have hh := congrArg Neg.neg (congrFun hcross i)
      simpa only [cross, rest, SchurRank.borderedGram, Matrix.sub_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
        Matrix.zero_apply, zero_sub, Matrix.mulVec, dotProduct] using hh
  | inr i =>
    cases j with
    | inl j =>
      simp only [cross, rest, SchurRank.borderedGram, Matrix.sub_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
        Matrix.zero_apply, zero_sub]
      rw [hl, hcross, hleft]
    | inr j =>
      have hh := congrArg Neg.neg hscalar
      simpa only [cross, rest, SchurRank.borderedGram, Matrix.sub_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.fromCols_apply_inr, Matrix.zero_apply, zero_sub,
        Matrix.mulVec, dotProduct, neg_neg] using hh

theorem rank_full_le
    (A R : Matrix τ τ K) [DecidableEq τ] (hAR : A * R = 1) (hRA : R * A = 1)
    (hR : R.IsSymm) (B : Matrix σ σ K) (hB : B.IsSymm)
    (J : Matrix τ σ K) (q : τ → K)
    (S : Matrix σ σ K) (hS : S = B - J.transpose * R * J) (v : σ → K)
    (hcross : J.transpose.mulVec (R.mulVec q) = S.mulVec v)
    (hscalar : dotProduct q (R.mulVec q) = -dotProduct v (S.mulVec v)) :
    (full A B J q).rank ≤ Fintype.card τ + S.rank := by
  classical
  have hh := SchurRank.rank_le_schur_of_inverse A R (cross J q) (cross J q).transpose
    (rest B) hAR hRA
  rw [schur_eq_borderedGram R hR B hB J q S hS v hcross hscalar] at hh
  exact hh.trans (Nat.add_le_add A.rank_le_card_width (SchurRank.rank_borderedGram_le S v))

end HessianTheorem11.GradedSchurMatrix
