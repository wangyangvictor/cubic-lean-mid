import HessianTheorem11.MatrixRankBounds
import HessianTheorem11.Restriction
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Rank bounds for an actual Schur complement and a bordered Gram
matrix. These general matrix identities are the linear algebra in the
graded singular Hessian calculation. -/
noncomputable section
namespace HessianTheorem11.SchurRank
open Matrix Module

variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]

theorem rank_blockDiagonal_le (A : Matrix σ σ K) (D : Matrix τ τ K) :
    (Matrix.fromBlocks A 0 0 D).rank ≤ A.rank + D.rank := by
  classical
  let E : Matrix (σ ⊕ τ) σ K := Matrix.fromRows 1 0
  let F : Matrix (σ ⊕ τ) τ K := Matrix.fromRows 0 1
  have he : Matrix.fromBlocks A 0 0 D = E * A * E.transpose + F * D * F.transpose := by
    dsimp [E,F]
    simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero]
    ext i j
    cases i <;> cases j <;> simp
  rw [he]
  have ha : (E * A * E.transpose).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hd : (F * D * F.transpose).rank ≤ D.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  exact (MatrixRankBounds.rank_add_le _ _).trans (Nat.add_le_add ha hd)

theorem rank_le_schur [DecidableEq σ] [DecidableEq τ]
    (A : Matrix σ σ K) (B : Matrix σ τ K) (C : Matrix τ σ K)
    (D : Matrix τ τ K) [Invertible A] :
    (Matrix.fromBlocks A B C D).rank ≤ A.rank + (D - C * ⅟A * B).rank := by
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ A B C D]
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_blockDiagonal_le A _)

theorem rank_le_schur_of_inverse
    (A R : Matrix σ σ K) (B : Matrix σ τ K) (C : Matrix τ σ K)
    (D : Matrix τ τ K) [DecidableEq σ] [DecidableEq τ]
    (hAR : A * R = 1) (hRA : R * A = 1) :
    (Matrix.fromBlocks A B C D).rank ≤ A.rank + (D - C * R * B).rank := by
  have he : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks 1 0 (C * R) 1 * Matrix.fromBlocks A 0 0 (D - C * R * B) *
        Matrix.fromBlocks 1 (R * B) 0 1 := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      hRA, hAR]
    simp [Matrix.mul_assoc, hRA, hAR]
  rw [he]
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_blockDiagonal_le A _)

def borderedGram (B : Matrix σ σ K) (v : σ → K) :
    Matrix (σ ⊕ Unit) (σ ⊕ Unit) K :=
  Matrix.fromBlocks B (fun i _ => -(B.mulVec v) i)
    (fun _ j => -(Matrix.vecMul v B) j) (fun _ _ => dotProduct v (B.mulVec v))

theorem borderedGram_factor [DecidableEq σ] (B : Matrix σ σ K) (v : σ → K) :
    borderedGram B v =
      (Matrix.fromRows 1 (fun _ : Unit => -v) : Matrix (σ ⊕ Unit) σ K) * B *
      (Matrix.fromCols 1 (fun (i : σ) (_ : Unit) => -v i) : Matrix σ (σ ⊕ Unit) K) := by
  classical
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j => simp [borderedGram, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  | inr i =>
    cases j with
    | inl j => simp [borderedGram, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    | inr j =>
      simp only [borderedGram, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
        Pi.neg_apply, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem rank_borderedGram_le (B : Matrix σ σ K) (v : σ → K) :
    (borderedGram B v).rank ≤ B.rank := by
  classical
  rw [borderedGram_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end HessianTheorem11.SchurRank
