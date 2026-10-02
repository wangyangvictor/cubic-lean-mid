import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
namespace HessianTheorem11.MatrixRankBounds
open Matrix Module
variable {K σ τ υ : Type*} [Field K] [Fintype σ] [Fintype τ] [Fintype υ]

theorem rank_add_le (A B : Matrix σ τ K) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- Adding a block of rows and the same number of columns increases rank
by at most twice the block size. In particular one border adds at most two. -/
theorem rank_fromBlocks_le (A : Matrix σ σ K) (B : Matrix σ τ K)
    (C : Matrix τ σ K) (D : Matrix τ τ K) :
    (Matrix.fromBlocks A B C D).rank ≤ A.rank + 2 * Fintype.card τ := by
  classical
  let E₁ : Matrix (σ ⊕ τ) σ K := Matrix.fromRows 1 0
  let E₂ : Matrix (σ ⊕ τ) τ K := Matrix.fromRows 0 1
  let P₁ : Matrix σ (σ ⊕ τ) K := Matrix.fromCols 1 0
  let P₂ : Matrix τ (σ ⊕ τ) K := Matrix.fromCols 0 1
  have he : Matrix.fromBlocks A B C D =
      (E₁ * A * P₁ + E₁ * B * P₂) + E₂ * Matrix.fromCols C D := by
    dsimp [E₁, E₂, P₁, P₂]
    simp only [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero]
    ext i j
    cases i <;> cases j <;> simp
  rw [he]
  have hr := rank_add_le (E₁ * A * P₁ + E₁ * B * P₂) (E₂ * Matrix.fromCols C D)
  have hr' := rank_add_le (E₁ * A * P₁) (E₁ * B * P₂)
  have hA : (E₁ * A * P₁).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hB : (E₁ * B * P₂).rank ≤ Fintype.card τ :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
      B.rank_le_card_width
  have hC : (E₂ * Matrix.fromCols C D).rank ≤ Fintype.card τ :=
    (Matrix.rank_mul_le_left _ _).trans E₂.rank_le_card_width
  omega

end HessianTheorem11.MatrixRankBounds
