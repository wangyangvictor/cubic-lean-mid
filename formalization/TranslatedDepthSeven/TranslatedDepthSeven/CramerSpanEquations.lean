import TranslatedDepthSeven.CramerHeight
import TranslatedDepthSeven.ProjectiveLinearHeightBound
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Explicit equations for the span of bounded integral vectors

Choose a nonsingular maximal minor of an integral row matrix.  Cramer's
rule then writes down, without Gaussian-elimination choices, one linear
equation for every nonpivot coordinate.  The resulting equation matrix
annihilates every original row and has independent rows.  This is the
elementary linear-algebra construction used to turn a tangent-packet span
into a literal rational projective linear section.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open Matrix

/-- The coordinates outside the image of a selected pivot embedding. -/
abbrev MatrixNonpivot {r N : ℕ} (J : Fin r ↪ Fin N) :=
  {j : Fin N // j ∉ Set.range J}

/-- The selected square pivot minor. -/
def selectedIntegralPivot {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N) :
    Matrix (Fin r) (Fin r) ℤ :=
  B.submatrix id J

/-- Cramer's-rule equations for the row span of `B`.  For a nonpivot
coordinate `l`, the equation is

`det(P) X_l - sum_k cramer(P, B_l)_k X_{J k}`.
-/
def cramerSpanEquationMatrix {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N) :
    Matrix (MatrixNonpivot J) (Fin N) ℤ :=
  fun l ↦
    (selectedIntegralPivot B J).det • Pi.single l.1 1 -
      ∑ k, ((selectedIntegralPivot B J).cramer (B.col l.1) k) •
        Pi.single (J k) 1

/-- On the nonpivot columns, the equation matrix is a scalar diagonal
matrix with scalar the selected determinant. -/
theorem cramerSpanEquationMatrix_apply_nonpivot {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (l u : MatrixNonpivot J) :
    cramerSpanEquationMatrix B J l u.1 =
      if l = u then (selectedIntegralPivot B J).det else 0 := by
  classical
  have hu : ∀ k, J k ≠ u.1 := by
    intro k hku
    exact u.2 ⟨k, hku⟩
  by_cases hlu : l = u
  · subst u
    simp [cramerSpanEquationMatrix, hu]
  · have hluval : l.1 ≠ u.1 := by
      intro h
      apply hlu
      exact Subtype.ext h
    simp [cramerSpanEquationMatrix, hu, hlu, hluval]

/-- Every original row satisfies every displayed Cramer equation. -/
theorem cramerSpanEquationMatrix_mulVec_row_eq_zero {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (i : Fin r) :
    cramerSpanEquationMatrix B J *ᵥ B.row i = 0 := by
  classical
  funext l
  let P := selectedIntegralPivot B J
  let b : Fin r → ℤ := B.col l.1
  have hcramer := congrFun (Matrix.mulVec_cramer P b) i
  change (cramerSpanEquationMatrix B J l) ⬝ᵥ B.row i = 0
  simp only [cramerSpanEquationMatrix, sub_dotProduct,
    sum_dotProduct, smul_dotProduct, single_dotProduct,
    one_mul, smul_eq_mul]
  change (selectedIntegralPivot B J).det * B i l.1 -
      ∑ k, (selectedIntegralPivot B J).cramer (B.col l.1) k *
        B i (J k) = 0
  rw [sub_eq_zero]
  simpa [P, b, selectedIntegralPivot, Matrix.mulVec, dotProduct,
    mul_comm] using hcramer.symm

/-- If the selected pivot determinant is nonzero, the Cramer equation rows
are linearly independent over `ℚ`. -/
theorem cramerSpanEquationMatrix_rows_linearIndependent {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    LinearIndependent ℚ
      (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg l
  have hcoordinate := congrFun hg l.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.row_apply, Matrix.map_apply,
    cramerSpanEquationMatrix_apply_nonpivot] at hcoordinate
  have hdetQ : ((selectedIntegralPivot B J).det : ℚ) ≠ 0 := by
    exact_mod_cast hdet
  simpa [hdetQ] using hcoordinate

/-- Consequently the equation matrix has full row rank. -/
theorem cramerSpanEquationMatrix_rank {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)).rank =
      Fintype.card (MatrixNonpivot J) := by
  exact (cramerSpanEquationMatrix_rows_linearIndependent B J hdet).rank_matrix

/-- The number of nonpivot coordinates is exactly `N-r`. -/
theorem card_matrixNonpivot {r N : ℕ} (J : Fin r ↪ Fin N) :
    Fintype.card (MatrixNonpivot J) = N - r := by
  classical
  have hrange : Fintype.card {j : Fin N // j ∈ Set.range J} = r := by
    calc
      Fintype.card {j : Fin N // j ∈ Set.range J} =
          Fintype.card (Fin r) :=
        (Fintype.card_congr (Equiv.ofInjective J J.injective)).symm
      _ = r := Fintype.card_fin r
  have hcompl := Fintype.card_subtype_compl
    (fun j : Fin N ↦ j ∈ Set.range J)
  rw [Fintype.card_fin, hrange] at hcompl
  omega

/-- A fixed finite reindexing of the nonpivot coordinates. -/
def matrixNonpivotEquivFin {r N : ℕ} (J : Fin r ↪ Fin N) :
    MatrixNonpivot J ≃ Fin (N - r) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using card_matrixNonpivot J)

/-- The Cramer equation matrix with its rows reindexed by a standard finite
ordinal, as required by the projective-height definition. -/
def cramerSpanEquationFinMatrix {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N) :
    Matrix (Fin (N - r)) (Fin N) ℤ :=
  (cramerSpanEquationMatrix B J).submatrix
    (matrixNonpivotEquivFin J).symm id

/-- Full row rank in the numerical codimension form. -/
theorem cramerSpanEquationMatrix_rank_eq_sub {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)).rank =
      N - r := by
  rw [cramerSpanEquationMatrix_rank B J hdet, card_matrixNonpivot J]

/-- Reindexing the Cramer equations by `Fin (N-r)` preserves their full
row rank. -/
theorem cramerSpanEquationFinMatrix_rank {r N : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    ((cramerSpanEquationFinMatrix B J).map ((↑) : ℤ → ℚ)).rank =
      N - r := by
  change (((cramerSpanEquationMatrix B J).map ((↑) : ℤ → ℚ)).submatrix
    (matrixNonpivotEquivFin J).symm (Equiv.refl (Fin N))).rank = N - r
  rw [Matrix.rank_submatrix]
  exact cramerSpanEquationMatrix_rank_eq_sub B J hdet

/-- If the original row matrix is entrywise bounded by `M`, then every
coefficient in its literal Cramer equation matrix has the same factorial
bound as an `r × r` determinant.  The pivot and nonpivot supports are
disjoint, so no extra factor from summing the Cramer coordinates is needed. -/
theorem cramerSpanEquationMatrix_entry_natAbs_le {r N M : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M)
    (l : MatrixNonpivot J) (j : Fin N) :
    (cramerSpanEquationMatrix B J l j).natAbs ≤
      r.factorial * M ^ r := by
  classical
  by_cases hj : j ∈ Set.range J
  · obtain ⟨k, rfl⟩ := hj
    have hl : J k ≠ l.1 := by
      intro hl
      exact l.2 ⟨k, hl⟩
    have hJ : ∀ u, J k = J u ↔ k = u := fun u ↦ J.injective.eq_iff
    simpa [cramerSpanEquationMatrix, Pi.single_apply, hl, hJ] using
      cramer_entry_natAbs_le_factorial_mul_pow
        (selectedIntegralPivot B J) (B.col l.1)
        (fun i u ↦ hB i (J u)) (fun i ↦ hB i l.1) k
  · have hJ : ∀ k, j ≠ J k := by
      intro k hkj
      exact hj ⟨k, hkj.symm⟩
    have hL : ∀ k, l.1 ≠ J k := by
      intro k hlk
      exact l.2 ⟨k, hlk.symm⟩
    by_cases hlj : j = l.1
    · simpa [cramerSpanEquationMatrix, Pi.single_apply, hJ, hL, hlj] using
        TangentPacketSpan.det_natAbs_le_factorial_mul_pow
          (selectedIntegralPivot B J) (fun i u ↦ hB i (J u))
    · simp [cramerSpanEquationMatrix, hJ, hlj]

/-- The projective linear space defined by the Cramer equations has an
explicit primitive Plücker-height bound. -/
theorem cramerSpanEquationMatrix_projectiveHeight_le {r N M : ℕ}
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M) :
    rationalProjectiveLinearHeight
        ((cramerSpanEquationFinMatrix B J).map ((↑) : ℤ → ℚ)) ≤
      (N - r).factorial * (r.factorial * M ^ r) ^ (N - r) := by
  exact rationalProjectiveLinearHeight_map_intCast_le
    (cramerSpanEquationFinMatrix B J) (by
      intro i j
      exact cramerSpanEquationMatrix_entry_natAbs_le B J hB
        ((matrixNonpivotEquivFin J).symm i) j)

/-- When the row span of `B` has codimension at least four, retain a fixed
four-row subsystem of its literal Cramer equations.  This is the homogeneous
codimension-four section used for a projective plane generated by three
independent rational vectors. -/
def fourRowCramerSpanEquationMatrix {r N : ℕ}
    (hfour : 4 ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) : Matrix (Fin 4) (Fin N) ℤ :=
  (cramerSpanEquationFinMatrix B J).submatrix (Fin.castLE hfour) id

/-- The retained four Cramer equations are independent whenever the selected
pivot minor is nonzero. -/
theorem fourRowCramerSpanEquationMatrix_rank {r N : ℕ}
    (hfour : 4 ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    ((fourRowCramerSpanEquationMatrix hfour B J).map
      ((↑) : ℤ → ℚ)).rank = 4 := by
  have hlinear : LinearIndependent ℚ
      ((fourRowCramerSpanEquationMatrix hfour B J).map
        ((↑) : ℤ → ℚ)).row := by
    have hfull : LinearIndependent ℚ
        ((cramerSpanEquationFinMatrix B J).map
          ((↑) : ℤ → ℚ)).row := by
      simpa [cramerSpanEquationFinMatrix] using
        (cramerSpanEquationMatrix_rows_linearIndependent B J hdet).comp
          (matrixNonpivotEquivFin J).symm
          (matrixNonpivotEquivFin J).symm.injective
    simpa [fourRowCramerSpanEquationMatrix] using
      hfull.comp (Fin.castLE hfour) (Fin.castLE_injective hfour)
  simpa using hlinear.rank_matrix

/-- Every original row of `B` satisfies the retained four equations. -/
theorem fourRowCramerSpanEquationMatrix_mulVec_row_eq_zero {r N : ℕ}
    (hfour : 4 ≤ N - r) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) (i : Fin r) :
    fourRowCramerSpanEquationMatrix hfour B J *ᵥ B.row i = 0 := by
  funext k
  have hk := congrFun (cramerSpanEquationMatrix_mulVec_row_eq_zero B J i)
    ((matrixNonpivotEquivFin J).symm (Fin.castLE hfour k))
  simpa [fourRowCramerSpanEquationMatrix, cramerSpanEquationFinMatrix,
    Matrix.mulVec, dotProduct] using hk

/-- The four-row subsystem has the sharper height bound obtained directly
from its four-by-four Pluecker minors, rather than from all `N-r` Cramer
rows. -/
theorem fourRowCramerSpanEquationMatrix_projectiveHeight_le
    {r N M : ℕ} (hfour : 4 ≤ N - r)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M) :
    rationalProjectiveLinearHeight
        ((fourRowCramerSpanEquationMatrix hfour B J).map
          ((↑) : ℤ → ℚ)) ≤
      Nat.factorial 4 * (r.factorial * M ^ r) ^ 4 := by
  apply rationalProjectiveLinearHeight_map_intCast_le
  intro i j
  exact cramerSpanEquationMatrix_entry_natAbs_le B J hB
    ((matrixNonpivotEquivFin J).symm (Fin.castLE hfour i)) j

end

end TranslatedDepthSeven
