import TranslatedDepthSeven.IsolatedVertexQuotientSourceSectionHeight

/-!
# The source-section rank dichotomy

This file proves the elementary Gaussian-elimination statement isolated in
`IsolatedVertexQuotientSourceSectionHeight`.  The proof is carried out on
row families.  Restriction from `(x_0,x')` to `x'` preserves independence
for rows vanishing at a vector whose zeroth coordinate is nonzero.  In the
second branch, the three displayed eliminated rows are obtained from four
independent rows by elementary row operations and restriction.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix

set_option maxHeartbeats 3000000

/-- Delete the zeroth column of a rational matrix with thirteen columns. -/
def rationalMatrixDropFirstColumn {r : Type*}
    (A : Matrix r (Fin 13) ℚ) : Matrix r (Fin 12) ℚ :=
  fun i j ↦ A i j.succ

/-- Independent rows which all vanish at `(m,-b)`, with `m != 0`, remain
independent after deletion of the zeroth column. -/
theorem linearIndependent_dropFirstColumn_of_vertexRelation
    {r : Type*} [Fintype r]
    (A : Matrix r (Fin 13) ℚ)
    (hA : LinearIndependent ℚ A.row)
    (b : Fin 12 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : ∀ i,
      m * A i 0 = ∑ j, rationalMatrixDropFirstColumn A i j * b j) :
    LinearIndependent ℚ (rationalMatrixDropFirstColumn A).row := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  apply (Fintype.linearIndependent_iff.mp hA g) ?_ i
  funext j
  cases j using Fin.cases with
  | zero =>
      have hgcoord : ∀ k : Fin 12,
          ∑ i, g i * rationalMatrixDropFirstColumn A i k = 0 := by
        intro k
        have hk := congrFun hg k
        simpa [Matrix.row] using hk
      have hmul : m * ∑ i, g i * A i 0 = 0 := by
        calc
          m * ∑ i, g i * A i 0 =
              ∑ i, g i * (m * A i 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _hk
                ring
          _ = ∑ i, g i *
              (∑ k, rationalMatrixDropFirstColumn A i k * b k) := by
                apply Finset.sum_congr rfl
                intro k _hk
                rw [hvertex k]
          _ = ∑ k, (∑ i,
              g i * rationalMatrixDropFirstColumn A i k) * b k := by
                simp_rw [Finset.mul_sum, Finset.sum_mul]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro k _hk
                apply Finset.sum_congr rfl
                intro i _hi
                ring
          _ = 0 := by simp_rw [hgcoord]; simp
      have hzero : ∑ i, g i * A i 0 = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hm
      simpa [Matrix.row] using hzero
  | succ j =>
      have hj := congrFun hg j
      simpa [Matrix.row, rationalMatrixDropFirstColumn] using hj

/-- A four-row rational matrix of rank four has independent rows. -/
theorem linearIndependent_rows_of_rank_four
    (A : Matrix (Fin 4) (Fin 13) ℚ) (hA : A.rank = 4) :
    LinearIndependent ℚ A.row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank, ← A.rank_eq_finrank_span_row, hA]
  simp

/-- The integral vertex-evaluation identity after coefficient inclusion in
the rationals. -/
theorem integralQuotientSource_vertexRelation_rat
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ)
    (hvertex : integralQuotientSourceVertexEvaluation A b m = 0) :
    ∀ i,
      (m : ℚ) * (A i 0 : ℚ) =
        ∑ j, (integralQuotientSourceSpatialMatrix A i j : ℚ) *
          (b j : ℚ) := by
  intro i
  have hi : m * A i 0 -
      ∑ j, integralQuotientSourceSpatialMatrix A i j * b j = 0 := by
    simpa using congrFun hvertex i
  rw [sub_eq_zero] at hi
  exact_mod_cast hi

/-- Kernel proof of the previously isolated Gaussian-elimination input. -/
theorem standardLinearAlgebra_isolatedVertexQuotientSourceSectionRanks :
    StandardLinearAlgebra.IsolatedVertexQuotientSourceSectionRanks := by
  intro A b m hm hA
  let Aq : Matrix (Fin 4) (Fin 13) ℚ := A.map (Int.castRingHom ℚ)
  let S : Matrix (Fin 4) (Fin 12) ℚ :=
    (integralQuotientSourceSpatialMatrix A).map (Int.castRingHom ℚ)
  have hArows : LinearIndependent ℚ Aq.row :=
    linearIndependent_rows_of_rank_four Aq hA
  constructor
  · intro hvertex
    have hrelation : ∀ i,
        (m : ℚ) * Aq i 0 =
          ∑ j, rationalMatrixDropFirstColumn Aq i j * (b j : ℚ) := by
      intro i
      simpa [Aq, rationalMatrixDropFirstColumn,
        integralQuotientSourceSpatialMatrix] using
        integralQuotientSource_vertexRelation_rat A b m hvertex i
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have hSrows : LinearIndependent ℚ
        (rationalMatrixDropFirstColumn Aq).row :=
      linearIndependent_dropFirstColumn_of_vertexRelation
        Aq hArows (fun j ↦ (b j : ℚ)) (m : ℚ) hmQ hrelation
    have hSrank : S.rank = 4 := by
      have hSeq : S = rationalMatrixDropFirstColumn Aq := by
        rfl
      rw [hSeq]
      exact hSrows.rank_matrix
    have hmap :
        (matrixPrependZeroColumn
          (integralQuotientSourceSpatialMatrix A)).map
            (Int.castRingHom ℚ) = matrixPrependZeroColumn S := by
      funext i j
      cases j using Fin.cases <;>
        simp [matrixPrependZeroColumn, S]
    rw [integralQuotientSourceFourSectionMatrix, hmap,
      matrixPrependZeroColumn_rank]
    exact hSrank
  · intro i₀ hi₀
    let beta : Fin 4 → ℚ := fun i ↦
      (integralQuotientSourceVertexEvaluation A b m i : ℚ)
    have hbeta₀ : beta i₀ ≠ 0 := by
      dsimp [beta]
      exact_mod_cast hi₀
    let rowIndex : Fin 3 → Fin 4 :=
      fun k ↦ (finThreeEquivNonpivotRow i₀ k).1
    have hrowIndex : Function.Injective rowIndex := by
      intro k l hkl
      apply (finThreeEquivNonpivotRow i₀).injective
      apply Subtype.ext
      exact hkl
    have hrowIndex_ne : ∀ k, rowIndex k ≠ i₀ := by
      intro k
      exact (finThreeEquivNonpivotRow i₀ k).2
    let c : Fin 4 → ℚ := fun i ↦
      if i = i₀ then 0 else -(beta i / beta i₀)
    have hc₀ : c i₀ = 0 := by simp [c]
    let transformedRows : Fin 4 → (Fin 13 → ℚ) :=
      Aq.row + (c · • Aq.row i₀)
    have htransformed : LinearIndependent ℚ transformedRows := by
      exact (linearIndependent_add_smul_iff
        (v := Aq.row) hc₀).2 hArows
    have hsub : LinearIndependent ℚ
        (fun k ↦ transformedRows (rowIndex k)) :=
      htransformed.comp rowIndex hrowIndex
    let u : ℚˣ := Units.mk0 (beta i₀) hbeta₀
    have hscaled : LinearIndependent ℚ
        ((fun _k : Fin 3 ↦ u) •
          (fun k ↦ transformedRows (rowIndex k))) :=
      hsub.units_smul (fun _k : Fin 3 ↦ u)
    let T : Matrix (Fin 3) (Fin 13) ℚ := fun k j ↦
      beta i₀ * Aq (rowIndex k) j - beta (rowIndex k) * Aq i₀ j
    have hscaled_eq :
        ((fun _k : Fin 3 ↦ u) •
          (fun k ↦ transformedRows (rowIndex k))) = T.row := by
      funext k j
      have hk : rowIndex k ≠ i₀ := hrowIndex_ne k
      simp [T, transformedRows, c, rowIndex, u, hk,
        Matrix.row, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hTrows : LinearIndependent ℚ T.row := by
      rw [← hscaled_eq]
      exact hscaled
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have hTrelation : ∀ k,
        (m : ℚ) * T k 0 =
          ∑ j, rationalMatrixDropFirstColumn T k j * (b j : ℚ) := by
      intro k
      have hrow (i : Fin 4) :
          (m : ℚ) * Aq i 0 -
              ∑ j, rationalMatrixDropFirstColumn Aq i j * (b j : ℚ) =
            beta i := by
        simp [Aq, beta, rationalMatrixDropFirstColumn,
          integralQuotientSourceVertexEvaluation,
          integralQuotientSourceSpatialMatrix]
      have hsum :
          (∑ j, (beta i₀ * Aq (rowIndex k) j.succ -
              beta (rowIndex k) * Aq i₀ j.succ) * (b j : ℚ)) =
            beta i₀ * (∑ j, Aq (rowIndex k) j.succ * (b j : ℚ)) -
              beta (rowIndex k) * (∑ j, Aq i₀ j.succ * (b j : ℚ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      rw [← sub_eq_zero]
      calc
        (m : ℚ) * T k 0 -
            ∑ j, rationalMatrixDropFirstColumn T k j * (b j : ℚ) =
          beta i₀ * ((m : ℚ) * Aq (rowIndex k) 0 -
              ∑ j, rationalMatrixDropFirstColumn Aq (rowIndex k) j *
                (b j : ℚ)) -
            beta (rowIndex k) * ((m : ℚ) * Aq i₀ 0 -
              ∑ j, rationalMatrixDropFirstColumn Aq i₀ j *
                (b j : ℚ)) := by
                  simp only [T, rationalMatrixDropFirstColumn]
                  rw [hsum]
                  ring
        _ = beta i₀ * beta (rowIndex k) -
            beta (rowIndex k) * beta i₀ := by
              rw [hrow, hrow]
        _ = 0 := by ring
    have hEspatial : LinearIndependent ℚ
        (rationalMatrixDropFirstColumn T).row :=
      linearIndependent_dropFirstColumn_of_vertexRelation T hTrows
        (fun j ↦ (b j : ℚ)) (m : ℚ) hmQ hTrelation
    have hEeq :
        (integralQuotientSourceThreeEquationMatrix A b m i₀).map
            (Int.castRingHom ℚ) =
          rationalMatrixDropFirstColumn T := by
      funext k j
      simp [integralQuotientSourceThreeEquationMatrix,
        integralQuotientSourceSpatialMatrix, T, Aq, beta, rowIndex,
        rationalMatrixDropFirstColumn]
    have hErank :
        ((integralQuotientSourceThreeEquationMatrix A b m i₀).map
          (Int.castRingHom ℚ)).rank = 3 := by
      rw [hEeq]
      exact hEspatial.rank_matrix
    have hmap :
        (matrixPrependZeroColumn
          (integralQuotientSourceThreeEquationMatrix A b m i₀)).map
            (Int.castRingHom ℚ) =
          matrixPrependZeroColumn
            ((integralQuotientSourceThreeEquationMatrix A b m i₀).map
              (Int.castRingHom ℚ)) := by
      funext k j
      cases j using Fin.cases <;>
        simp [matrixPrependZeroColumn]
    rw [integralQuotientSourceThreeSectionMatrix, hmap,
      matrixPrependZeroColumn_rank]
    exact hErank

end

end TranslatedDepthSeven
