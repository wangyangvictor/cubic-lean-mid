import HessianTheorem11.PolynomialSchurVanishing
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Actual nonvanishing minors witness rectangular matrix rank. The proof
selects independent spanning columns and then independent spanning rows. -/
noncomputable section
namespace HessianTheorem11.MatrixRankMinors
open Matrix Module

theorem exists_rank_minor {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (M : Matrix α β K) :
    ∃ (rows : Fin M.rank → α) (cols : Fin M.rank → β),
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨κ, c, hc, hspan, hli⟩ := exists_linearIndependent' K M.col
  letI : Fintype κ := Fintype.ofInjective c hc
  have hcard : Fintype.card κ = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let e : Fin M.rank ≃ κ :=
    (finCongr hcard.symm).trans (Fintype.equivFin κ).symm
  let cols : Fin M.rank → β := c ∘ e
  let N : Matrix α (Fin M.rank) K := M.submatrix id cols
  have hn : N.rank = M.rank := by
    have he : Set.range N.col = Set.range (M.col ∘ c) := by
      change Set.range ((M.col ∘ c) ∘ e) = Set.range (M.col ∘ c)
      apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro _ ⟨i, rfl⟩
        obtain ⟨j, rfl⟩ := e.surjective i
        exact ⟨j, rfl⟩
    calc
      N.rank = finrank K (Submodule.span K (Set.range N.col)) := Matrix.rank_eq_finrank_span_cols _
      _ = finrank K (Submodule.span K (Set.range M.col)) := by rw [he, hspan]
      _ = M.rank := (Matrix.rank_eq_finrank_span_cols _).symm
  obtain ⟨η, r, hr, hrspan, hrli⟩ := exists_linearIndependent' K N.row
  letI : Fintype η := Fintype.ofInjective r hr
  have hrcard : Fintype.card η = M.rank := by
    calc
      Fintype.card η = finrank K (Submodule.span K (Set.range (N.row ∘ r))) :=
        (finrank_span_eq_card hrli).symm
      _ = finrank K (Submodule.span K (Set.range N.row)) := by rw [hrspan]
      _ = N.rank := (Matrix.rank_eq_finrank_span_row _).symm
      _ = M.rank := hn
  let f : Fin M.rank ≃ η :=
    (finCongr hrcard.symm).trans (Fintype.equivFin η).symm
  let rows : Fin M.rank → α := r ∘ f
  have hminor : LinearIndependent K (M.submatrix rows cols).row := by
    exact hrli.comp f f.injective
  have hu : IsUnit (M.submatrix rows cols) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hminor
  exact ⟨rows, cols, isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)⟩

theorem rank_le_of_minors_vanish {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (M : Matrix α β K) (r : ℕ)
    (h : ∀ (k : ℕ), r < k → ∀ (rows : Fin k → α) (cols : Fin k → β),
      (M.submatrix rows cols).det = 0) : M.rank ≤ r := by
  by_contra hn
  obtain ⟨rows, cols, hdet⟩ := exists_rank_minor M
  exact hdet (h M.rank (lt_of_not_ge hn) rows cols)

theorem minor_size_le_rank {K α β : Type*} [Field K] [Fintype α] [Fintype β]
    (M : Matrix α β K) {k : ℕ} (rows : Fin k → α) (cols : Fin k → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) : k ≤ M.rank := by
  have hu : IsUnit (M.submatrix rows cols) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hr := PolynomialSchurVanishing.rank_submatrix_le M rows cols
  rw [Matrix.rank_of_isUnit _ hu] at hr
  simpa using hr

end HessianTheorem11.MatrixRankMinors
