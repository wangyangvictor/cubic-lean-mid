import HessianTheorem11.MatrixRankMinors
import HessianTheorem11.KernelAnnihilatorGeometry

/-! Polynomial kernel generators on an actual nonvanishing maximal-minor
chart. These are elementary matrix identities over a field, with no geometric
input. They turn a successive annihilator into finitely many equations. -/
noncomputable section
namespace HessianTheorem11.KernelAnnihilatorProjector
open Matrix Module
set_option linter.unusedSectionVars false

variable {K α β : Type*} [Field K] [Fintype α] [Fintype β]

def insertion {R : Type*} [CommRing R] [DecidableEq β] {r : ℕ}
    (cols : Fin r → β) : Matrix β (Fin r) R :=
  fun j i => if j = cols i then 1 else 0

theorem mul_insertion [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (cols : Fin r → β) :
    M * insertion cols = M.submatrix id cols := by
  ext i j
  simp [Matrix.mul_apply, insertion]

theorem ker_eq_selected_rows [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) (hrank : M.rank ≤ r) :
    LinearMap.ker M.mulVecLin = LinearMap.ker (M.submatrix rows id).mulVecLin := by
  classical
  have hle : LinearMap.ker M.mulVecLin ≤
      LinearMap.ker (M.submatrix rows id).mulVecLin := by
    intro v hv
    change (M.submatrix rows id).mulVec v = 0
    ext i
    exact congrFun hv (rows i)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hsmall : r ≤ (M.submatrix rows id).rank := by
    simpa [Matrix.submatrix_submatrix] using
      MatrixRankMinors.minor_size_le_rank (M.submatrix rows id) id cols hdet
  have hlarge := PolynomialSchurVanishing.rank_submatrix_le M rows id
  have hdimM := M.mulVecLin.finrank_range_add_finrank_ker
  have hdimR := (M.submatrix rows id).mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at hdimM
  change (M.submatrix rows id).rank + _ = _ at hdimR
  omega

def projector {R : Type*} [CommRing R] [DecidableEq β] {r : ℕ}
    (M : Matrix α β R) (rows : Fin r → α) (cols : Fin r → β) : Matrix β β R :=
  (M.submatrix rows cols).det • 1 -
    insertion cols * (M.submatrix rows cols).adjugate * M.submatrix rows id

theorem projector_map {R S : Type*} [CommRing R] [CommRing S]
    [DecidableEq β] {r : ℕ} (f : R →+* S)
    (M : Matrix α β R) (rows : Fin r → α) (cols : Fin r → β) :
    (projector M rows cols).map f = projector (M.map f) rows cols := by
  classical
  have hinsert : (insertion (R := R) cols).map f = insertion (R := S) cols := by
    ext i j
    simp [insertion, Matrix.map_apply]
  have hdet := f.map_det (M.submatrix rows cols)
  have hadj := f.map_adjugate (M.submatrix rows cols)
  simp only [RingHom.mapMatrix_apply] at hdet hadj
  unfold projector
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, hinsert]
  simp only [← Matrix.submatrix_map, hadj]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [hdet]
  simp [Matrix.one_apply, Matrix.submatrix_map]
  all_goals first | rfl | exact f.map_sub

theorem selected_rows_mul_projector [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β) :
    M.submatrix rows id * projector M rows cols = 0 := by
  classical
  rw [projector, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_insertion]
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  rw [Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, sub_self]

theorem projector_mem_ker [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) (hrank : M.rank ≤ r)
    (v : β → K) : (projector M rows cols).mulVec v ∈ LinearMap.ker M.mulVecLin := by
  rw [ker_eq_selected_rows M rows cols hdet hrank]
  change (M.submatrix rows id).mulVec ((projector M rows cols).mulVec v) = 0
  rw [Matrix.mulVec_mulVec, selected_rows_mul_projector, Matrix.zero_mulVec]

theorem projector_on_ker [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β)
    (v : β → K) (hv : v ∈ LinearMap.ker M.mulVecLin) :
    (projector M rows cols).mulVec v = (M.submatrix rows cols).det • v := by
  classical
  have hrows : (M.submatrix rows id).mulVec v = 0 := by
    ext i
    exact congrFun hv (rows i)
  rw [projector, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hrows, Matrix.mulVec_zero, sub_zero]

theorem range_projector [DecidableEq β] {r : ℕ}
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) (hrank : M.rank ≤ r) :
    LinearMap.range (projector M rows cols).mulVecLin = LinearMap.ker M.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact projector_mem_ker M rows cols hdet hrank v
  · intro v hv
    refine ⟨(M.submatrix rows cols).det⁻¹ • v, ?_⟩
    change (projector M rows cols).mulVec ((M.submatrix rows cols).det⁻¹ • v) = v
    rw [Matrix.mulVec_smul, projector_on_ker M rows cols v hv,
      smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem annihilates_kernel_iff_columns [DecidableEq β] {r : ℕ}
    {V : Type*} [AddCommGroup V] [Module K V]
    (M : Matrix α β K) (rows : Fin r → α) (cols : Fin r → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) (hrank : M.rank ≤ r)
    (A : (β → K) →ₗ[K] V) :
    (∀ u ∈ LinearMap.ker M.mulVecLin, A u = 0) ↔
      ∀ j, A ((projector M rows cols).col j) = 0 := by
  change LinearMap.ker M.mulVecLin ≤ LinearMap.ker A ↔ _
  rw [← range_projector M rows cols hdet hrank, Matrix.range_mulVecLin,
    Submodule.span_le, Set.range_subset_iff]
  rfl

theorem successive_annihilator_iff_columns [DecidableEq β] {r : ℕ}
    {γ : Type*} [Fintype γ]
    (M : Matrix α β K) (N : (β → K) →ₗ[K] Matrix γ β K)
    (rows : Fin r → α) (cols : Fin r → β)
    (hdet : (M.submatrix rows cols).det ≠ 0) (hrank : M.rank ≤ r)
    (v : β → K) :
    (∀ u ∈ LinearMap.ker M.mulVecLin, (N u).mulVec v = 0) ↔
      ∀ j, (N ((projector M rows cols).col j)).mulVec v = 0 := by
  exact annihilates_kernel_iff_columns M rows cols hdet hrank
    (((Matrix.mulVecBilin K K).flip v).comp N)

end HessianTheorem11.KernelAnnihilatorProjector
