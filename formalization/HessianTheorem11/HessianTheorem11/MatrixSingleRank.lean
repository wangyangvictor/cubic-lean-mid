import HessianTheorem11.MatrixRankBounds
import Mathlib.Data.Matrix.Basis

/-! Activating a diagonal entry whose row and column were zero strictly
increases the actual matrix rank. -/
noncomputable section
namespace HessianTheorem11
open Matrix Module

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem rank_lt_add_single (A : Matrix ι ι K) (c : ι) (a : K)
    (hrow : ∀ j, A c j = 0) (hcol : ∀ i, A i c = 0) (ha : a ≠ 0) :
    A.rank < (A + Matrix.single c c a).rank := by
  let M := A + Matrix.single c c a
  have hec : A.mulVec (Pi.single c 1) = 0 := by
    ext i
    simpa only [Matrix.mulVec_single_one, Pi.zero_apply] using hcol i
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.range M.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    refine ⟨v - v c • (Pi.single c 1 : ι → K), ?_⟩
    change M.mulVec _ = A.mulVec v
    rw [show M = A + Matrix.single c c a from rfl, Matrix.add_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hec, smul_zero, sub_zero,
      Matrix.single_mulVec]
    simp
  have hm : (Pi.single c 1 : ι → K) ∈ LinearMap.range M.mulVecLin := by
    refine ⟨a⁻¹ • (Pi.single c 1 : ι → K), ?_⟩
    change M.mulVec _ = _
    rw [show M = A + Matrix.single c c a from rfl, Matrix.add_mulVec,
      Matrix.mulVec_smul, hec, smul_zero, zero_add, Matrix.single_mulVec]
    ext i
    by_cases hi : i = c
    · subst i
      simp [ha]
    · simp [hi, ha, Pi.single_apply]
  have ha : (Pi.single c 1 : ι → K) ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨v, hv⟩
    have h := congrFun hv c
    change A.mulVec v c = (Pi.single c 1 : ι → K) c at h
    simp [Matrix.mulVec, dotProduct, hrow] at h
  exact Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne hle (by intro he; rw [he] at ha; exact ha hm))

end HessianTheorem11
