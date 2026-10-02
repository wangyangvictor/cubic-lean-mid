import HessianTheorem11.TwoPlaneRank
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section
namespace HessianTheorem11
open Matrix Module Submodule
variable {K : Type*} [Field K] {n m : ℕ}

def threePlaneMatrix (u v w : Fin n → K) : Matrix (Fin n) (Fin 3) K :=
  fun i j => ![u i, v i, w i] j

theorem threePlaneMatrix_mulVec (u v w : Fin n → K) (a : Fin 3 → K) :
    (threePlaneMatrix u v w).mulVec a = a 0 • u + a 1 • v + a 2 • w := by
  ext i
  simp [threePlaneMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm,
    add_assoc]

theorem mul_threePlaneMatrix_col (A : Matrix (Fin m) (Fin n) K)
    (u v w : Fin n → K) :
    (A * threePlaneMatrix u v w).col = ![A.mulVec u, A.mulVec v, A.mulVec w] := by
  ext j i
  fin_cases j <;> simp [Matrix.col, Matrix.mul_apply, threePlaneMatrix, Matrix.mulVec,
    dotProduct]

theorem exists_threePlane_preserving_rank (A : Matrix (Fin m) (Fin n) K)
    (x : Fin n → K) (hx : A.mulVec x ≠ 0) (hA : A.rank ≤ 3) :
    ∃ v w, (A * threePlaneMatrix x v w).rank = A.rank := by
  classical
  by_cases hthree : A.rank = 3
  · let y : LinearMap.range A.mulVecLin := ⟨A.mulVec x, x, rfl⟩
    have hy : y ≠ 0 := by intro h; exact hx (congrArg Subtype.val h)
    have hone : LinearIndependent K ![y] := LinearIndependent.of_subsingleton 0 hy
    obtain ⟨z, hz⟩ := exists_linearIndependent_snoc_of_lt_finrank hone
      (show 1 < finrank K (LinearMap.range A.mulVecLin) by change 1 < A.rank; omega)
    obtain ⟨s, hs⟩ := exists_linearIndependent_snoc_of_lt_finrank hz
      (show 2 < finrank K (LinearMap.range A.mulVecLin) by change 2 < A.rank; omega)
    obtain ⟨v, hv⟩ := z.property
    obtain ⟨w, hw⟩ := s.property
    refine ⟨v, w, ?_⟩
    have hli := hs.map' (LinearMap.range A.mulVecLin).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have he : (LinearMap.range A.mulVecLin).subtype ∘ Fin.snoc (Fin.snoc ![y] z) s =
        ![A.mulVec x, A.mulVec v, A.mulVec w] := by
      ext i
      fin_cases i <;> simp [Function.comp_def, Fin.snoc, y, ← hv, ← hw]
    rw [he] at hli
    have hinj : Function.Injective (A * threePlaneMatrix x v w).mulVec := by
      rw [Matrix.mulVec_injective_iff, mul_threePlaneMatrix_col]
      exact hli
    rw [hthree]
    have hd := LinearMap.finrank_range_of_inj
      (f := (A * threePlaneMatrix x v w).mulVecLin) hinj
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      mul_one] using hd
  · obtain ⟨v, hv⟩ := exists_twoPlane_preserving_rank A x hx (by omega)
    refine ⟨v, 0, le_antisymm (Matrix.rank_mul_le_left _ _) ?_⟩
    rw [← hv]
    apply Submodule.finrank_mono
    rintro y ⟨a, rfl⟩
    refine ⟨![a 0, a 1, 0], ?_⟩
    change (A * threePlaneMatrix x v 0).mulVec ![a 0,a 1,0] =
      (A * twoPlaneMatrix x v).mulVec a
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      threePlaneMatrix_mulVec, twoPlaneMatrix_mulVec]
    simp

end HessianTheorem11
