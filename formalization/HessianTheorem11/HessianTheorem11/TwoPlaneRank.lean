import HessianTheorem11.QuadraticGenericRank

/-! A linear map of rank at most two has a two-vector slice preserving its
rank, with any prescribed vector whose image is nonzero as its first vector. -/
noncomputable section
namespace HessianTheorem11
open Matrix Module Submodule
variable {K : Type*} [Field K] {n m : ℕ}

def twoPlaneMatrix (u v : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  fun i j => ![u i, v i] j

theorem twoPlaneMatrix_mulVec (u v : Fin n → K) (a : Fin 2 → K) :
    (twoPlaneMatrix u v).mulVec a = a 0 • u + a 1 • v := by
  ext i
  simp [twoPlaneMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem mul_twoPlaneMatrix_col (A : Matrix (Fin m) (Fin n) K) (u v : Fin n → K) :
    (A * twoPlaneMatrix u v).col = ![A.mulVec u, A.mulVec v] := by
  ext j i
  fin_cases j <;> simp [Matrix.col, Matrix.mul_apply, twoPlaneMatrix, Matrix.mulVec,
    dotProduct]

theorem exists_twoPlane_preserving_rank (A : Matrix (Fin m) (Fin n) K)
    (x : Fin n → K) (hx : A.mulVec x ≠ 0) (hA : A.rank ≤ 2) :
    ∃ v, (A * twoPlaneMatrix x v).rank = A.rank := by
  classical
  have hspan : finrank K (K ∙ A.mulVec x) = 1 := finrank_span_singleton hx
  have hmem : A.mulVec x ∈ LinearMap.range A.mulVecLin := ⟨x,rfl⟩
  have hlow : 1 ≤ A.rank := by
    rw [← hspan]
    exact Submodule.finrank_mono (Submodule.span_le.mpr (by simpa using hmem))
  by_cases htwo : A.rank = 2
  · have hnot : ¬ LinearMap.range A.mulVecLin ≤ K ∙ A.mulVec x := by
      intro hh
      have hi := Submodule.finrank_mono hh
      change A.rank ≤ _ at hi
      omega
    obtain ⟨y, hy, hys⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨v, rfl⟩ := hy
    refine ⟨v, ?_⟩
    have hli : LinearIndependent K ![A.mulVec x, A.mulVec v] := by
      rw [LinearIndependent.pair_iff' hx]
      intro a ha
      apply hys
      change A.mulVec v ∈ K ∙ A.mulVec x
      rw [← ha]
      exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
    have hinj : Function.Injective (A * twoPlaneMatrix x v).mulVec := by
      rw [Matrix.mulVec_injective_iff, mul_twoPlaneMatrix_col]
      exact hli
    have he := LinearMap.finrank_range_of_inj
      (f := (A * twoPlaneMatrix x v).mulVecLin) hinj
    rw [htwo]
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      mul_one] using he
  · refine ⟨0, le_antisymm (Matrix.rank_mul_le_left _ _) ?_⟩
    have hle : K ∙ A.mulVec x ≤ LinearMap.range (A * twoPlaneMatrix x 0).mulVecLin := by
      apply Submodule.span_le.mpr
      intro y hy
      obtain rfl : y = A.mulVec x := Set.mem_singleton_iff.mp hy
      refine ⟨![1,0], ?_⟩
      change (A * twoPlaneMatrix x 0).mulVec ![1,0] = _
      rw [← Matrix.mulVec_mulVec, twoPlaneMatrix_mulVec]
      simp
    have hi := Submodule.finrank_mono hle
    rw [hspan] at hi
    change 1 ≤ (A * twoPlaneMatrix x 0).rank at hi
    omega

end HessianTheorem11
