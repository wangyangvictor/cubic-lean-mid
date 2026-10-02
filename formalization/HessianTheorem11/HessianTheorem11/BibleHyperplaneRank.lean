import HessianTheorem11.SingularLinearAlgebra

/-! A matrix whose restriction to a hyperplane vanishes has rank at most
two. Neither symmetry nor algebraic-geometric input is required. -/
noncomputable section
namespace HessianTheorem11.BibleHyperplanes
open Module Matrix

theorem rank_le_two_of_hyperplane_restriction_zero
    {K : Type*} [Field K] {m : ℕ}
    (B : Matrix (Fin (m+1)) (Fin m) K) (hB : Function.Injective B.mulVec)
    (A : Matrix (Fin (m+1)) (Fin (m+1)) K)
    (hzero : B.transpose * A * B = 0) : A.rank ≤ 2 := by
  let T := LinearMap.range B.mulVecLin
  have hT : finrank K T = m := by
    rw [LinearMap.finrank_range_of_inj hB]
    simp
  have hBt : B.transpose.rank = m := by
    rw [rank_transpose]
    exact hT
  have hnull := B.transpose.mulVecLin.finrank_range_add_finrank_ker
  change B.transpose.rank + _ = finrank K (Fin (m+1) → K) at hnull
  rw [hBt, show finrank K (Fin (m+1) → K) = m+1 by simp] at hnull
  have hker : finrank K (LinearMap.ker B.transpose.mulVecLin) = 1 := by omega
  have hsub : LinearMap.range (A.mulVecLin.domRestrict T) ≤
      LinearMap.ker B.transpose.mulVecLin := by
    rintro _ ⟨u,rfl⟩
    obtain ⟨z,hz⟩ := u.property
    change B.transpose.mulVec (A.mulVec u.val) = 0
    rw [← hz]
    change B.transpose.mulVec (A.mulVec (B.mulVec z)) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  have hr : finrank K (LinearMap.range (A.mulVecLin.domRestrict T)) ≤ 1 :=
    (Submodule.finrank_mono hsub).trans_eq hker
  have hk := kernel_finrank_lower_of_restricted_rank A.mulVecLin T hr
  rw [hT] at hk
  have ha := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + _ = finrank K (Fin (m+1) → K) at ha
  rw [show finrank K (Fin (m+1) → K) = m+1 by simp] at ha
  omega

end HessianTheorem11.BibleHyperplanes
