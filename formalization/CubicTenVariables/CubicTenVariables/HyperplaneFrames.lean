import CubicTenVariables.TerminalSectionIncidence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Every nonzero normal has an actual injective frame with precisely its
hyperplane as image, over any field. Thus statements uniform in all frames
apply to every hyperplane normal, including in positive characteristic. -/

noncomputable section
namespace CubicTenVariables.HyperplaneFrames
open Module Matrix TerminalSectionIncidence
variable {K : Type*} [Field K] {n : ℕ}

theorem normalFunctional_surjective (v : Fin (n+1) → K) (hv : v ≠ 0) :
    Function.Surjective (normalFunctional v) := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  intro c
  refine ⟨Pi.single k (c / v k),?_⟩
  change dotProduct v (Pi.single k (c / v k))=c
  simp only [dotProduct_single]
  field_simp

theorem hyperplane_finrank (v : Fin (n+1) → K) (hv : v ≠ 0) :
    finrank K (hyperplane v) = n := by
  have h := (normalFunctional v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (normalFunctional_surjective v hv)] at h
  simp only [finrank_top,finrank_self,Module.finrank_pi,Fintype.card_fin] at h
  change 1 + finrank K (hyperplane v) = n+1 at h
  omega

/-- No basis, coordinate-chart or nonvanishing-minor choice is assumed. -/
theorem exists_frame (v : Fin (n+1) → K) (hv : v ≠ 0) :
    ∃ B : Matrix (Fin (n+1)) (Fin n) K,
      Function.Injective B.mulVec ∧ LinearMap.range B.mulVecLin = hyperplane v := by
  let H := hyperplane v
  have hd : finrank K H=n := hyperplane_finrank v hv
  let e : H ≃ₗ[K] (Fin n → K) :=
    ((Module.finBasis K H).reindex (finCongr hd)).equivFun
  let L : (Fin n → K) →ₗ[K] (Fin (n+1) → K) := H.subtype.comp e.symm.toLinearMap
  let B := LinearMap.toMatrix' L
  have hB : B.mulVec = L := by
    funext x
    exact LinearMap.toMatrix'_mulVec L x
  have hBL : B.mulVecLin=L := by
    apply LinearMap.ext
    intro x
    exact congrFun hB x
  refine ⟨B,?_,?_⟩
  · rw [hB]
    exact H.subtype_injective.comp e.symm.injective
  · rw [hBL]
    apply le_antisymm
    · rintro x ⟨y,rfl⟩
      exact (e.symm y).property
    · intro x hx
      exact ⟨e ⟨x,hx⟩,congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)⟩

end CubicTenVariables.HyperplaneFrames
