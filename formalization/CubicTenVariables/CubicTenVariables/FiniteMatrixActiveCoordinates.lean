import CubicTenVariables.ReducedConeCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A rectangular matrix with at most three rows has an invertible coordinate
change leaving at most three active columns. The active set is enlarged to
exactly three when the ambient dimension is at least three. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteMatrixActiveCoordinates
open Matrix Module
variable {K : Type*} [Field K] {n m : ℕ}

theorem exists_coordinates (A : Matrix (Fin m) (Fin n) K) (hm : m ≤ 3) (hn : 3 ≤ n) :
    ∃ (B : Matrix (Fin n) (Fin n) K) (s : Finset (Fin n)),
      B.det ≠ 0 ∧ s.card = 3 ∧ ∀ i j, j ∉ s → (A * B) i j = 0 := by
  classical
  let W := LinearMap.ker A.mulVecLin
  let k := finrank K W
  have hk : k ≤ n := by
    simpa [k,W] using Submodule.finrank_le (LinearMap.ker A.mulVecLin)
  have hnk : n-k ≤ 3 := by
    have hdim := A.mulVecLin.finrank_range_add_finrank_ker
    have hr : finrank K (LinearMap.range A.mulVecLin) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range A.mulVecLin)
    simp only [Module.finrank_pi,Fintype.card_fin] at hdim
    change finrank K (LinearMap.range A.mulVecLin)+k=n at hdim
    omega
  obtain ⟨E,hE⟩ := ReducedConeCoordinates.exists_adapted_equiv W
  let ι := Fin k ⊕ Fin (n-k)
  let e : ι ≃ Fin n := finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))
  let L : (Fin n → K) ≃ₗ[K] (ι → K) :=
    E.trans (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (n-k)) K K).symm
  let P : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (LinearEquiv.piCongrLeft' K (fun _ : Fin n => K) e.symm).trans L.symm
  let B : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' P.toLinearMap
  have hB : B.det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det B).mp
      (Matrix.mulVec_injective_iff_isUnit.mp (by
        intro x y h
        apply P.injective
        simpa only [B,LinearMap.toMatrix'_mulVec] using h)) |>.ne_zero
  let s₀ : Finset (Fin n) := Finset.univ.image (fun j : Fin (n-k) => e (Sum.inr j))
  have hs₀ : s₀.card ≤ 3 :=
    (Finset.card_image_le).trans (by simpa using hnk)
  obtain ⟨s,hs,_,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s₀) hs₀ (by simpa using hn)
  refine ⟨B,s,hB,hcard,?_⟩
  intro i j hj
  have hj₀ : j ∉ s₀ := fun h => hj (hs h)
  have hproj : (E (P (Pi.single j 1))).2 = 0 := by
    have he : E (P (Pi.single j 1)) =
        (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (n-k)) K K)
          ((LinearEquiv.piCongrLeft' K (fun _ : Fin n => K) e.symm) (Pi.single j 1)) := by
      simp only [P,LinearEquiv.trans_apply,L,LinearEquiv.symm_trans_apply,
        LinearEquiv.apply_symm_apply,LinearEquiv.symm_symm]
      rfl
    rw [he]
    funext l
    change (Pi.single j (1 : K) : Fin n → K) (e (Sum.inr l)) = 0
    apply Pi.single_eq_of_ne
    intro h
    apply hj₀
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ l,h⟩
  have hker := (hE (P (Pi.single j 1))).mp hproj
  have hz : A.mulVec (P (Pi.single j 1)) = 0 := hker
  have hv : (A*B).mulVec (Pi.single j 1) = 0 := by
    simpa only [← Matrix.mulVec_mulVec,B,LinearMap.toMatrix'_mulVec] using hz
  have h := congrFun hv i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using h

end CubicTenVariables.FiniteMatrixActiveCoordinates
