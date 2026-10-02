import HessianTheorem11.IsotropicPlaneCoordinates
import HessianTheorem11.ResolventRankOne

/-! The rank-two branch of the four-dimensional resolvent alternative,
using an actually constructed Witt basis and lift of range coordinates. -/
noncomputable section
set_option maxRecDepth 4000
namespace HessianTheorem11.ResolventCyclic
open Module Submodule Matrix PolynomialMoments TwoByTwoResolvent IsotropicPlaneCoordinates
variable {K A V : Type*} [Field K] [CharZero K]
  [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem rank_two_alternative (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V=4)
    (e : A →ₗ[K] V) (hr : finrank K (LinearMap.range e)=2)
    (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v=B u (M a v))
    (hm : ∀ a (j : ℕ), B (e a) (((M a)^j) (e a))=0) :
    (∀ a, Preserves (M a) (LinearMap.range e)) ∨
      (∀ z∈LinearMap.ker e, ∃ α : K, M z=α • LinearMap.id) := by
  classical
  have hW := range_isotropic B hB e (by intro a; simpa using hm a 0)
  obtain ⟨D⟩ := IsotropicPlaneCoordinates.exists_data B hB hn hd (LinearMap.range e) hW hr
  obtain ⟨L,hL⟩ := IsotropicPlaneCoordinates.exists_lift e D
  let am := (D.blockMap Sum.inl Sum.inl).comp M
  let bm := (D.blockMap Sum.inl Sum.inr).comp M
  let cm := (D.blockMap Sum.inr Sum.inl).comp M
  let aa := am.comp L
  let bb := bm.comp L
  let cc := cm.comp L
  have hsymC (u) : (cc u).IsSymm := (D.selfAdjoint_blocks hB (M (L u)) (hM (L u))).2.2
  have hpoint (z : A) (hz : z∈LinearMap.ker e) (u : Vec K) (t : K) (j : ℕ) :
      moment gram (block (aa u+t • am z) (bb u+t • bm z) (cc u+t • cm z)) (embed u) j=0 := by
    have he : e (L u+t • z)=D.leftMap u := by
      have hze : e z=0 := hz
      simp [hze,hL]
    have hvec : D.basis.equivFun (e (L u+t • z))=embed u := by
      rw [he,leftMap_eq,LinearEquiv.apply_symm_apply]
    have hmat := (D.selfAdjoint_blocks hB (M (L u+t • z)) (hM (L u+t • z))).1
    have h := hm (L u+t • z) j
    rw [← moment_toMatrix D.basis B (M (L u+t • z)),D.gram_eq,hvec,hmat] at h
    simpa only [map_add,map_smul,LinearMap.comp_apply] using h
  have hkernel (z : A) (hz : z∈LinearMap.ker e) : cm z=0 := by
    exact kernelC_zero aa bb cc (am z) (bm z) (cm z)
      (D.selfAdjoint_blocks hB (M z) (hM z)).2.2
      (fun u t => hpoint z hz u t 1)
  by_cases hc : cc=0
  · left
    intro a
    apply D.preserves_of_lower_zero (M a)
    let u : Vec K := fun i => D.basis.equivFun (e a) (Sum.inl i)
    have hea : D.leftMap u=e a := D.leftMap_coordinates (e a) (LinearMap.mem_range_self e a)
    have hz : a-L u∈LinearMap.ker e := by
      change e (a-L u)=0
      rw [map_sub,hL,hea,sub_self]
    have hcm : cm a=0 := by
      have h := hkernel (a-L u) hz
      have hl : cm (L u)=0 := by
        change cc u=0
        rw [hc]; rfl
      simpa only [map_sub,hl,sub_zero] using h
    exact hcm
  · right
    intro z hz
    obtain ⟨α,ha⟩ := kernel_block_scalar aa bb cc hsymC hc (am z) (bm z) (cm z)
      (D.selfAdjoint_blocks hB (M z) (hM z)).2.1
      (D.selfAdjoint_blocks hB (M z) (hM z)).2.2 (hpoint z hz)
    refine ⟨α,?_⟩
    apply (LinearMap.toMatrix D.basis D.basis).injective
    rw [map_smul,LinearMap.toMatrix_id]
    rw [(D.selfAdjoint_blocks hB (M z) (hM z)).1]
    exact ha

end HessianTheorem11.ResolventCyclic
