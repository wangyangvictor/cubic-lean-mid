import HessianTheorem11.ResolventCyclic
import HessianTheorem11.PolynomialMoments

/-! Removing the nonzero rank-one factor from all cyclic moments and
constructing the actual invariant isotropic space. -/
noncomputable section
namespace HessianTheorem11.ResolventCyclic
open Module Submodule PolynomialMoments
variable {K A V : Type*} [Field K] [CharZero K]
  [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
  [FiniteDimensional K A] [FiniteDimensional K V]

theorem moment_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (B : LinearMap.BilinForm K V) (T : Module.End K V)
    (v : V) (j : ℕ) :
    moment (BilinForm.toMatrix b B) (LinearMap.toMatrix b b T) (b.equivFun v) j =
      B v ((T^j) v) := by
  rw [moment,LinearMap.toMatrix_pow]
  rw [← Matrix.mulVec_mulVec]
  change dotProduct (b.repr v) ((BilinForm.toMatrix b B).mulVec
    ((LinearMap.toMatrix b b (T^j)).mulVec (b.repr v))) = _
  rw [LinearMap.toMatrix_mulVec_repr]
  exact (BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v ((T^j) v)).symm

theorem cancel_rank_one_factor
    (B : LinearMap.BilinForm K V) (M : A →ₗ[K] Module.End K V)
    (v : V) (l : A →ₗ[K] K) (hl : ∃ a, l a ≠ 0)
    (hm : ∀ a (j : ℕ), B (l a • v) (((M a)^j) (l a • v)) = 0) :
    ∀ a (j : ℕ), B v (((M a)^j) v) = 0 := by
  classical
  let ba := Module.finBasis K A
  let bv := Module.finBasis K V
  let M' := (LinearMap.toMatrix bv bv).toLinearMap.comp (M.comp ba.equivFun.symm.toLinearMap)
  let l' := l.comp ba.equivFun.symm.toLinearMap
  have hl' : ∃ a, l' a ≠ 0 := by
    obtain ⟨a,ha⟩ := hl
    exact ⟨ba.equivFun a,by simpa [l'] using ha⟩
  have hh := PolynomialMoments.cancel_linear_factor (BilinForm.toMatrix bv B) M'
    (bv.equivFun v) l' hl' (by
      intro a j
      have hs : l' a • bv.equivFun v = bv.equivFun (l' a • v) := by simp
      rw [hs]
      change moment (BilinForm.toMatrix bv B)
        (LinearMap.toMatrix bv bv (M (ba.equivFun.symm a)))
        (bv.equivFun (l' a • v)) j = 0
      rw [moment_toMatrix]
      exact hm (ba.equivFun.symm a) j)
  intro a j
  have h := hh (ba.equivFun a) j
  change moment (BilinForm.toMatrix bv B)
    (LinearMap.toMatrix bv bv (M (ba.equivFun.symm (ba.equivFun a))))
    (bv.equivFun v) j = 0 at h
  simpa only [LinearEquiv.symm_apply_apply,moment_toMatrix] using h

theorem rank_one_invariant_of_factor (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V = 4)
    (e : A →ₗ[K] V) (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v = B u (M a v))
    (v : V) (l : A →ₗ[K] K) (hl : ∃ a, l a ≠ 0) (he : ∀ a, e a=l a • v)
    (hm : ∀ a (j : ℕ), B (e a) (((M a)^j) (e a))=0) :
    ∃ W : Submodule K V, TotallyIsotropic B W ∧ finrank K W ≤ 2 ∧
      LinearMap.range e ≤ W ∧ ∀ a, Preserves (M a) W := by
  have hfixed := cancel_rank_one_factor B M v l hl (by simpa only [← he] using hm)
  have hW := firstSpan_isotropic B hB M hM v hfixed
  refine ⟨firstSpan M v,hW,isotropic_finrank_le_two B hB hn hd _ hW,?_,
    firstSpan_preserves B hB hn hd M hM v hfixed⟩
  rintro _ ⟨a,rfl⟩
  rw [he]
  exact (firstSpan M v).smul_mem _ (firstSpan_self M v)

theorem rank_one_factor (e : A →ₗ[K] V) (hr : finrank K (LinearMap.range e)=1) :
    ∃ (v : V) (l : A →ₗ[K] K), (∃ a, l a≠0) ∧ ∀ a, e a=l a • v := by
  classical
  let b := (Module.finBasis K (LinearMap.range e)).reindex (finCongr hr)
  let l := (b.coord (0 : Fin 1)).comp e.rangeRestrict
  refine ⟨b 0,l,?_,?_⟩
  · obtain ⟨a,ha⟩ := (b 0).property
    refine ⟨a,?_⟩
    have he : e.rangeRestrict a = b 0 := Subtype.ext ha
    simp [l,he]
  · intro a
    have hh := b.sum_repr (e.rangeRestrict a)
    have hh' : b.coord 0 (e.rangeRestrict a) • b 0 = e.rangeRestrict a := by
      simpa only [Fin.sum_univ_one,Basis.coord_apply] using hh
    exact (congrArg (fun x : LinearMap.range e => (x : V)) hh').symm

theorem rank_one_invariant (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V=4)
    (e : A →ₗ[K] V) (hr : finrank K (LinearMap.range e)=1)
    (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v=B u (M a v))
    (hm : ∀ a (j : ℕ), B (e a) (((M a)^j) (e a))=0) :
    ∃ W : Submodule K V, TotallyIsotropic B W ∧ finrank K W≤2 ∧
      LinearMap.range e≤W ∧ ∀ a, Preserves (M a) W := by
  obtain ⟨v,l,hl,he⟩ := rank_one_factor e hr
  exact rank_one_invariant_of_factor B hB hn hd e M hM v l hl he hm

end HessianTheorem11.ResolventCyclic
