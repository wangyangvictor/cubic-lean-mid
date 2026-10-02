import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The actual differential of a kernel incidence and the dimension of
its second projection. These are purely linear-algebraic statements. -/

noncomputable section
namespace HessianTheorem11.TangentBundleLinearAlgebra
open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]

theorem finrank_comap_of_le_range (f : V →ₗ[K] W) (S : Submodule K W)
    (hS : S ≤ LinearMap.range f) :
    finrank K (S.comap f) = finrank K (LinearMap.ker f) + finrank K S := by
  let R := S.comap f
  have hkerR : LinearMap.ker f ≤ R := by
    intro v hv
    change f v ∈ S
    rw [LinearMap.mem_ker.mp hv]
    exact S.zero_mem
  have hrange : LinearMap.range (f.domRestrict R) = S := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hw
      obtain ⟨v, hv⟩ := hS hw
      exact ⟨⟨v, by change f v ∈ S; rwa [hv]⟩, hv⟩
  have hker : LinearMap.ker (f.domRestrict R) = (LinearMap.ker f).comap R.subtype := rfl
  have hd := (f.domRestrict R).finrank_range_add_finrank_ker
  rw [hrange, hker, (Submodule.comapSubtypeEquivOfLe hkerR).finrank_eq] at hd
  exact hd.symm.trans (Nat.add_comm _ _)

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- The actual linearized equations of a kernel family over tangent
directions T: the base variation is a∈T and H b + A a=0. -/
def incidenceTangent (H : E →ₗ[K] W) (A : V →ₗ[K] W) (T : Submodule K V) : Submodule K (V × E) :=
  T.comap (LinearMap.fst K V E) ⊓
    LinearMap.ker (H.comp (LinearMap.snd K V E) + A.comp (LinearMap.fst K V E))

theorem mem_incidenceTangent_iff (H : E →ₗ[K] W) (A : V →ₗ[K] W) (T : Submodule K V) (p : V × E) :
    p ∈ incidenceTangent H A T ↔ p.1 ∈ T ∧ H p.2 + A p.1 = 0 := Iff.rfl

def tangentProjection (H : E →ₗ[K] W) (A : V →ₗ[K] W) (T : Submodule K V) :
    incidenceTangent H A T →ₗ[K] E :=
  (LinearMap.snd K V E).domRestrict (incidenceTangent H A T)

theorem range_tangentProjection (H : E →ₗ[K] W) (A : V →ₗ[K] W) (T : Submodule K V) :
    LinearMap.range (tangentProjection H A T) = (T.map A).comap H := by
  ext b
  constructor
  · rintro ⟨p, rfl⟩
    have hp := (mem_incidenceTangent_iff H A T p).mp p.property
    change H (p : V × E).2 ∈ T.map A
    refine ⟨-(p : V × E).1, T.neg_mem hp.1, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hp.2).symm
  · intro hb
    obtain ⟨a, ha, hab⟩ : ∃ a ∈ T, A a = H b := hb
    refine ⟨⟨(-a, b), ?_⟩, rfl⟩
    rw [mem_incidenceTangent_iff]
    refine ⟨T.neg_mem ha, ?_⟩
    simp only [map_neg, ← hab, add_neg_cancel]

/-- The dimension of the actual projected tangent space is the tangent
kernel dimension plus the rank of the normal differential. -/
theorem finrank_range_tangentProjection (H A : V →ₗ[K] W)
    (hA : (LinearMap.ker H).map A ≤ LinearMap.range H) :
    finrank K (LinearMap.range (tangentProjection H A (LinearMap.ker H))) =
      finrank K (LinearMap.ker H) +
        finrank K (LinearMap.range (A.domRestrict (LinearMap.ker H))) := by
  rw [range_tangentProjection, finrank_comap_of_le_range H _ hA]
  congr 1
  rw [LinearMap.range_domRestrict]

end HessianTheorem11.TangentBundleLinearAlgebra
