import HessianTheorem11.ResolventRankTwo

/-! Source Lemma 34.3, proved from actual self-adjoint endomorphisms and
resolvent moments. Every coordinate choice and coefficient comparison is
constructed; the scalar coefficient is a linear map on the actual kernel. -/
noncomputable section
namespace HessianTheorem11.ResolventAlternative
open Module Submodule ResolventCyclic
variable {K A V : Type*} [Field K] [CharZero K]
  [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
  [FiniteDimensional K A] [FiniteDimensional K V]

theorem linear_scalars_on_kernel (e : A →ₗ[K] V) (M : A →ₗ[K] Module.End K V)
    (hd : 0 < finrank K V)
    (h : ∀ z∈LinearMap.ker e, ∃ α : K, M z=α • LinearMap.id) :
    ∃ α : LinearMap.ker e →ₗ[K] K, ∀ z : LinearMap.ker e,
      M z=α z • LinearMap.id := by
  classical
  let b := Module.finBasis K V
  let i : Fin (finrank K V) := ⟨0,hd⟩
  let α : LinearMap.ker e →ₗ[K] K := {
    toFun := fun z => b.coord i (M z (b i))
    map_add' := by intro z w; simp
    map_smul' := by intro c z; simp }
  refine ⟨α,fun z => ?_⟩
  obtain ⟨c,hc⟩ := h z z.property
  have ha : α z=c := by
    change b.coord i (M z (b i))=c
    rw [hc]
    simp
  rw [ha]
  exact hc

/-- A nondegenerate four-dimensional symmetric space with a linear
self-adjoint family satisfying all actual resolvent moments has either a
common invariant isotropic space containing the image, or the scalar
kernel alternative. -/
theorem four_dimensional_alternative
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (hd : finrank K V=4) (e : A →ₗ[K] V) (M : A →ₗ[K] Module.End K V)
    (hM : ∀ a u v, B (M a u) v=B u (M a v))
    (hm : ∀ a (j : ℕ), B (e a) (((M a)^j) (e a))=0) :
    (∃ W : Submodule K V, TotallyIsotropic B W ∧ finrank K W≤2 ∧
      LinearMap.range e≤W ∧ ∀ a, Preserves (M a) W) ∨
    (finrank K (LinearMap.range e)=2 ∧
      ∃ α : LinearMap.ker e →ₗ[K] K, ∀ z : LinearMap.ker e,
        M z=α z • LinearMap.id) := by
  have hW := range_isotropic B hB e (by intro a; simpa using hm a 0)
  have hr := isotropic_finrank_le_two B hB hn hd (LinearMap.range e) hW
  have hcases : finrank K (LinearMap.range e)=0 ∨
      finrank K (LinearMap.range e)=1 ∨ finrank K (LinearMap.range e)=2 := by omega
  rcases hcases with h0 | h1 | h2
  · have he : LinearMap.range e=⊥ := Submodule.finrank_eq_zero.mp h0
    left
    refine ⟨⊥,?_,by simp,he.le,?_⟩
    · intro u hu v hv
      have hu0 : u=0 := hu
      simp [hu0]
    · intro a v hv
      have hv0 : v=0 := hv
      simp [hv0]
  · exact Or.inl (rank_one_invariant B hB hn hd e h1 M hM hm)
  · rcases rank_two_alternative B hB hn hd e h2 M hM hm with hi | hs
    · exact Or.inl ⟨LinearMap.range e,hW,hr,le_rfl,hi⟩
    · exact Or.inr ⟨h2,linear_scalars_on_kernel e M (by omega) hs⟩

end HessianTheorem11.ResolventAlternative
