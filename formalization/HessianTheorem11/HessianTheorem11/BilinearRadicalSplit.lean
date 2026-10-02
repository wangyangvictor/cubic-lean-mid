import HessianTheorem11.IsotropicDual

/-! The actual regular/radical decomposition of a subspace, followed by
its orthogonal complement in the ambient symmetric bilinear space. -/
noncomputable section
namespace HessianTheorem11.BilinearRadicalSplit
open Module Submodule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

structure Data (B : LinearMap.BilinForm K V) (U : Submodule K V) where
  regular : Submodule K V
  radical : Submodule K V
  regular_le : regular ≤ U
  radical_le : radical ≤ U
  sup_eq : regular ⊔ radical = U
  disjoint : Disjoint regular radical
  regular_nondegenerate : (B.restrict regular).Nondegenerate
  radical_orthogonal : ∀ r ∈ radical, ∀ u ∈ U, B r u = 0

theorem nonempty_data (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (U : Submodule K V) : Nonempty (Data B U) := by
  classical
  let R := LinearMap.ker (B.restrict U)
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl R
  have hBU : (B.restrict U).IsSymm := by
    constructor
    intro x y
    exact hB.eq x y
  have hn := HyperbolicBasis.restrict_nondegenerate_of_isCompl_kernel
    (B.restrict U) hBU C hC
  refine ⟨{
    regular := C.map U.subtype
    radical := R.map U.subtype
    regular_le := ?_
    radical_le := ?_
    sup_eq := ?_
    disjoint := ?_
    regular_nondegenerate := ?_
    radical_orthogonal := ?_ }⟩
  · rintro x ⟨c,hc,rfl⟩
    exact c.property
  · rintro x ⟨r,hr,rfl⟩
    exact r.property
  · rw [← Submodule.map_sup, sup_comm, hC.sup_eq_top]
    simp
  · apply Submodule.disjoint_def.mpr
    intro v hvC hvR
    obtain ⟨c,hc,hcv⟩ := hvC
    obtain ⟨r,hr,hrv⟩ := hvR
    have hcr : c = r := Subtype.ext (hcv.trans hrv.symm)
    have hcR : c ∈ R := hcr ▸ hr
    have hc0 := Submodule.disjoint_def.mp hC.disjoint c hcR hc
    simpa [hc0] using hcv.symm
  · intro v hv
    obtain ⟨c,hc,hcv⟩ := v.property
    have hc0 : (⟨c,hc⟩ : C) = 0 := by
      apply hn
      intro d
      have hd : U.subtype (d : U) ∈ C.map U.subtype := ⟨d,d.property,rfl⟩
      have he := hv ⟨U.subtype d,hd⟩
      change B (c : V) (d : V) = 0
      change B v.val (d : V) = 0 at he
      change (c : V) = v.val at hcv
      rw [hcv]
      exact he
    apply Subtype.ext
    rw [← hcv]
    exact congrArg (fun d : C => ((d : U) : V)) hc0
  · rintro r ⟨a,ha,rfl⟩ u hu
    exact congrArg (fun f : U →ₗ[K] K => f ⟨u,hu⟩) ha

theorem Data.radical_isotropic {B : LinearMap.BilinForm K V} {U : Submodule K V}
    (D : Data B U) : ∀ r ∈ D.radical, ∀ s ∈ D.radical, B r s = 0 :=
  fun r hr s hs => D.radical_orthogonal r hr s (D.radical_le hs)

theorem Data.isCompl_regular_orthogonal {B : LinearMap.BilinForm K V}
    {U : Submodule K V} (D : Data B U) (hB : B.IsSymm) :
    IsCompl D.regular (B.orthogonal D.regular) :=
  B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl D.regular_nondegenerate

theorem Data.radical_le_orthogonal {B : LinearMap.BilinForm K V}
    {U : Submodule K V} (D : Data B U) (hB : B.IsSymm) :
    D.radical ≤ B.orthogonal D.regular := by
  intro r hr u hu
  change B u r = 0
  rw [hB.eq]
  exact D.radical_orthogonal r hr u (D.regular_le hu)

end HessianTheorem11.BilinearRadicalSplit
