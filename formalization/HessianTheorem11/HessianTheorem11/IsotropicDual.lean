import HessianTheorem11.HyperbolicBasis
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! An actual isotropic dual family for any totally isotropic subspace of
a finite-dimensional nondegenerate symmetric bilinear space. -/
noncomputable section
namespace HessianTheorem11.IsotropicDual
open Module Submodule
open scoped BigOperators
variable {K V ι : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype ι] [DecidableEq ι]

theorem exists_dual_family (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (W : Submodule K V)
    (hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0) (b : Basis ι K W) :
    ∃ z : ι → V, (∀ i j, B (b i : V) (z j) = if i = j then 1 else 0) ∧
      ∀ i j, B (z i) (z j) = 0 := by
  classical
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl W
  let f : ι → Module.Dual K V := fun i =>
    (b.coord i).comp (W.linearProjOfIsCompl C hC)
  let y : ι → V := fun i => (B.toDual hn).symm (f i)
  have hyw (i j : ι) : B (y i) (b j : V) = if j = i then 1 else 0 := by
    simp [y, f, LinearMap.BilinForm.apply_toDual_symm_apply,
      Submodule.linearProjOfIsCompl_apply_left, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply]
  have hwy (i j : ι) : B (b i : V) (y j) = if i = j then 1 else 0 := by
    rw [hB.eq, hyw]
  let c : ι → V := fun i => (1/2 : K) • ∑ j, B (y i) (y j) • (b j : V)
  have hcW (i : ι) : c i ∈ W := by
    apply W.smul_mem
    apply W.sum_mem
    intro j hj
    exact W.smul_mem _ (b j).property
  have hwc (i j : ι) : B (b i : V) (c j) = 0 := hW _ (b i).property _ (hcW j)
  have hcy (i j : ι) : B (c i) (y j) = (1/2 : K) * B (y i) (y j) := by
    simp [c, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      hwy, smul_eq_mul, mul_ite]
  have hyc (i j : ι) : B (y i) (c j) = (1/2 : K) * B (y i) (y j) := by
    rw [hB.eq, hcy, hB.eq (y j) (y i)]
  have hcc (i j : ι) : B (c i) (c j) = 0 := hW _ (hcW i) _ (hcW j)
  refine ⟨fun i => y i - c i, ?_, ?_⟩
  · intro i j
    rw [map_sub, hwy, hwc, sub_zero]
  · intro i j
    simp only [map_sub, LinearMap.sub_apply, hcy, hyc, hcc]
    ring

theorem hyperbolic_family_independent
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (w z : ι → V)
    (hww : ∀ i j, B (w i) (w j) = 0)
    (hzz : ∀ i j, B (z i) (z j) = 0)
    (hwz : ∀ i j, B (w i) (z j) = if i = j then 1 else 0) :
    LinearIndependent K (Sum.elim w z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzw (i j : ι) : B (z i) (w j) = if j = i then 1 else 0 := by
    rw [hB.eq, hwz]
  have hl (i : ι) : c (Sum.inl i) = 0 := by
    have he := congrArg (B (z i)) hc
    simpa [map_sum, map_smul, Fintype.sum_sum_type, hzz, hzw, smul_eq_mul,
      mul_ite] using he
  have hr (i : ι) : c (Sum.inr i) = 0 := by
    have he := congrArg (B (w i)) hc
    simpa [map_sum, map_smul, Fintype.sum_sum_type, hww, hwz, smul_eq_mul,
      mul_ite] using he
  intro i
  cases i with
  | inl i => exact hl i
  | inr i => exact hr i

theorem hyperbolic_span_nondegenerate
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (w z : ι → V)
    (hww : ∀ i j, B (w i) (w j) = 0)
    (hzz : ∀ i j, B (z i) (z j) = 0)
    (hwz : ∀ i j, B (w i) (z j) = if i = j then 1 else 0) :
    (B.restrict (Submodule.span K (Set.range (Sum.elim w z)))).Nondegenerate := by
  intro v hv
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp v.property
  have hzw (i j : ι) : B (z i) (w j) = if j = i then 1 else 0 := by
    rw [hB.eq, hwz]
  have hl (i : ι) : c (Sum.inl i) = 0 := by
    have he := hv ⟨z i, Submodule.subset_span ⟨Sum.inr i, rfl⟩⟩
    change B v.val (z i) = 0 at he
    rw [← hc] at he
    simpa [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Fintype.sum_sum_type, hzz, hwz, smul_eq_mul, mul_ite] using he
  have hr (i : ι) : c (Sum.inr i) = 0 := by
    have he := hv ⟨w i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩
    change B v.val (w i) = 0 at he
    rw [← hc] at he
    simpa [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Fintype.sum_sum_type, hww, hzw, smul_eq_mul, mul_ite] using he
  apply Subtype.ext
  rw [← hc]
  simp [Fintype.sum_sum_type, hl, hr]

theorem isotropic_finrank_bound
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (W : Submodule K V) (hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0) :
    2 * finrank K W ≤ finrank K V := by
  let b := Module.finBasis K W
  obtain ⟨z,hwz,hzz⟩ := exists_dual_family B hB hn W hW b
  have hi := hyperbolic_family_independent B hB (fun i => (b i : V)) z
    (fun i j => hW _ (b i).property _ (b j).property) hzz hwz
  have hc := hi.fintype_card_le_finrank
  simpa [two_mul] using hc

end HessianTheorem11.IsotropicDual
