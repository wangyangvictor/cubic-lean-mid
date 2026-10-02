import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-! The two-dimensional symmetric-product lemma in source Lemma 34.5.
The argument uses linear algebra over a field of characteristic zero only. -/
noncomputable section
namespace HessianTheorem11.TwoDimensionalSymmetricProducts
open Module
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def product (u v : Module.Dual K V) : LinearMap.BilinForm K V :=
  u.smulRight v + v.smulRight u

@[simp] theorem product_apply (u v : Module.Dual K V) (a b : V) :
    product u v a b = u a * v b + v a * u b := rfl

def productLinear (v : Module.Dual K V) :
    Module.Dual K V →ₗ[K] LinearMap.BilinForm K V where
  toFun u := product u v
  map_add' u w := by ext a b; simp; ring
  map_smul' c u := by ext a b; simp; ring

theorem productLinear_injective (v : Module.Dual K V) (hv : v ≠ 0) :
    Function.Injective (productLinear v) := by
  suffices hz : ∀ u, productLinear v u = 0 → u = 0 by
    intro u w h
    exact sub_eq_zero.mp (hz (u-w) (by rw [map_sub, h, sub_self]))
  intro u hu
  have hex : ∃ a, v a ≠ 0 := by
    by_contra! h
    exact hv (LinearMap.ext h)
  obtain ⟨a,ha⟩ := hex
  have huu := congrArg (fun B : LinearMap.BilinForm K V => B a a) hu
  change u a * v a + v a * u a = 0 at huu
  have hua : u a = 0 := by
    have : (2 : K) * u a * v a = 0 := by linear_combination huu
    exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ha)).resolve_left (by norm_num)
  ext b
  have hub := congrArg (fun B : LinearMap.BilinForm K V => B a b) hu
  change u a * v b + v a * u b = 0 at hub
  simpa [hua, ha] using hub

theorem mem_line_of_ker_le {u v : Module.Dual K V}
    (h : LinearMap.ker v ≤ LinearMap.ker u) :
    u ∈ Submodule.span K ({v} : Set (Module.Dual K V)) := by
  simpa only [iInf_const, Set.range_const] using
    (mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => v) (K := u)
      (by simpa only [iInf_const] using h))

/-- A pencil containing all products of a two-dimensional space with the
image of one of its nonzero members has their annihilator in its radical.
In particular this applies to the span of two independent symmetric forms. -/
theorem common_radical
    (U : Submodule K (Module.Dual K V)) (hU : finrank K U = 2)
    (P : Submodule K (LinearMap.BilinForm K V)) (hP : finrank K P ≤ 2)
    (Q : LinearMap.BilinForm K V) (hQ : Q ∈ P) (hQ0 : Q ≠ 0)
    (hmixed : ∀ u ∈ U, ∀ a, product u (Q a) ∈ P) :
    ∀ z, (∀ u ∈ U, u z = 0) → ∀ R ∈ P, R z = 0 := by
  classical
  obtain ⟨a₀,ha₀⟩ : ∃ a, Q a ≠ 0 := by
    by_contra! h
    exact hQ0 (LinearMap.ext h)
  let v := Q a₀
  have hv : v ≠ 0 := ha₀
  let f := (productLinear v).comp U.subtype
  have hf : Function.Injective f := (productLinear_injective v hv).comp Subtype.val_injective
  have hrange : LinearMap.range f = P := by
    have hle : LinearMap.range f ≤ P := by
      rintro _ ⟨u,rfl⟩
      exact hmixed u u.property a₀
    have hd := LinearMap.finrank_range_of_inj hf
    have hm := Submodule.finrank_mono hle
    have he : finrank K (LinearMap.range f) = finrank K P := by omega
    exact @Submodule.eq_of_le_of_finrank_eq K (LinearMap.BilinForm K V)
      inferInstance inferInstance inferInstance
      (LinearMap.range (τ₁₂ := RingHom.id K) f) P inferInstance hle he
  have hrepr (R : LinearMap.BilinForm K V) (hR : R ∈ P) :
      ∃ u ∈ U, product u v = R := by
    rw [← hrange] at hR
    obtain ⟨u,hu⟩ := hR
    exact ⟨u,u.property,hu⟩
  obtain ⟨u,hu,hun⟩ : ∃ u ∈ U, u ∉ Submodule.span K ({v} : Set (Module.Dual K V)) := by
    by_contra! h
    have hd := Submodule.finrank_mono (show U ≤ Submodule.span K {v} from h)
    rw [finrank_span_singleton hv, hU] at hd
    omega
  obtain ⟨b,hvb,hub⟩ : ∃ b, v b = 0 ∧ u b ≠ 0 := by
    by_contra! h
    apply hun
    apply mem_line_of_ker_le
    intro b hb
    exact h b hb
  have hline (a : V) : Q a ∈ Submodule.span K ({v} : Set (Module.Dual K V)) := by
    apply mem_line_of_ker_le
    intro c hc
    obtain ⟨w,hw,heq⟩ := hrepr _ (hmixed u hu a)
    have hbb := congrArg (fun B : LinearMap.BilinForm K V => B b b) heq
    simp only [product_apply, hvb, mul_zero, zero_mul, add_zero, zero_add] at hbb
    have hqb : Q a b = 0 := by
      have : (2 : K) * u b * Q a b = 0 := by linear_combination -hbb
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hub)
    have hbc := congrArg (fun B : LinearMap.BilinForm K V => B b c) heq
    change v c = 0 at hc
    simp only [product_apply, hvb, hc, hqb, mul_zero, zero_mul, add_zero,
      zero_add] at hbc
    exact (mul_eq_zero.mp hbc.symm).resolve_left hub
  obtain ⟨w,hw,hwQ⟩ := hrepr Q hQ
  obtain ⟨c,hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra! h
    exact hv (LinearMap.ext h)
  have hwline : w ∈ Submodule.span K ({v} : Set (Module.Dual K V)) := by
    have heq : v c • w = Q c - w c • v := by
      ext b
      have hh := congrArg (fun B : LinearMap.BilinForm K V => B c b) hwQ
      simp only [product_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at *
      linear_combination hh
    have hmem : v c • w ∈ Submodule.span K ({v} : Set (Module.Dual K V)) := by
      rw [heq]
      exact Submodule.sub_mem _ (hline c)
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v)))
    exact (Submodule.smul_mem_iff _ hc).mp hmem
  obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp hwline
  have hd0 : d ≠ 0 := by
    intro hz
    have hw0 : w = 0 := by simpa [hz] using hd.symm
    apply hQ0
    rw [← hwQ, hw0]
    ext a b
    simp
  have hvU : v ∈ U := by
    apply (Submodule.smul_mem_iff U hd0).mp
    rwa [hd]
  intro z hz R hR
  obtain ⟨w,hw,heq⟩ := hrepr R hR
  rw [← heq]
  ext b
  simp [hz w hw, hz v hvU]

end HessianTheorem11.TwoDimensionalSymmetricProducts
