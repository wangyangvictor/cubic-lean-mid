import HessianTheorem11.UnconditionalFlagKernelBasis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Two weighted flags admit a common basis, preserving the complete weight
multisets. The proof is a hyperplane induction, without invariant theory. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFlags
open Module
variable {K : Type*} [Field K]

private theorem flag_coe_of_basis_mem {V : Type*} [AddCommGroup V] [Module K V]
    {n m : ℕ} {N : Submodule K V} (b : Basis (Fin n) K V)
    (c : Basis (Fin m) K N) (w : Fin n → ℤ) (u : Fin m → ℤ)
    (hc : ∀ i, (c i : V) ∈ basisFlag b w (u i)) :
    ∀ a x, x ∈ basisFlag c u a → (x : V) ∈ basisFlag b w a := by
  intro a
  have hle : basisFlag c u a ≤ (basisFlag b w a).comap N.subtype := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    exact basisFlag_mono b w hi (hc i)
  exact fun x hx => hle hx

private theorem flag_at_max {V : Type*} [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (w : Fin n → ℤ) (i : Fin n)
    (hi : ∀ k, w k ≤ w i) : basisFlag b w (w i) = ⊤ := by
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨k,rfl⟩
  exact basisFlag_mono b w (hi k) (mem_basisFlag b w k)

/-- A single basis compatible with both weighted flags, with each original
weight multiset preserved (expressed by every real-valued sum). -/
theorem exists_common_compatible_basis {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module K V]
    (b c : Basis (Fin n) K V) (w u : Fin n → ℤ) :
    ∃ d : Basis (Fin n) K V, ∃ w' u' : Fin n → ℤ,
      (∀ i, d i ∈ basisFlag b w (w' i)) ∧
      (∀ i, d i ∈ basisFlag c u (u' i)) ∧
      (∀ φ : ℤ → ℝ, ∑ i, φ (w' i) = ∑ i, φ (w i)) ∧
      (∀ φ : ℤ → ℝ, ∑ i, φ (u' i) = ∑ i, φ (u i)) := by
  classical
  induction n generalizing V with
  | zero => exact ⟨b,w,u,fun i => Fin.elim0 i,fun i => Fin.elim0 i,
      fun _ => rfl,fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨i,_,himax⟩ := Finset.exists_max_image Finset.univ w
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n+1))).Nonempty)
    have hmax : ∀ k, w k ≤ w i := fun k => himax k (Finset.mem_univ k)
    let l := b.coord i
    have hli : l (b i) = 1 := by simp [l,Basis.coord_apply]
    have hl : l ≠ 0 := by
      intro hz
      have he := hli
      rw [hz,LinearMap.zero_apply] at he
      exact zero_ne_one he
    obtain ⟨j,hj,hfirst⟩ := exists_first_visible c u l hl
    let v := (l (c j))⁻¹ • c j
    have hv : l v = 1 := by simp [v,hj]
    obtain ⟨bH,hbH⟩ := exists_projected_kernel_basis b l i (by rw [hli]; exact one_ne_zero)
    obtain ⟨cH,hcH⟩ := exists_projected_kernel_basis c l j hj
    have hbmem (k : Fin n) : (bH k : V) ∈ basisFlag b w (w (i.succAbove k)) := by
      rw [hbH]
      have hk : l (b (i.succAbove k)) = 0 := by
        simp [l,Basis.coord_apply,Finsupp.single_apply,Fin.succAbove_ne]
      simp only [hyperplaneProjection_apply,hk,zero_smul,sub_zero]
      exact mem_basisFlag b w _
    have hcmem (k : Fin n) : (cH k : V) ∈ basisFlag c u (u (j.succAbove k)) := by
      rw [hcH]
      exact projection_preserves_flag c u l j hfirst v
        ((basisFlag c u (u j)).smul_mem _ (mem_basisFlag c u j)) _ _
        (mem_basisFlag c u _)
    obtain ⟨dH,wH,uH,hdw,hdu,hsw,hsu⟩ := ih bH cH
      (fun k => w (i.succAbove k)) (fun k => u (j.succAbove k))
    have hlin : ∀ a : K, ∀ x ∈ LinearMap.ker l, a • v + x = 0 → a = 0 := by
      intro a x hx he
      have e := congrArg l he
      change l x = 0 at hx
      simpa [hv,hx] using e
    have hspan : ∀ x : V, ∃ a : K, x + a • v ∈ LinearMap.ker l := by
      intro x
      refine ⟨-l x,?_⟩
      change l (x + (-l x) • v) = 0
      simp [hv]
    let d := Basis.mkFinCons v dH hlin hspan
    refine ⟨d,Fin.cons (w i) wH,Fin.cons (u j) uH,?_,?_,?_,?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [d,Basis.coe_mkFinCons,Fin.cons_zero]
        change v ∈ basisFlag b w (w i)
        rw [flag_at_max b w i hmax]
        trivial
      · simp only [d,Basis.coe_mkFinCons,Fin.cons_succ,Function.comp_apply]
        change (dH k : V) ∈ basisFlag b w (wH k)
        exact flag_coe_of_basis_mem b bH w _ hbmem _ _ (hdw k)
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [d,Basis.coe_mkFinCons,Fin.cons_zero]
        change v ∈ basisFlag c u (u j)
        exact (basisFlag c u (u j)).smul_mem _ (mem_basisFlag c u j)
      · simp only [d,Basis.coe_mkFinCons,Fin.cons_succ,Function.comp_apply]
        change (dH k : V) ∈ basisFlag c u (uH k)
        exact flag_coe_of_basis_mem c cH u _ hcmem _ _ (hdu k)
    · intro φ
      rw [Fin.sum_univ_succ,Fin.sum_univ_succAbove (fun k => φ (w k)) i]
      simpa using congrArg (fun x : ℝ => φ (w i) + x) (hsw φ)
    · intro φ
      rw [Fin.sum_univ_succ,Fin.sum_univ_succAbove (fun k => φ (u k)) j]
      simpa using congrArg (fun x : ℝ => φ (u j) + x) (hsu φ)

/-- The dimension of an actual flag level counts the weights at that level. -/
theorem finrank_basisFlag {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (b : Basis (Fin n) K V) (w : Fin n → ℤ) (a : ℤ) :
    finrank K (basisFlag b w a) = ∑ i : Fin n, if w i ≤ a then 1 else 0 := by
  classical
  let f : {i : Fin n // w i ≤ a} → V := fun i => b i
  have hs : {v | ∃ i, w i ≤ a ∧ v = b i} = Set.range f := by
    ext v
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,i.property,rfl⟩
  have hli : LinearIndependent K f := b.linearIndependent.comp
    (fun i : {i : Fin n // w i ≤ a} => i.val) Subtype.val_injective
  rw [basisFlag,hs,finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

/-- Compatibility and preservation of all weight sums give equality of every
actual filtration subspace. -/
theorem basisFlag_eq_of_compatible {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (b d : Basis (Fin n) K V) (w u : Fin n → ℤ)
    (hd : ∀ i, d i ∈ basisFlag b w (u i))
    (hs : ∀ φ : ℤ → ℝ, ∑ i, φ (u i) = ∑ i, φ (w i)) :
    basisFlag d u = basisFlag b w := by
  classical
  letI : FiniteDimensional K V := Basis.finiteDimensional_of_finite b
  funext a
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro x ⟨i,hi,rfl⟩
    exact basisFlag_mono b w hi (hd i)
  · rw [finrank_basisFlag,finrank_basisFlag]
    have he := hs (fun z => if z ≤ a then 1 else 0)
    exact_mod_cast he

/-- Two integer-weighted basis flags have a common splitting, with the two
weight multisets unchanged. No geometric or invariant-theoretic input. -/
theorem exists_common_weighted_basis {n : ℕ} {V : Type*} [AddCommGroup V] [Module K V]
    (b c : Basis (Fin n) K V) (w u : Fin n → ℤ) :
    ∃ d : Basis (Fin n) K V, ∃ w' u' : Fin n → ℤ,
      basisFlag d w' = basisFlag b w ∧ basisFlag d u' = basisFlag c u ∧
      (∀ φ : ℤ → ℝ, ∑ i, φ (w' i) = ∑ i, φ (w i)) ∧
      (∀ φ : ℤ → ℝ, ∑ i, φ (u' i) = ∑ i, φ (u i)) := by
  obtain ⟨d,w',u',hdw,hdu,hsw,hsu⟩ := exists_common_compatible_basis b c w u
  exact ⟨d,w',u',basisFlag_eq_of_compatible b d w w' hdw hsw,
    basisFlag_eq_of_compatible c d u u' hdu hsu,hsw,hsu⟩

end HessianTheorem11.UnconditionalFlags
