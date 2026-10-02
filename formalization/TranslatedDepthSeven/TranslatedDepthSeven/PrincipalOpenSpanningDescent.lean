import TranslatedDepthSeven.FiniteFreeFibrePointCount
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Descent of a finite spanning family to one principal open

Let `R → B`, let `M ⊆ R` be a multiplicative set, and let `A` be a
`B`-module.  Suppose that a displayed family `t` spans `A` over `B`, while
the image of another displayed family `s` spans after the elements of `M`
have been inverted in `B`.  Membership in the localized span gives one
base denominator for each member of `t`.  Their product is a single
element `m ∈ M` such that

`algebraMap R B m • A ⊆ span_B(s)`.

Consequently the same family `s` spans after localizing away from this one
base element.  If `A` is a ring, this gives a finite algebra on that
principal open, and the displayed family continues to span after every
field specialization of the open.

The statement is deliberately vertical: the only finite-model hypothesis
is the literal family `t` spanning the chosen `B`-model.  No relative
component space or flattening stratification is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open Pointwise

universe u v w x

/-- Generator-wise scalar denominators may be replaced by their product.
This module version is the exact analogue of simultaneous denominator
clearing for finitely generated ideals. -/
theorem prod_denominators_smul_mem_of_mem_span_range
    {B : Type u} {A : Type v} [CommRing B] [AddCommGroup A] [Module B A]
    {n : ℕ} (P : Submodule B A) (t : Fin n → A) (d : Fin n → B)
    (hclear : ∀ i, d i • t i ∈ P) {x : A}
    (hx : x ∈ Submodule.span B (Set.range t)) :
    (∏ i, d i) • x ∈ P := by
  classical
  refine Submodule.span_induction
    (p := fun x (_ : x ∈ Submodule.span B (Set.range t)) ↦
      (∏ i, d i) • x ∈ P)
    ?gen ?zero ?add ?smul hx
  · rintro x ⟨i, rfl⟩
    obtain ⟨c, hc⟩ : d i ∣ ∏ j, d j :=
      Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    rw [hc, mul_smul]
    simpa only [smul_smul, mul_comm] using P.smul_mem c (hclear i)
  · simp
  · intro x y _ _ hx hy
    simpa [smul_add] using P.add_mem hx hy
  · intro a x _ hx
    simpa [smul_smul, mul_comm] using P.smul_mem a hx

/-- One element of the base multiplicative set clears a generically
spanning family on a finite module model.

The generic fibre is the canonical localization of `A` at the image of
`M` in `B`.  The conclusion retains both the explicit clearing inclusion
and the exact spanning identity on the resulting principal open. -/
theorem exists_base_denominator_span_after_localization
    {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup A] [Module B A]
    (M : Submonoid R) {N D : ℕ} (t : Fin N → A) (s : Fin D → A)
    (ht : Submodule.span B (Set.range t) = ⊤)
    (hgeneric :
      Submodule.span (Localization (M.map (algebraMap R B)))
          (Set.range (fun i ↦
            LocalizedModule.mkLinearMap (M.map (algebraMap R B)) A (s i))) =
        ⊤) :
    ∃ m : R, m ∈ M ∧
      (∀ x : A,
        algebraMap R B m • x ∈ Submodule.span B (Set.range s)) ∧
      Submodule.span (Localization.Away (algebraMap R B m))
          (Set.range (fun i ↦
            LocalizedModule.mkLinearMap
              (Submonoid.powers (algebraMap R B m)) A (s i))) = ⊤ := by
  classical
  let S : Submonoid B := M.map (algebraMap R B)
  let f : A →ₗ[B] LocalizedModule S A :=
    LocalizedModule.mkLinearMap S A
  let P : Submodule B A := Submodule.span B (Set.range s)
  have hgeneric' :
      P.localized' (Localization S) S f = ⊤ := by
    rw [Submodule.localized'_span]
    rw [← Set.range_comp']
    simpa only [S, f, P] using hgeneric
  have hdenom :
      ∀ i : Fin N, ∃ d : R, d ∈ M ∧
        algebraMap R B d • t i ∈ P := by
    intro i
    have hfti : f (t i) ∈ P.localized' (Localization S) S f := by
      rw [hgeneric']
      trivial
    obtain ⟨a, ha, z, hz⟩ :=
      (Submodule.mem_localized' (Localization S) S f P (f (t i))).mp hfti
    have hfa : f a = z • f (t i) :=
      (IsLocalizedModule.mk'_eq_iff.mp hz)
    have hfa' : f a = f (z • t i) := by
      simpa only [Submonoid.smul_def, map_smul] using hfa
    obtain ⟨c, hc⟩ :=
      (IsLocalizedModule.eq_iff_exists S f).mp hfa'
    have hcz : (c * z) • t i ∈ P := by
      rw [mul_smul, ← hc]
      exact P.smul_mem c ha
    obtain ⟨d, hdM, hdz⟩ := Submonoid.mem_map.mp (c * z).property
    refine ⟨d, hdM, ?_⟩
    rw [hdz]
    exact hcz
  choose d hdM hclear using hdenom
  let m : R := ∏ i, d i
  have hmM : m ∈ M := by
    exact M.prod_mem fun i _hi ↦ hdM i
  have hclearAll :
      ∀ x : A, algebraMap R B m • x ∈ P := by
    intro x
    have hx : x ∈ Submodule.span B (Set.range t) := by
      rw [ht]
      trivial
    simpa only [m, map_prod] using
      (prod_denominators_smul_mem_of_mem_span_range P t
        (fun i ↦ algebraMap R B (d i)) hclear hx)
  let a : B := algebraMap R B m
  let Sa : Submonoid B := Submonoid.powers a
  let fa : A →ₗ[B] LocalizedModule Sa A :=
    LocalizedModule.mkLinearMap Sa A
  have haSa : a ∈ Sa := by
    exact ⟨1, by simp⟩
  let au : Sa := ⟨a, haSa⟩
  have hsmul : au • (⊤ : Submodule B A) ≤ P := by
    intro x hx
    obtain ⟨y, _hy, rfl⟩ := hx
    simpa only [au, a, Submonoid.smul_def] using hclearAll y
  have hlocalTop : P.localized' (Localization.Away a) Sa fa = ⊤ := by
    have hle :=
      Submodule.localized'_le_localized'_of_smul_le
        (Localization.Away a) Sa fa au hsmul
    rw [Submodule.localized'_top] at hle
    exact top_unique hle
  refine ⟨m, hmM, ?_, ?_⟩
  · simpa only [P] using hclearAll
  · rw [Submodule.localized'_span] at hlocalTop
    rw [← Set.range_comp'] at hlocalTop
    simpa only [a, Sa, fa, P] using hlocalTop

/-- Ring form of the preceding theorem.  On the principal open defined by
the returned base element, the localized algebra is module-finite and is
spanned by the images of the same `D` displayed elements. -/
theorem exists_base_denominator_moduleFinite_after_localization
    {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing A] [Algebra B A]
    (M : Submonoid R) {N D : ℕ} (t : Fin N → A) (s : Fin D → A)
    (ht : Submodule.span B (Set.range t) = ⊤)
    (hgeneric :
      Submodule.span (Localization (M.map (algebraMap R B)))
          (Set.range (fun i ↦
            LocalizedModule.mkLinearMap (M.map (algebraMap R B)) A (s i))) =
        ⊤) :
    ∃ m : R, m ∈ M ∧
      let Bm := Localization.Away (algebraMap R B m)
      let Am := LocalizedModule (Submonoid.powers (algebraMap R B m)) A
      let sm : Fin D → Am := fun i ↦
        LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R B m)) A (s i)
      Submodule.span Bm (Set.range sm) = ⊤ ∧ Module.Finite Bm Am := by
  obtain ⟨m, hm, _hclear, hspan⟩ :=
    exists_base_denominator_span_after_localization M t s ht hgeneric
  refine ⟨m, hm, hspan, ?_⟩
  exact Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr ⟨D, _, hspan⟩

/-- Specialization-uniform form.  After one base denominator is removed,
the same `D` elements span every scalar fibre over every field; in
particular every such fibre has vector-space dimension at most `D`. -/
theorem exists_base_denominator_finrank_specialization_le
    {R : Type u} {B : Type v} {A : Type w}
    [CommRing R] [CommRing B] [Algebra R B]
    [CommRing A] [Algebra B A]
    (M : Submonoid R) {N D : ℕ} (t : Fin N → A) (s : Fin D → A)
    (ht : Submodule.span B (Set.range t) = ⊤)
    (hgeneric :
      Submodule.span (Localization (M.map (algebraMap R B)))
          (Set.range (fun i ↦
            LocalizedModule.mkLinearMap (M.map (algebraMap R B)) A (s i))) =
        ⊤) :
    ∃ m : R, m ∈ M ∧
      ∀ (K : Type x), ∀ [Field K]
        [Algebra (Localization.Away (algebraMap R B m)) K],
        Module.finrank K
          (TensorProduct (Localization.Away (algebraMap R B m)) K
            (LocalizedModule (Submonoid.powers (algebraMap R B m)) A)) ≤ D := by
  obtain ⟨m, hm, hspan, _hfinite⟩ :=
    exists_base_denominator_moduleFinite_after_localization M t s ht hgeneric
  refine ⟨m, hm, ?_⟩
  intro K _ _
  exact finrank_scalarFibre_le_of_span_fin
    (Localization.Away (algebraMap R B m)) K
    (LocalizedModule (Submonoid.powers (algebraMap R B m)) A) D
    (fun i ↦ LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap R B m)) A (s i)) hspan

end

end TranslatedDepthSeven
