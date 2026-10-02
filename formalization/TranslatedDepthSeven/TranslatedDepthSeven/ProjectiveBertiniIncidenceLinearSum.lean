import TranslatedDepthSeven.ProjectiveBertiniIncidenceCoordinates
import Mathlib.Data.Fintype.BigOperators

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R]

def bertiniLinear {σ : Type*} [Fintype σ] (d : σ → R) : MvPolynomial σ R :=
  ∑ i, C (d i) * X i

omit [IsDomain R] in
theorem bertiniLinear_rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (d : σ → R) :
    rename e (bertiniLinear d) = bertiniLinear (d ∘ e.symm) := by
  classical
  simp only [bertiniLinear, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv e _ _ (fun i ↦ by simp)

omit [IsDomain R] in
theorem bertiniLinear_option {σ : Type*} [Fintype σ] (d : Option σ → R) :
    bertiniLinear d = C (d none) * X none +
      rename some (bertiniLinear (fun i ↦ d (some i))) := by
  simp only [bertiniLinear, Fintype.sum_option, map_sum, map_mul, rename_C, rename_X]

theorem bertini_linear_sum_span_isPrime_of_regular_pair
    {σ : Type*} [Fintype σ] (d : σ → R) (i j : σ) (hij : j ≠ i)
    (hi : d i ≠ 0)
    (hj : IsRegular (Ideal.Quotient.mk (Ideal.span ({d i} : Set R)) (d j))) :
    (Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R))).IsPrime := by
  classical
  let j' : {k : σ // k ≠ i} := ⟨j, hij⟩
  let τ := {k : {k : σ // k ≠ i} // k ≠ j'}
  let e : σ ≃ Option (Option τ) :=
    (Equiv.optionSubtypeNe i).symm.trans
      (Equiv.optionCongr (Equiv.optionSubtypeNe j').symm)
  let d' : Option (Option τ) → R := d ∘ e.symm
  have hd0 : d' none = d i := by simp [d', e]
  have hd1 : d' (some none) = d j := by
    simp [d', e, j']
    rfl
  have hp : (Ideal.span ({bertiniLinear d'} :
      Set (MvPolynomial (Option (Option τ)) R))).IsPrime := by
    rw [bertiniLinear_option, bertiniLinear_option, hd0, hd1]
    exact bertini_mvPolynomial_incidence_span_isPrime τ (d i) (d j) _ hi hj
  let f := renameEquiv R e
  have he : f (bertiniLinear d) = bertiniLinear d' := bertiniLinear_rename e d
  have hmap : (Ideal.span ({bertiniLinear d} : Set _)).map f.toRingHom =
      Ideal.span ({bertiniLinear d'} : Set _) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span ({p} : Set _)) he
  rw [← hmap] at hp
  have h := hp.comap f.toRingHom
  rw [Ideal.comap_map_of_bijective f.toRingHom f.bijective] at h
  exact h

theorem bertini_linear_sum_span_isPrime_of_isUnit
    {σ : Type*} [Fintype σ] (d : σ → R) (i : σ) (hi : IsUnit (d i)) :
    (Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R))).IsPrime := by
  classical
  let τ := {j : σ // j ≠ i}
  let e := (Equiv.optionSubtypeNe i).symm
  let d' : Option τ → R := d ∘ e.symm
  let f := (renameEquiv R e).trans (optionEquivLeft R τ)
  have he : f (bertiniLinear d) =
      Polynomial.C (C (d i)) * Polynomial.X +
        Polynomial.C (bertiniLinear (fun j : τ ↦ d j)) := by
    change optionEquivLeft R τ (rename e (bertiniLinear d)) = _
    rw [bertiniLinear_rename, bertiniLinear_option]
    simp only [e, Function.comp_apply, Equiv.symm_symm, Equiv.optionSubtypeNe_none,
      Equiv.optionSubtypeNe_some, map_add, map_mul, optionEquivLeft_X_none]
    change optionEquivLeft R τ (C (d i)) * Polynomial.X +
      optionEquivLeft R τ (rename some (bertiniLinear (fun j : τ ↦ d j))) = _
    rw [optionEquivLeft_C, bertini_optionEquivLeft_rename_some]
  have hu : IsUnit (C (d i) : MvPolynomial τ R) := hi.map C
  haveI : Subsingleton (MvPolynomial τ R ⧸ Ideal.span ({C (d i)} : Set _)) :=
    Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
  have hreg : IsRegular (Ideal.Quotient.mk (Ideal.span ({C (d i)} : Set _))
      (bertiniLinear (fun j : τ ↦ d j))) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  have hp := bertini_linear_span_isPrime_of_regular_pair
    (C (d i)) (bertiniLinear (fun j : τ ↦ d j)) hu.ne_zero hreg
  have hmap : (Ideal.span ({bertiniLinear d} : Set _)).map f.toRingHom =
      Ideal.span ({Polynomial.C (C (d i)) * Polynomial.X +
        Polynomial.C (bertiniLinear (fun j : τ ↦ d j))} : Set _) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p ↦ Ideal.span ({p} : Set _)) he
  rw [← hmap] at hp
  have h := hp.comap f.toRingHom
  rw [Ideal.comap_map_of_bijective f.toRingHom f.bijective] at h
  exact h

omit [IsDomain R] in
theorem bertini_linear_sum_quotient_C_ne_zero
    {σ : Type*} [Fintype σ] (d : σ → R) (r : R) (hr : r ≠ 0) :
    Ideal.Quotient.mk (Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R)))
      (C r) ≠ 0 := by
  have hle : Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R)) ≤
      RingHom.ker (eval (fun _ ↦ (0 : R))) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change eval (fun _ ↦ (0 : R)) (bertiniLinear d) = 0
    simp [bertiniLinear]
  intro hz
  have h := hle (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  exact hr (by simpa using h)

end
end TranslatedDepthSeven
