import TranslatedDepthSeven.FiniteCoefficientDescent
import TranslatedDepthSeven.FiniteGaloisIdealDescent
import TranslatedDepthSeven.QbarFiniteCoefficientField
import TranslatedDepthSeven.FiniteHomogeneousIdealGenerators

/-!
# Descent of a Galois-invariant ideal over `QbarField`

This file carries out coefficient descent using an actual finite generating
family.  The finite normal field contains the coefficients of those
generators.  Contraction to that field is stable under its finite Galois
group, because every finite-field automorphism extends to `QbarField`; finite
Galois ideal descent then gives the rational ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 800000

open MvPolynomial

universe u

variable {σ : Type u} [Fintype σ]

abbrev QbarField := AlgebraicClosure ℚ

local instance : DecidableEq (MvPolynomial σ QbarField) := Classical.decEq _
local instance qbarMvPolynomialGradedAlgebra :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ QbarField) :=
  MvPolynomial.gradedAlgebra
local instance rationalMvPolynomialGradedAlgebra :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule σ ℚ) :=
  MvPolynomial.gradedAlgebra

omit [Fintype σ] in
theorem map_finiteGaloisConjugatePolynomial_to_qbar
    {L : Type*} [Field L] [Algebra ℚ L]
    (ι : L →ₐ[ℚ] QbarField) (τ : L ≃ₐ[ℚ] L)
    (g : QbarField ≃ₐ[ℚ] QbarField)
    (hg : ∀ x : L, g (ι x) = ι (τ x))
    (f : MvPolynomial σ L) :
    MvPolynomial.map ι.toRingHom
        (finiteGaloisConjugatePolynomial τ f) =
      conjugatePolynomial g
        (MvPolynomial.map ι.toRingHom f) := by
  ext m
  simp only [finiteGaloisConjugatePolynomial, conjugatePolynomial_apply,
    MvPolynomial.coeff_map]
  rw [MvPolynomial.mapEquiv_apply, MvPolynomial.coeff_map]
  exact (hg (MvPolynomial.coeff m f)).symm

omit [Fintype σ] in
theorem contraction_stable_of_automorphisms_extend
    {L : Type*} [Field L] [Algebra ℚ L]
    (ι : L →ₐ[ℚ] QbarField)
    (hext : ∀ τ : L ≃ₐ[ℚ] L, ∃ g : QbarField ≃ₐ[ℚ] QbarField,
      ∀ x : L, g (ι x) = ι (τ x))
    (P : Ideal (MvPolynomial σ QbarField))
    (hP : ∀ g : QbarField ≃ₐ[ℚ] QbarField, conjugateIdeal g P = P) :
    ∀ τ : L ≃ₐ[ℚ] L,
      finiteGaloisConjugateIdeal τ
          (P.comap (MvPolynomial.map ι.toRingHom)) =
        P.comap (MvPolynomial.map ι.toRingHom) := by
  intro τ
  obtain ⟨g, hg⟩ := hext τ
  let J := P.comap (MvPolynomial.map ι.toRingHom)
  have hforward : finiteGaloisConjugateIdeal τ J ≤ J := by
    rw [finiteGaloisConjugateIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    change MvPolynomial.map ι.toRingHom
      (finiteGaloisConjugatePolynomial τ f) ∈ P
    rw [map_finiteGaloisConjugatePolynomial_to_qbar
      ι τ g hg]
    have hm : conjugatePolynomial g
        (MvPolynomial.map ι.toRingHom f) ∈
        conjugateIdeal g P := Ideal.mem_map_of_mem _ hf
    rwa [hP g] at hm
  apply le_antisymm hforward
  obtain ⟨g', hg'⟩ := hext τ.symm
  have hback : finiteGaloisConjugateIdeal τ.symm J ≤ J := by
    rw [finiteGaloisConjugateIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    change MvPolynomial.map ι.toRingHom
      (finiteGaloisConjugatePolynomial τ.symm f) ∈ P
    rw [map_finiteGaloisConjugatePolynomial_to_qbar
      ι τ.symm g' hg']
    have hm : conjugatePolynomial g'
        (MvPolynomial.map ι.toRingHom f) ∈
        conjugateIdeal g' P := Ideal.mem_map_of_mem _ hf
    rwa [hP g'] at hm
  intro f hf
  have hf' : finiteGaloisConjugatePolynomial τ.symm f ∈ J :=
    hback (Ideal.mem_map_of_mem _ hf)
  have hm := Ideal.mem_map_of_mem
    (finiteGaloisConjugatePolynomial τ).toRingHom hf'
  have heq : finiteGaloisConjugatePolynomial τ
      (finiteGaloisConjugatePolynomial τ.symm f) = f := by
    ext m
    simp only [finiteGaloisConjugatePolynomial, MvPolynomial.mapEquiv_apply]
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
    exact τ.apply_symm_apply _
  rw [← heq]
  exact hm

omit [Fintype σ] in
theorem contraction_to_polynomialFamilyGaloisField_stable
    (P : Ideal (MvPolynomial σ QbarField))
    (hP : ∀ g : QbarField ≃ₐ[ℚ] QbarField, conjugateIdeal g P = P)
    (E : Finset (MvPolynomial σ QbarField)) :
    ∀ τ : polynomialFamilyGaloisField E ≃ₐ[ℚ]
        polynomialFamilyGaloisField E,
      finiteGaloisConjugateIdeal τ
          (P.comap (MvPolynomial.map
            (polynomialFamilyGaloisField E).val.toRingHom)) =
        P.comap (MvPolynomial.map
          (polynomialFamilyGaloisField E).val.toRingHom) := by
  apply contraction_stable_of_automorphisms_extend
    (polynomialFamilyGaloisField E).val
  exact exists_qbarAlgEquiv_extending E
  exact hP

omit [Fintype σ] in
theorem map_comap_eq_of_generators_over_intermediateField
    (L : IntermediateField ℚ QbarField)
    (P : Ideal (MvPolynomial σ QbarField)) {N : ℕ}
    (f : Fin N → MvPolynomial σ QbarField)
    (hf : Ideal.span (Set.range f) = P)
    (hcoeff : ∀ i m, MvPolynomial.coeff m (f i) ∈ L) :
    (P.comap (MvPolynomial.map L.val.toRingHom)).map
        (MvPolynomial.map L.val.toRingHom) = P := by
  apply le_antisymm
  · exact (Ideal.map_le_iff_le_comap).mpr le_rfl
  · have hle : Ideal.span (Set.range f) ≤
        (P.comap (MvPolynomial.map L.val.toRingHom)).map
          (MvPolynomial.map L.val.toRingHom) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      let q : MvPolynomial σ L :=
        polynomialOverIntermediateField L (f i) (hcoeff i)
      have hqmap : MvPolynomial.map L.val.toRingHom q = f i :=
        map_polynomialOverIntermediateField L (f i) (hcoeff i)
      rw [← hqmap]
      apply Ideal.mem_map_of_mem
      change MvPolynomial.map L.val.toRingHom q ∈ P
      rw [hqmap]
      rw [← hf]
      exact Ideal.subset_span ⟨i, rfl⟩
    rw [hf] at hle
    exact hle

omit [Fintype σ] in
theorem coefficient_mem_generator_galoisField
    {N : ℕ} (f : Fin N → MvPolynomial σ QbarField)
    (i : Fin N) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (f i) ∈
      (polynomialFamilyGaloisField (Finset.univ.image f) :
        IntermediateField ℚ QbarField) := by
  classical
  by_cases hz : MvPolynomial.coeff m (f i) = 0
  · rw [hz]
    exact (polynomialFamilyGaloisField
      (Finset.univ.image f) : IntermediateField ℚ QbarField).zero_mem
  · apply coefficient_mem_polynomialFamilyGaloisField
      (Finset.univ.image f)
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · exact MvPolynomial.coeff_mem_coeffs m hz

/-- A coefficientwise Galois-invariant ideal over `QbarField` is exactly the
coefficient extension of a rational ideal. -/
theorem exists_rationalIdeal_map_eq_of_galoisInvariant
    (P : Ideal (MvPolynomial σ QbarField))
    (hP : ∀ g : QbarField ≃ₐ[ℚ] QbarField, conjugateIdeal g P = P) :
    ∃ I : Ideal (MvPolynomial σ ℚ),
      I.map (MvPolynomial.map (algebraMap ℚ QbarField)) = P := by
  classical
  have hPfg : P.FG := IsNoetherian.noetherian P
  obtain ⟨N, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hPfg
  let E := Finset.univ.image f
  let L : IntermediateField ℚ QbarField :=
    polynomialFamilyGaloisField E
  let J : Ideal (MvPolynomial σ L) :=
    P.comap (MvPolynomial.map L.val.toRingHom)
  have hJL : J.map (MvPolynomial.map L.val.toRingHom) = P := by
    apply map_comap_eq_of_generators_over_intermediateField L P f hf
    intro i m
    exact coefficient_mem_generator_galoisField f i m
  have hJstable : ∀ τ : L ≃ₐ[ℚ] L,
      finiteGaloisConjugateIdeal τ J = J := by
    exact contraction_to_polynomialFamilyGaloisField_stable P hP E
  let I : Ideal (MvPolynomial σ ℚ) :=
    J.comap (MvPolynomial.map (algebraMap ℚ L))
  refine ⟨I, ?_⟩
  rw [← hJL]
  have hJI : I.map (MvPolynomial.map (algebraMap ℚ L)) = J :=
    map_comap_eq_of_finiteGalois_invariant J hJstable
  rw [← hJI, Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro q
    simp [RingHom.comp_apply]
  · intro i
    simp [RingHom.comp_apply]

theorem map_rationalContraction_eq_of_galoisInvariant
    (P : Ideal (MvPolynomial σ QbarField))
    (hP : ∀ g : QbarField ≃ₐ[ℚ] QbarField, conjugateIdeal g P = P) :
    (P.comap (MvPolynomial.map (algebraMap ℚ QbarField))).map
        (MvPolynomial.map (algebraMap ℚ QbarField)) = P := by
  obtain ⟨I, hI⟩ := exists_rationalIdeal_map_eq_of_galoisInvariant P hP
  apply le_antisymm
  · exact (Ideal.map_le_iff_le_comap).mpr le_rfl
  · have hle : I ≤ P.comap
        (MvPolynomial.map (algebraMap ℚ QbarField)) := by
      intro f hf
      change MvPolynomial.map (algebraMap ℚ QbarField) f ∈ P
      rw [← hI]
      exact Ideal.mem_map_of_mem _ hf
    calc
      P = I.map (MvPolynomial.map (algebraMap ℚ QbarField)) := hI.symm
      _ ≤ (P.comap (MvPolynomial.map (algebraMap ℚ QbarField))).map
          (MvPolynomial.map (algebraMap ℚ QbarField)) := Ideal.map_mono hle

omit [Fintype σ] in
theorem rationalContraction_isHomogeneous
    (P : Ideal (MvPolynomial σ QbarField))
    (hhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ QbarField)) :
    (P.comap (MvPolynomial.map (algebraMap ℚ QbarField))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ ℚ) := by
  intro d f hf
  rw [← DirectSum.Decomposition.decompose'_eq]
  rw [MvPolynomial.decomposition.decompose'_apply]
  change MvPolynomial.map (algebraMap ℚ QbarField)
      (MvPolynomial.homogeneousComponent d f) ∈ P
  have hmap : MvPolynomial.map (algebraMap ℚ QbarField)
        (MvPolynomial.homogeneousComponent d f) =
      MvPolynomial.homogeneousComponent d
        (MvPolynomial.map (algebraMap ℚ QbarField) f) := by
    ext m
    by_cases hm : Finsupp.weight (1 : σ → ℕ) m = d <;>
    simp [MvPolynomial.homogeneousComponent,
      MvPolynomial.coeff_weightedHomogeneousComponent,
      MvPolynomial.coeff_map, hm]
  rw [hmap]
  have hp := hhom d hf
  rw [← DirectSum.Decomposition.decompose'_eq] at hp
  rw [MvPolynomial.decomposition.decompose'_apply] at hp
  exact hp

/-- Full homogeneous form of QbarField invariant-ideal descent.  The descended
ideal is the literal rational contraction, is homogeneous, and its exact
coefficient extension is the original ideal. -/
theorem rationalHomogeneousIdeal_descent_of_galoisInvariant
    (P : Ideal (MvPolynomial σ QbarField))
    (hstable : ∀ g : QbarField ≃ₐ[ℚ] QbarField, conjugateIdeal g P = P)
    (hhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ QbarField)) :
    ∃ I : Ideal (MvPolynomial σ ℚ),
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℚ) ∧
      I.map (MvPolynomial.map (algebraMap ℚ QbarField)) = P := by
  exact ⟨P.comap (MvPolynomial.map (algebraMap ℚ QbarField)),
    rationalContraction_isHomogeneous P hhom,
    map_rationalContraction_eq_of_galoisInvariant P hstable⟩

end

end TranslatedDepthSeven
