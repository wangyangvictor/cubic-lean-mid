import TranslatedDepthSeven.ExplicitFiniteNormalizationModel
import TranslatedDepthSeven.FractionFieldFiniteCoefficientClearing

/-!
# The vertical finite-normalization package

This file packages the finite-data part of the vertical argument.  A finite
family of generic equations, finitely many polynomial normalization
coordinates, and monic coordinate relations over a fraction field all descend
to one principal localization.  The literal model obtained by adjoining the
substituted monic relations has exactly the prescribed generic ideal and is
finite over the displayed polynomial algebra.

No primality, reducedness, equidimensionality, smoothness, or assertion about
special fibres is required.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u

open Polynomial

/-- If the displayed equations span `P` and all substituted normalization
relations already lie in `P`, adjoining those relations does not change the
ideal. -/
theorem finiteNormalizationModelIdeal_eq_of_span_eq
    {K : Type u} [CommRing K] {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) K)
    (q : Fin d → MvPolynomial (Fin N) K)
    (p : Fin N → (MvPolynomial (Fin d) K)[X])
    (P : Ideal (MvPolynomial (Fin N) K))
    (hspan : Ideal.span (Set.range f) = P)
    (hrel : ∀ i, normalizationCoordinateRelation q p i ∈ P) :
    finiteNormalizationModelIdeal f q p = P := by
  apply le_antisymm
  · rw [finiteNormalizationModelIdeal, Ideal.span_le]
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · rw [← hspan]
      exact Ideal.subset_span ⟨i, rfl⟩
    · exact hrel i
  · rw [← hspan]
    apply Ideal.span_mono
    exact Set.subset_union_left

/-- A finite generic model with displayed normalization coordinates and monic
coordinate relations admits one common principal model.  Its generic scalar
extension is exactly the target ideal, and its displayed normalization map is
finite.  This strongest form only assumes the equality of the displayed
generic model ideal with the target ideal. -/
theorem exists_vertical_finite_normalization_model_of_modelIdeal_eq
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) K)
    (q : Fin d → MvPolynomial (Fin N) K)
    (p : Fin N → (MvPolynomial (Fin d) K)[X])
    (hmonic : ∀ i, (p i).Monic)
    (P : Ideal (MvPolynomial (Fin N) K))
    (hmodel : finiteNormalizationModelIdeal f q p = P) :
    ∃ (Δ : R) (hΔ : Δ ≠ 0),
      ∃ f₀ : Fin r → MvPolynomial (Fin N) (Localization.Away Δ),
      ∃ q₀ : Fin d → MvPolynomial (Fin N) (Localization.Away Δ),
      ∃ p₀ : Fin N →
          (MvPolynomial (Fin d) (Localization.Away Δ))[X],
        (∀ i, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (f₀ i) = f i) ∧
        (∀ j, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (q₀ j) = q j) ∧
        (∀ i, (p₀ i).Monic) ∧
        (∀ i, Polynomial.map
          (MvPolynomial.map
            (awayToFractionRing (R := R) (K := K) Δ hΔ))
          (p₀ i) = p i) ∧
        Ideal.map
            (MvPolynomial.map
              (awayToFractionRing (R := R) (K := K) Δ hΔ))
            (finiteNormalizationModelIdeal f₀ q₀ p₀) = P ∧
        (finiteNormalizationModelAlgHom f₀ q₀ p₀).Finite := by
  classical
  let fq : Fin (r + d) → MvPolynomial (Fin N) K :=
    Fin.addCases f q
  let pp : Fin N → MvPolynomial (Option (Fin d)) K :=
    fun i ↦ (MvPolynomial.optionEquivLeft K (Fin d)).symm (p i)
  obtain ⟨Δ, hΔ, fq₀, pp₀, hfq₀, hpp₀⟩ :=
    exists_common_principal_model_two_mvPolynomial_families
      (R := R) (K := K) fq pp
  let f₀ : Fin r → MvPolynomial (Fin N) (Localization.Away Δ) :=
    fun i ↦ fq₀ (Fin.castAdd d i)
  let q₀ : Fin d → MvPolynomial (Fin N) (Localization.Away Δ) :=
    fun j ↦ fq₀ (Fin.natAdd r j)
  let p₀ : Fin N →
      (MvPolynomial (Fin d) (Localization.Away Δ))[X] :=
    fun i ↦ MvPolynomial.optionEquivLeft
      (Localization.Away Δ) (Fin d) (pp₀ i)
  have hf₀ : ∀ i, MvPolynomial.map
      (awayToFractionRing (R := R) (K := K) Δ hΔ) (f₀ i) = f i := by
    intro i
    simpa only [f₀, fq, Fin.addCases_left] using hfq₀ (Fin.castAdd d i)
  have hq₀ : ∀ j, MvPolynomial.map
      (awayToFractionRing (R := R) (K := K) Δ hΔ) (q₀ j) = q j := by
    intro j
    simpa only [q₀, fq, Fin.addCases_right] using hfq₀ (Fin.natAdd r j)
  have hp₀ : ∀ i, (p₀ i).Monic := by
    intro i
    change (MvPolynomial.optionEquivLeft
      (Localization.Away Δ) (Fin d) (pp₀ i)).Monic
    apply Polynomial.monic_of_injective
      (MvPolynomial.map_injective
        (awayToFractionRing (R := R) (K := K) Δ hΔ)
        (awayToFractionRing_injective Δ hΔ))
    rw [map_optionEquivLeft, hpp₀ i]
    simpa only [pp,
      (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply]
      using hmonic i
  have hmap_p₀ : ∀ i, Polynomial.map
      (MvPolynomial.map
        (awayToFractionRing (R := R) (K := K) Δ hΔ))
      (p₀ i) = p i := by
    intro i
    change Polynomial.map
        (MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ))
        (MvPolynomial.optionEquivLeft
          (Localization.Away Δ) (Fin d) (pp₀ i)) = p i
    rw [map_optionEquivLeft, hpp₀ i]
    exact (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply (p i)
  refine ⟨Δ, hΔ, f₀, q₀, p₀, hf₀, hq₀, hp₀, hmap_p₀, ?_, ?_⟩
  · rw [map_finiteNormalizationModelIdeal]
    have hmapmodel :
        finiteNormalizationModelIdeal
          (fun i ↦ MvPolynomial.map
            (awayToFractionRing (R := R) (K := K) Δ hΔ) (f₀ i))
          (fun j ↦ MvPolynomial.map
            (awayToFractionRing (R := R) (K := K) Δ hΔ) (q₀ j))
          (fun i ↦ (p₀ i).map
            (MvPolynomial.map
              (awayToFractionRing (R := R) (K := K) Δ hΔ))) =
          finiteNormalizationModelIdeal f q p := by
      congr 1
      · funext i
        exact hf₀ i
      · funext j
        exact hq₀ j
      · funext i
        exact hmap_p₀ i
    rw [hmapmodel]
    exact hmodel
  · exact finite_finiteNormalizationModelAlgHom f₀ q₀ p₀ hp₀

/-- The form used when `f` already generates the generic target ideal and
the displayed normalization relations are known to vanish on it. -/
theorem exists_vertical_finite_normalization_model
    {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {N d r : ℕ}
    (f : Fin r → MvPolynomial (Fin N) K)
    (q : Fin d → MvPolynomial (Fin N) K)
    (p : Fin N → (MvPolynomial (Fin d) K)[X])
    (hmonic : ∀ i, (p i).Monic)
    (P : Ideal (MvPolynomial (Fin N) K))
    (hspan : Ideal.span (Set.range f) = P)
    (hrel : ∀ i, normalizationCoordinateRelation q p i ∈ P) :
    ∃ (Δ : R) (hΔ : Δ ≠ 0),
      ∃ f₀ : Fin r → MvPolynomial (Fin N) (Localization.Away Δ),
      ∃ q₀ : Fin d → MvPolynomial (Fin N) (Localization.Away Δ),
      ∃ p₀ : Fin N →
          (MvPolynomial (Fin d) (Localization.Away Δ))[X],
        (∀ i, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (f₀ i) = f i) ∧
        (∀ j, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (q₀ j) = q j) ∧
        (∀ i, (p₀ i).Monic) ∧
        (∀ i, Polynomial.map
          (MvPolynomial.map
            (awayToFractionRing (R := R) (K := K) Δ hΔ))
          (p₀ i) = p i) ∧
        Ideal.map
            (MvPolynomial.map
              (awayToFractionRing (R := R) (K := K) Δ hΔ))
            (finiteNormalizationModelIdeal f₀ q₀ p₀) = P ∧
        (finiteNormalizationModelAlgHom f₀ q₀ p₀).Finite := by
  exact exists_vertical_finite_normalization_model_of_modelIdeal_eq
    f q p hmonic P
      (finiteNormalizationModelIdeal_eq_of_span_eq
        f q p P hspan hrel)

end

end TranslatedDepthSeven
