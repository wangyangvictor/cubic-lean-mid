import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Monic
import TranslatedDepthSeven.FiniteCoefficientDescent

/-!
# One denominator for finitely many fraction-field coefficients

A finite family in the fraction field of a domain is defined over one
principal localization of the domain.  The denominator below is the
literal product of denominators for the displayed family.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

universe u v

theorem fractionRing_algebraMap_ne_zero
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {d : R} (hd : d ≠ 0) : algebraMap R K d ≠ 0 := by
  intro hzero
  apply hd
  apply IsLocalization.injective K (M := R⁰) le_rfl
  simpa only [map_zero] using hzero

/-- The canonical map from one principal localization of a domain to a
chosen fraction field. -/
noncomputable def awayToFractionRing
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (d : R) (hd : d ≠ 0) : Localization.Away d →+* K :=
  IsLocalization.Away.lift d <|
    isUnit_iff_ne_zero.mpr <|
      fractionRing_algebraMap_ne_zero hd

@[simp]
theorem awayToFractionRing_algebraMap
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (d : R) (hd : d ≠ 0) (r : R) :
    awayToFractionRing d hd (algebraMap R (Localization.Away d) r) =
      algebraMap R K r := by
  simpa only [awayToFractionRing] using
    (IsLocalization.Away.lift_eq
      (S := Localization.Away d) d
      (isUnit_iff_ne_zero.mpr <|
        fractionRing_algebraMap_ne_zero hd) r)

/-- A finite family of fraction-field elements lies in the image of one
principal localization.  No denominator is hidden: `d` is chosen as the
product of one nonzero denominator for each member of the family. -/
theorem exists_common_principal_denominator_fintype
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ (d : R) (hd : d ≠ 0),
      ∀ i, ∃ y : Localization.Away d,
        awayToFractionRing d hd y = c i := by
  classical
  choose a b hb hfrac using fun i ↦
    IsFractionRing.div_surjective (A := R) (c i)
  let d : R := ∏ i, b i
  have hd : d ≠ 0 := by
    simp only [d, Finset.prod_ne_zero_iff]
    intro i _hi
    exact mem_nonZeroDivisors_iff_ne_zero.mp (hb i)
  refine ⟨d, hd, ?_⟩
  intro i
  have hbid : b i ∣ d := by
    exact Finset.dvd_prod_of_mem b (Finset.mem_univ i)
  have hunit :
      IsUnit (algebraMap R (Localization.Away d) (b i)) :=
    IsLocalization.Away.isUnit_of_dvd
      (S := Localization.Away d) (x := d) hbid
  let u : (Localization.Away d)ˣ := hunit.unit
  let y : Localization.Away d :=
    algebraMap R (Localization.Away d) (a i) * ↑(u⁻¹)
  refine ⟨y, ?_⟩
  rw [← hfrac i]
  apply (eq_div_iff (fractionRing_algebraMap_ne_zero
    (mem_nonZeroDivisors_iff_ne_zero.mp (hb i)))).mpr
  have hu : (↑u : Localization.Away d) =
      algebraMap R (Localization.Away d) (b i) := hunit.unit_spec
  change awayToFractionRing d hd y * algebraMap R K (b i) =
    algebraMap R K (a i)
  rw [← awayToFractionRing_algebraMap d hd (b i), ← hu]
  simp [y]
  have hmapu :
      awayToFractionRing (R := R) (K := K) d hd (↑u) ≠ 0 :=
    (u.isUnit.map
      (awayToFractionRing (R := R) (K := K) d hd)).ne_zero
  rw [mul_assoc, inv_mul_cancel₀ hmapu, mul_one]

/-- Restrict the coefficients of one multivariate polynomial along a ring
map when literal preimages of all coefficients are supplied. -/
noncomputable def mvPolynomialOverRingHomRange
    {σ : Type*} {S T : Type*} [CommRing S] [CommRing T]
    (phi : S →+* T) (p : MvPolynomial σ T)
    (hcoeff : ∀ m, ∃ a : S, phi a = MvPolynomial.coeff m p) :
    MvPolynomial σ S :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial m (Classical.choose (hcoeff m))

/-- Coefficient extension of the preceding restricted polynomial recovers
the original polynomial exactly. -/
theorem map_mvPolynomialOverRingHomRange
    {σ : Type*} {S T : Type*} [CommRing S] [CommRing T]
    (phi : S →+* T) (p : MvPolynomial σ T)
    (hcoeff : ∀ m, ∃ a : S, phi a = MvPolynomial.coeff m p) :
    MvPolynomial.map phi (mvPolynomialOverRingHomRange phi p hcoeff) = p := by
  rw [mvPolynomialOverRingHomRange]
  simp only [map_sum, MvPolynomial.map_monomial]
  have hcoeff' : ∀ m,
      phi (Classical.choose (hcoeff m)) = MvPolynomial.coeff m p :=
    fun m ↦ Classical.choose_spec (hcoeff m)
  simp_rw [hcoeff']
  exact (MvPolynomial.as_sum p).symm

/-- A finite multivariate-polynomial family over a fraction field is
defined over one principal localization of the domain. -/
theorem exists_common_principal_model_mvPolynomial_family
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {σ : Type*} {n : ℕ} (f : Fin n → MvPolynomial σ K) :
    ∃ (d : R) (hd : d ≠ 0),
      ∃ f₀ : Fin n → MvPolynomial σ (Localization.Away d),
        ∀ i, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) d hd) (f₀ i) = f i := by
  classical
  let C : Finset K := finitePolynomialFamilyCoefficients f
  obtain ⟨d, hd, hC⟩ :=
    exists_common_principal_denominator_fintype
      (R := R) (K := K) (fun z : C ↦ (z : K))
  have hcoeff : ∀ i m,
      ∃ a : Localization.Away d,
        awayToFractionRing (R := R) (K := K) d hd a =
          MvPolynomial.coeff m (f i) := by
    intro i m
    by_cases hzero : MvPolynomial.coeff m (f i) = 0
    · refine ⟨0, ?_⟩
      simp only [map_zero, hzero]
    · have hmem : MvPolynomial.coeff m (f i) ∈ C := by
        change MvPolynomial.coeff m (f i) ∈
          finitePolynomialFamilyCoefficients f
        rw [finitePolynomialFamilyCoefficients, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i,
          MvPolynomial.coeff_mem_coeffs m hzero⟩
      exact hC ⟨MvPolynomial.coeff m (f i), hmem⟩
  let f₀ : Fin n → MvPolynomial σ (Localization.Away d) :=
    fun i ↦ mvPolynomialOverRingHomRange
      (awayToFractionRing (R := R) (K := K) d hd) (f i) (hcoeff i)
  refine ⟨d, hd, f₀, ?_⟩
  intro i
  exact map_mvPolynomialOverRingHomRange
    (awayToFractionRing (R := R) (K := K) d hd) (f i) (hcoeff i)

/-- The canonical map from a principal localization of a domain into its
fraction field is injective. -/
theorem awayToFractionRing_injective
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (d : R) (hd : d ≠ 0) :
    Function.Injective (awayToFractionRing (R := R) (K := K) d hd) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers d)]
  intro x y
  constructor
  · intro h
    simpa only [awayToFractionRing_algebraMap] using
      congrArg (awayToFractionRing (R := R) (K := K) d hd) h
  · intro h
    have hxy : x = y := by
      apply IsLocalization.injective K (M := R⁰) le_rfl
      simpa only [awayToFractionRing_algebraMap] using h
    rw [hxy]

/-- Viewing an `Option`-indexed multivariate polynomial as a polynomial in
one distinguished variable commutes with coefficient extension. -/
theorem map_optionEquivLeft
    {S T σ : Type*} [CommRing S] [CommRing T]
    (phi : S →+* T) (f : MvPolynomial (Option σ) S) :
    Polynomial.map (MvPolynomial.map phi)
        (MvPolynomial.optionEquivLeft S σ f) =
      MvPolynomial.optionEquivLeft T σ (MvPolynomial.map phi f) := by
  ext i m
  simp only [Polynomial.coeff_map, MvPolynomial.coeff_map]
  have hs :
      MvPolynomial.coeff m
          ((MvPolynomial.optionEquivLeft S σ f).coeff i) =
        MvPolynomial.coeff (m.optionElim i) f := by
    simpa only [Finsupp.some_optionElim,
      Finsupp.optionElim_apply_none] using
      (MvPolynomial.optionEquivLeft_coeff_coeff
        S σ (m.optionElim i) f)
  have ht :
      MvPolynomial.coeff m
          ((MvPolynomial.optionEquivLeft T σ
            (MvPolynomial.map phi f)).coeff i) =
        MvPolynomial.coeff (m.optionElim i)
          (MvPolynomial.map phi f) := by
    simpa only [Finsupp.some_optionElim,
      Finsupp.optionElim_apply_none] using
      (MvPolynomial.optionEquivLeft_coeff_coeff
        T σ (m.optionElim i) (MvPolynomial.map phi f))
  rw [hs, ht, MvPolynomial.coeff_map]

/-- Two finite polynomial families, even with different variable sets,
are simultaneously defined over one principal localization.  The
denominator is obtained from the union of their literal coefficient
sets. -/
theorem exists_common_principal_model_two_mvPolynomial_families
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {σ τ : Type*} {n m : ℕ}
    (f : Fin n → MvPolynomial σ K)
    (g : Fin m → MvPolynomial τ K) :
    ∃ (Δ : R) (hΔ : Δ ≠ 0),
      ∃ f₀ : Fin n → MvPolynomial σ (Localization.Away Δ),
      ∃ g₀ : Fin m → MvPolynomial τ (Localization.Away Δ),
        (∀ i, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (f₀ i) = f i) ∧
        ∀ j, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (g₀ j) = g j := by
  classical
  let C : Finset K :=
    finitePolynomialFamilyCoefficients f ∪
      finitePolynomialFamilyCoefficients g
  obtain ⟨Δ, hΔ, hC⟩ :=
    exists_common_principal_denominator_fintype
      (R := R) (K := K) (fun z : C ↦ (z : K))
  have hcoeff_f : ∀ i a,
      ∃ c : Localization.Away Δ,
        awayToFractionRing (R := R) (K := K) Δ hΔ c =
          MvPolynomial.coeff a (f i) := by
    intro i a
    by_cases hzero : MvPolynomial.coeff a (f i) = 0
    · exact ⟨0, by simp only [map_zero, hzero]⟩
    · have hmem : MvPolynomial.coeff a (f i) ∈ C := by
        apply Finset.mem_union_left
        rw [finitePolynomialFamilyCoefficients, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ i,
          MvPolynomial.coeff_mem_coeffs a hzero⟩
      exact hC ⟨MvPolynomial.coeff a (f i), hmem⟩
  have hcoeff_g : ∀ j a,
      ∃ c : Localization.Away Δ,
        awayToFractionRing (R := R) (K := K) Δ hΔ c =
          MvPolynomial.coeff a (g j) := by
    intro j a
    by_cases hzero : MvPolynomial.coeff a (g j) = 0
    · exact ⟨0, by simp only [map_zero, hzero]⟩
    · have hmem : MvPolynomial.coeff a (g j) ∈ C := by
        apply Finset.mem_union_right
        rw [finitePolynomialFamilyCoefficients, Finset.mem_biUnion]
        exact ⟨j, Finset.mem_univ j,
          MvPolynomial.coeff_mem_coeffs a hzero⟩
      exact hC ⟨MvPolynomial.coeff a (g j), hmem⟩
  let f₀ : Fin n → MvPolynomial σ (Localization.Away Δ) :=
    fun i ↦ mvPolynomialOverRingHomRange
      (awayToFractionRing (R := R) (K := K) Δ hΔ)
      (f i) (hcoeff_f i)
  let g₀ : Fin m → MvPolynomial τ (Localization.Away Δ) :=
    fun j ↦ mvPolynomialOverRingHomRange
      (awayToFractionRing (R := R) (K := K) Δ hΔ)
      (g j) (hcoeff_g j)
  refine ⟨Δ, hΔ, f₀, g₀, ?_, ?_⟩
  · intro i
    exact map_mvPolynomialOverRingHomRange
      (awayToFractionRing (R := R) (K := K) Δ hΔ)
      (f i) (hcoeff_f i)
  · intro j
    exact map_mvPolynomialOverRingHomRange
      (awayToFractionRing (R := R) (K := K) Δ hΔ)
      (g j) (hcoeff_g j)

/-- A finite family of monic polynomials over a polynomial ring with
fraction-field coefficients descends, after inverting one nonzero base
element, to a family of monic polynomials.  Mapping all scalar
coefficients back to the fraction field recovers the original family
exactly. -/
theorem exists_common_principal_model_monic_polynomial_family
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {d n : ℕ}
    (p : Fin n → Polynomial (MvPolynomial (Fin d) K))
    (hp : ∀ i, (p i).Monic) :
    ∃ (Δ : R) (hΔ : Δ ≠ 0),
      ∃ p₀ : Fin n →
          Polynomial (MvPolynomial (Fin d) (Localization.Away Δ)),
        (∀ i, (p₀ i).Monic) ∧
        ∀ i,
          Polynomial.map
              (MvPolynomial.map
                (awayToFractionRing (R := R) (K := K) Δ hΔ))
              (p₀ i) = p i := by
  let f : Fin n → MvPolynomial (Option (Fin d)) K :=
    fun i ↦ (MvPolynomial.optionEquivLeft K (Fin d)).symm (p i)
  obtain ⟨Δ, hΔ, f₀, hf₀⟩ :=
    exists_common_principal_model_mvPolynomial_family
      (R := R) (K := K) f
  let p₀ : Fin n →
      Polynomial (MvPolynomial (Fin d) (Localization.Away Δ)) :=
    fun i ↦ MvPolynomial.optionEquivLeft
      (Localization.Away Δ) (Fin d) (f₀ i)
  refine ⟨Δ, hΔ, p₀, ?_, ?_⟩
  · intro i
    apply Polynomial.monic_of_injective
      (MvPolynomial.map_injective
        (awayToFractionRing (R := R) (K := K) Δ hΔ)
        (awayToFractionRing_injective Δ hΔ))
    rw [map_optionEquivLeft, hf₀ i]
    simpa only [f,
      (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply]
      using hp i
  · intro i
    change Polynomial.map
        (MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ))
        (MvPolynomial.optionEquivLeft
          (Localization.Away Δ) (Fin d) (f₀ i)) = p i
    rw [map_optionEquivLeft, hf₀ i]
    exact (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply (p i)

/-- One principal localization simultaneously carries a displayed finite
normalization map and a finite family of monic coordinate relations.
This is the literal finite-data spreading statement used in the vertical
argument: `q` supplies the normalization images and `p` supplies the
monic relations over its polynomial base. -/
theorem exists_common_principal_model_normalization_and_monic_relations
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {d N n : ℕ}
    (q : Fin d → MvPolynomial (Fin N) K)
    (p : Fin n → Polynomial (MvPolynomial (Fin d) K))
    (hp : ∀ i, (p i).Monic) :
    ∃ (Δ : R) (hΔ : Δ ≠ 0),
      ∃ q₀ : Fin d → MvPolynomial (Fin N) (Localization.Away Δ),
      ∃ p₀ : Fin n →
          Polynomial (MvPolynomial (Fin d) (Localization.Away Δ)),
        (∀ j, MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ) (q₀ j) = q j) ∧
        (∀ i, (p₀ i).Monic) ∧
        ∀ i, Polynomial.map
          (MvPolynomial.map
            (awayToFractionRing (R := R) (K := K) Δ hΔ))
          (p₀ i) = p i := by
  let f : Fin n → MvPolynomial (Option (Fin d)) K :=
    fun i ↦ (MvPolynomial.optionEquivLeft K (Fin d)).symm (p i)
  obtain ⟨Δ, hΔ, q₀, f₀, hq₀, hf₀⟩ :=
    exists_common_principal_model_two_mvPolynomial_families
      (R := R) (K := K) q f
  let p₀ : Fin n →
      Polynomial (MvPolynomial (Fin d) (Localization.Away Δ)) :=
    fun i ↦ MvPolynomial.optionEquivLeft
      (Localization.Away Δ) (Fin d) (f₀ i)
  refine ⟨Δ, hΔ, q₀, p₀, hq₀, ?_, ?_⟩
  · intro i
    apply Polynomial.monic_of_injective
      (MvPolynomial.map_injective
        (awayToFractionRing (R := R) (K := K) Δ hΔ)
        (awayToFractionRing_injective Δ hΔ))
    rw [map_optionEquivLeft, hf₀ i]
    simpa only [f,
      (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply]
      using hp i
  · intro i
    change Polynomial.map
        (MvPolynomial.map
          (awayToFractionRing (R := R) (K := K) Δ hΔ))
        (MvPolynomial.optionEquivLeft
          (Localization.Away Δ) (Fin d) (f₀ i)) = p i
    rw [map_optionEquivLeft, hf₀ i]
    exact (MvPolynomial.optionEquivLeft K (Fin d)).apply_symm_apply (p i)

end

end TranslatedDepthSeven
