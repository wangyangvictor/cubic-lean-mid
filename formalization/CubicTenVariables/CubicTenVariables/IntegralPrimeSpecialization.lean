import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Prime quotient specialization of an integral injective normalization.
Lying-over supplies the missing lower dimension inequality: no flatness,
reducedness, or constancy-of-dimension premise is needed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.IntegralPrimeSpecialization

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Algebra R S] [Algebra.IsIntegral R S]

/-- An extended prime ideal contracts to itself for an integral injection. -/
theorem comap_map_prime (hinj : Function.Injective (algebraMap R S))
    (P : Ideal R) [P.IsPrime] :
    (P.map (algebraMap R S)).comap (algebraMap R S) = P := by
  obtain ⟨Q, _, _hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S) (by
      rw [Ideal.comap_bot_of_injective _ hinj]
      exact bot_le)
  apply le_antisymm _ Ideal.le_comap_map
  have hPQ : P.map (algebraMap R S) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr hQP.ge
  exact (Ideal.comap_mono hPQ).trans hQP.le

/-- The map of prime quotients remains injective. -/
theorem quotientMap_injective (hinj : Function.Injective (algebraMap R S))
    (P : Ideal R) [P.IsPrime] :
    Function.Injective
      (Ideal.quotientMap (P.map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map) :=
  Ideal.quotientMap_injective' (comap_map_prime hinj P).le

/-- Prime quotient specialization preserves the dimension of the source
of an integral injective map, even when the target quotient is not reduced. -/
theorem quotient_ringKrullDim_eq
    (hinj : Function.Injective (algebraMap R S))
    (P : Ideal R) [P.IsPrime] :
    ringKrullDim (S ⧸ P.map (algebraMap R S)) = ringKrullDim (R ⧸ P) := by
  have hcontract := comap_map_prime hinj P
  have hproper : P.map (algebraMap R S) ≠ ⊤ := by
    intro htop
    rw [htop, Ideal.comap_top] at hcontract
    exact (inferInstance : P.IsPrime).ne_top hcontract.symm
  letI : Nontrivial (S ⧸ P.map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : Nontrivial (R ⧸ (P.map (algebraMap R S)).comap (algebraMap R S)) := by
    rw [hcontract]
    infer_instance
  have heq := TranslatedDepthSeven.ringKrullDim_eq_of_isIntegral_injective
    (R := R ⧸ (P.map (algebraMap R S)).comap (algebraMap R S))
    (S := S ⧸ P.map (algebraMap R S))
    (Ideal.quotientMap_injective (I := P.map (algebraMap R S))
      (f := algebraMap R S))
  exact heq.trans (ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hcontract))

/-- An integral injection remains injective in a surjective specialization
square when the target kernel is the extension of the source prime kernel. -/
theorem specialized_injective
    {R' S' : Type*} [CommRing R'] [IsDomain R'] [CommRing S']
    (hinj : Function.Injective (algebraMap R S))
    (a : R →+* R') (b : S →+* S') (g : R' →+* S')
    (ha : Function.Surjective a)
    (hcomm : b.comp (algebraMap R S) = g.comp a)
    (hker : RingHom.ker b = (RingHom.ker a).map (algebraMap R S)) :
    Function.Injective g := by
  letI : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  apply (injective_iff_map_eq_zero g).mpr
  intro x hx
  obtain ⟨r, rfl⟩ := ha x
  have hr : algebraMap R S r ∈ RingHom.ker b := by
    change b (algebraMap R S r) = 0
    exact (RingHom.congr_fun hcomm r).trans hx
  rw [hker] at hr
  have hmem : r ∈ ((RingHom.ker a).map (algebraMap R S)).comap
      (algebraMap R S) := hr
  rw [comap_map_prime hinj (RingHom.ker a)] at hmem
  exact hmem

/-- Integrality descends through a surjective target specialization. -/
theorem specialized_isIntegral
    {R' S' : Type*} [CommRing R'] [CommRing S']
    (a : R →+* R') (b : S →+* S') (g : R' →+* S')
    (hb : Function.Surjective b)
    (hcomm : b.comp (algebraMap R S) = g.comp a) :
    g.IsIntegral := by
  have h : (b.comp (algebraMap R S)).IsIntegral :=
    RingHom.IsIntegral.trans (algebraMap R S) b
      Algebra.IsIntegral.isIntegral (b.isIntegral_of_surjective hb)
  rw [hcomm] at h
  exact RingHom.IsIntegral.tower_top a g h

/-- Exact dimension equality in the same specialization square. -/
theorem specialized_ringKrullDim_eq
    {R' S' : Type*} [CommRing R'] [IsDomain R'] [CommRing S']
    (hinj : Function.Injective (algebraMap R S))
    (a : R →+* R') (b : S →+* S') (g : R' →+* S')
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hcomm : b.comp (algebraMap R S) = g.comp a)
    (hker : RingHom.ker b = (RingHom.ker a).map (algebraMap R S)) :
    ringKrullDim S' = ringKrullDim R' := by
  have hg := specialized_injective hinj a b g ha hcomm hker
  letI : Nontrivial S' := hg.nontrivial
  letI : Algebra R' S' := g.toAlgebra
  letI : Algebra.IsIntegral R' S' := ⟨specialized_isIntegral a b g hb hcomm⟩
  exact TranslatedDepthSeven.ringKrullDim_eq_of_isIntegral_injective hg

end CubicTenVariables.IntegralPrimeSpecialization
