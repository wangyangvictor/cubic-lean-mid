import TranslatedDepthSeven.FiniteComponentFrontier
import TranslatedDepthSeven.FiniteSmoothLocusCover

/-!
# The singular-complement dimension step

For a finitely presented domain over a base ring, define the ideal of the
closed complement of the smooth locus literally by its vanishing ideal.  If
the smooth locus is nonempty, this ideal strictly contains zero.  Every prime
in the complement contains one of its finitely many minimal primes, and each
such minimal component has strictly smaller Krull dimension when the domain
has a stated finite dimension.

This is the qualitative dimension devissage.  It gives no degree or
coefficient-height bound for the singular-locus ideal or its components.
-/

namespace TranslatedDepthSeven

noncomputable section

open TopologicalSpace

universe u v

/-- The radical ideal defining the closed complement of the smooth locus. -/
def singularLocusIdeal
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] : Ideal A :=
  PrimeSpectrum.vanishingIdeal (Algebra.smoothLocus R A)ᶜ

/-- The zero locus of `singularLocusIdeal` is exactly the complement of the
smooth locus for a finitely presented algebra. -/
theorem zeroLocus_singularLocusIdeal
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    PrimeSpectrum.zeroLocus (singularLocusIdeal R A) =
      (Algebra.smoothLocus R A)ᶜ := by
  rw [singularLocusIdeal,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    Algebra.isOpen_smoothLocus.isClosed_compl.closure_eq]

/-- On a domain with a nonempty smooth locus, its singular-locus ideal is
strictly larger than the zero ideal. -/
theorem bot_lt_singularLocusIdeal_of_nonempty_smoothLocus
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (hsmooth : (Algebra.smoothLocus R A).Nonempty) :
    (⊥ : Ideal A) < singularLocusIdeal R A := by
  obtain ⟨p, hp⟩ := hsmooth
  have hproper : (Algebra.smoothLocus R A)ᶜ ⊂
      (Set.univ : Set (PrimeSpectrum A)) := by
    refine ⟨Set.subset_univ _, ?_⟩
    intro hreverse
    have hpcompl : p ∈ (Algebra.smoothLocus R A)ᶜ := by
      exact hreverse (Set.mem_univ p)
    exact hpcompl hp
  have hstrict :=
    (PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff
      Algebra.isOpen_smoothLocus.isClosed_compl isClosed_univ).mp hproper
  simpa [singularLocusIdeal, PrimeSpectrum.vanishingIdeal_univ,
    (nilradical_eq_bot_iff.mpr inferInstance)] using hstrict

/-- The finite list of irreducible components of the singular complement. -/
def finiteSingularLocusComponents
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    Finset (Ideal A) :=
  finiteMinimalPrimes (singularLocusIdeal R A)

@[simp]
theorem mem_finiteSingularLocusComponents_iff
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing A]
    (L : Ideal A) :
    L ∈ finiteSingularLocusComponents R A ↔
      L ∈ (singularLocusIdeal R A).minimalPrimes := by
  simp [finiteSingularLocusComponents, finiteMinimalPrimes]

/-- Every prime in the nonsmooth complement contains one of the finite
minimal components of that complement. -/
theorem exists_finiteSingularLocusComponent_le
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) (hp : p ∉ Algebra.smoothLocus R A) :
    ∃ L ∈ finiteSingularLocusComponents R A, L ≤ p.asIdeal := by
  have hpzero : p ∈ PrimeSpectrum.zeroLocus (singularLocusIdeal R A) := by
    rw [zeroLocus_singularLocusIdeal]
    exact hp
  have hle : singularLocusIdeal R A ≤ p.asIdeal := by
    exact hpzero
  change ∃ L ∈ finiteMinimalPrimes (singularLocusIdeal R A),
    L ≤ p.asIdeal
  exact exists_finiteMinimalPrime_le hle

/-- Every irreducible component of the singular complement has strictly
smaller dimension than a finite-dimensional domain with a nonempty smooth
locus. -/
theorem ringKrullDim_singularComponent_lt
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing A]
    (hsmooth : (Algebra.smoothLocus R A).Nonempty)
    {L : Ideal A} (hL : L ∈ finiteSingularLocusComponents R A)
    {s : ℕ} (hdim : ringKrullDim A = s) :
    ringKrullDim (A ⧸ L) < s := by
  have hJle : singularLocusIdeal R A ≤ L :=
    le_of_mem_finiteMinimalPrimes hL
  have hbotL : (⊥ : Ideal A) < L :=
    (bot_lt_singularLocusIdeal_of_nonempty_smoothLocus
      R A hsmooth).trans_le hJle
  letI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
  letI : L.IsPrime := isPrime_of_mem_finiteMinimalPrimes hL
  have hbotdim : ringKrullDim (A ⧸ (⊥ : Ideal A)) = s :=
    (RingEquiv.ringKrullDim (RingEquiv.quotientBot A)).trans hdim
  have hfinite : ringKrullDim (A ⧸ (⊥ : Ideal A)) < ⊤ := by
    rw [hbotdim]
    change (↑(s : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top s)
  have hdrop := ringKrullDim_quotient_lt_of_prime_lt
    (⊥ : Ideal A) L hbotL hfinite
  rwa [hbotdim] at hdrop

end

end TranslatedDepthSeven
