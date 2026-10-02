import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Spreading a generic-fibre component through localization

The generic fibre of an affine family over a domain is obtained by
localizing its equation ring at the nonzero elements of the base.  This file
records the precise commutative-algebra fact needed by the vertical
construction: a minimal component of the localized equation ideal contracts
to a minimal component before localization, and is recovered exactly by
mapping that contraction back to the localization.

No Hilbert scheme or relative component space enters this statement.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
  (S : Submonoid R) [Algebra R A] [IsLocalization S A]

include S

/-- A minimal component after localization is the localization of its
contracted minimal component. -/
theorem localization_minimalComponent_contracts
    (I : Ideal R) (Q : Ideal A)
    (hQ : Q ∈ (I.map (algebraMap R A)).minimalPrimes) :
    Q.comap (algebraMap R A) ∈ I.minimalPrimes ∧
      (Q.comap (algebraMap R A)).map (algebraMap R A) = Q := by
  have hcontract : Q.comap (algebraMap R A) ∈ I.minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map S A] at hQ
    exact hQ
  exact ⟨hcontract, IsLocalization.map_comap S A Q⟩

/-- Conversely, a minimal component disjoint from the multiplicative set
remains a minimal component after localization, and contracts back exactly.
-/
theorem localization_minimalComponent_maps
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes)
    (hdisj : Disjoint (S : Set R) P) :
    P.map (algebraMap R A) ∈ (I.map (algebraMap R A)).minimalPrimes ∧
      (P.map (algebraMap R A)).comap (algebraMap R A) = P := by
  have hprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint S A P hprime hdisj
  have hmap : P.map (algebraMap R A) ∈
      (I.map (algebraMap R A)).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map S A]
    simpa [hcomap] using hP
  exact ⟨hmap, hcomap⟩

end

end TranslatedDepthSeven
