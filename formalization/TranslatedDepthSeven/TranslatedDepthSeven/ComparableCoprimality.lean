import TranslatedDepthSeven.ComparablePrimePool
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Coprimality of the surviving comparable-prime products

The deletion construction removes precisely the selected primes which divide
an integer certificate.  This file proves, rather than merely uses, that the
fixed-cardinality products from the remaining pool are exactly the original
reservoir moduli coprime to that certificate.  The analogous statement for
two certificates is also recorded.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The primes of `P` which do not divide `D`. -/
def certificateAllowedPrimes (P : Finset ℕ) (D : ℤ) : Finset ℕ :=
  P.filter fun p ↦ ¬(p : ℤ) ∣ D

/-- The primes of `P` which divide neither of two certificates. -/
def certificateAllowedPrimesTwo (P : Finset ℕ) (D₁ D₂ : ℤ) : Finset ℕ :=
  P.filter fun p ↦ ¬(p : ℤ) ∣ D₁ ∧ ¬(p : ℤ) ∣ D₂

/-- A product of distinct listed primes is coprime to `|D|` exactly when none
of its listed prime factors divides the integer `D`. -/
theorem primeProduct_coprime_natAbs_iff
    {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) (D : ℤ) :
    Nat.Coprime (primeProduct s) D.natAbs ↔
      ∀ p ∈ s, ¬(p : ℤ) ∣ D := by
  rw [primeProduct, Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp hpd
    have hnot : ¬p ∣ D.natAbs :=
      (hprime p hp).coprime_iff_not_dvd.mp (h p hp)
    exact hnot (Int.natCast_dvd.mp hpd)
  · intro h p hp
    apply (hprime p hp).coprime_iff_not_dvd.mpr
    intro hpd
    exact h p hp (Int.natCast_dvd.mpr hpd)

/-- The direct, proof-parameter-free identification of the surviving prime
subsets with the reservoir moduli coprime to one certificate. -/
theorem subset_certificateAllowedPrimes_iff_coprime
    {P s : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hs : s ⊆ P) (D : ℤ) :
    s ⊆ certificateAllowedPrimes P D ↔
      Nat.Coprime (primeProduct s) D.natAbs := by
  rw [primeProduct_coprime_natAbs_iff
    (fun p hp ↦ hprime p (hs hp)) D]
  simp only [certificateAllowedPrimes, Finset.subset_iff, Finset.mem_filter]
  constructor
  · intro h p hp
    exact (h hp).2
  · intro h p hp
    exact ⟨hs hp, h p hp⟩

/-- The analogous identification for two certificates. -/
theorem subset_certificateAllowedPrimesTwo_iff_coprime
    {P s : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime)
    (hs : s ⊆ P) (D₁ D₂ : ℤ) :
    s ⊆ certificateAllowedPrimesTwo P D₁ D₂ ↔
      Nat.Coprime (primeProduct s) D₁.natAbs ∧
        Nat.Coprime (primeProduct s) D₂.natAbs := by
  rw [primeProduct_coprime_natAbs_iff
      (fun p hp ↦ hprime p (hs hp)) D₁,
    primeProduct_coprime_natAbs_iff
      (fun p hp ↦ hprime p (hs hp)) D₂]
  simp only [certificateAllowedPrimesTwo, Finset.subset_iff,
    Finset.mem_filter]
  constructor
  · intro h
    exact ⟨fun _ hp ↦ (h hp).2.1, fun _ hp ↦ (h hp).2.2⟩
  · rintro ⟨h₁, h₂⟩ p hp
    exact ⟨hs hp, h₁ p hp, h₂ p hp⟩

/-- Coprimality with two signed certificates is exactly coprimality with
their product.  This is the literal form used when the manuscript replaces
two exceptional-prime lists by one integer certificate. -/
theorem coprime_two_natAbs_iff_coprime_mul
    (q : ℕ) (D₁ D₂ : ℤ) :
    Nat.Coprime q D₁.natAbs ∧ Nat.Coprime q D₂.natAbs ↔
      Nat.Coprime q (D₁ * D₂).natAbs := by
  rw [Int.natAbs_mul]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact h₁.mul_right h₂
  · intro h
    exact ⟨h.of_dvd_right (dvd_mul_right D₁.natAbs D₂.natAbs),
      h.of_dvd_right (dvd_mul_left D₂.natAbs D₁.natAbs)⟩

/-- Within the chosen pool, deleting the primes recorded by one certificate
is literally equivalent to retaining products coprime to that certificate. -/
theorem subset_comparablePool_sdiff_bad_iff_coprime
    {x : ℝ} {M : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    {s : Finset ℕ}
    (hs : s ⊆ comparablePrimePool x M hM) (D : ℤ) :
    s ⊆ comparablePrimePool x M hM \
        comparableIntegerBadPrimes x M hM D ↔
      Nat.Coprime (primeProduct s) D.natAbs := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦
    prime_of_mem_comparablePrimePool (hs hp)
  rw [primeProduct_coprime_natAbs_iff hprime D]
  constructor
  · intro h p hp hpd
    have hnotbad := (Finset.mem_sdiff.mp (h hp)).2
    exact hnotbad (mem_comparableIntegerBadPrimes_iff.mpr ⟨hs hp, hpd⟩)
  · intro h p hp
    exact Finset.mem_sdiff.mpr ⟨hs hp, fun hbad ↦
      h p hp (mem_comparableIntegerBadPrimes_iff.mp hbad).2⟩

/-- Deleting the union of the prime divisors of two certificates is exactly
the conjunction of coprimality with their absolute values. -/
theorem subset_comparablePool_sdiff_badTwo_iff_coprime
    {x : ℝ} {M : ℕ}
    {hM : M ≤ (comparablePrimeCandidates x).card}
    {s : Finset ℕ}
    (hs : s ⊆ comparablePrimePool x M hM) (D₁ D₂ : ℤ) :
    s ⊆ comparablePrimePool x M hM \
        comparableIntegerBadPrimesTwo x M hM D₁ D₂ ↔
      Nat.Coprime (primeProduct s) D₁.natAbs ∧
        Nat.Coprime (primeProduct s) D₂.natAbs := by
  rw [← subset_comparablePool_sdiff_bad_iff_coprime hs D₁,
    ← subset_comparablePool_sdiff_bad_iff_coprime hs D₂]
  constructor
  · intro h
    constructor
    · intro p hp
      have hp' := Finset.mem_sdiff.mp (h hp)
      exact Finset.mem_sdiff.mpr ⟨hp'.1, fun hbad ↦
        hp'.2 (Finset.mem_union_left _ hbad)⟩
    · intro p hp
      have hp' := Finset.mem_sdiff.mp (h hp)
      exact Finset.mem_sdiff.mpr ⟨hp'.1, fun hbad ↦
        hp'.2 (Finset.mem_union_right _ hbad)⟩
  · rintro ⟨h₁, h₂⟩ p hp
    have hp₁ := Finset.mem_sdiff.mp (h₁ hp)
    have hp₂ := Finset.mem_sdiff.mp (h₂ hp)
    exact Finset.mem_sdiff.mpr ⟨hp₁.1, by
      rw [comparableIntegerBadPrimesTwo, Finset.mem_union]
      exact not_or_intro hp₁.2 hp₂.2⟩

end

end TranslatedDepthSeven
