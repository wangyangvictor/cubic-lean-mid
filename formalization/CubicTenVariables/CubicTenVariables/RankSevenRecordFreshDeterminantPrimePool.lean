import TranslatedDepthSeven.RankSevenPersistentRecords
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Fresh determinant primes after fixing a persistent record

Once a persistent record has been fixed, its modulus uses exactly `poolDepth`
primes from the original pool.  The determinant argument must use primes that
do not divide that fixed modulus.  This file makes the literal choice

`Pdet = Ppool \ record.modulus.primeFactors`

and records the finite-set facts needed to feed it to the independent-prime
version of the fixed-surface estimate.

There is no new number-theoretic or geometric input here.  The only room
hypothesis is the sharp finite statement
`poolDepth + detDepth <= Ppool.card`.
-/

set_option autoImplicit false

noncomputable section

namespace TranslatedDepthSeven

/-- A reservoir product formed from a smaller prime pool is also a reservoir
product of the same depth in every larger pool. -/
theorem mem_modulusReservoir_of_subset
    {P Q : Finset ℕ} (hPQ : P ⊆ Q) {depth q : ℕ}
    (hq : q ∈ modulusReservoir P depth) :
    q ∈ modulusReservoir Q depth := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hsSpec := Finset.mem_powersetCard.mp hs
  exact Finset.mem_image.mpr ⟨s, Finset.mem_powersetCard.mpr
    ⟨fun p hp ↦ hPQ (hsSpec.1 hp), hsSpec.2⟩, rfl⟩

/-- The unused primes of the original pool after fixing one persistent
record. -/
def recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    Finset ℕ :=
  Ppool \ record.modulus.1.primeFactors

theorem recordFreshDeterminantPrimePool_subset
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    recordFreshDeterminantPrimePool record ⊆ Ppool := by
  exact Finset.sdiff_subset

theorem prime_of_mem_recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    {p : ℕ} (hp : p ∈ recordFreshDeterminantPrimePool record) :
    p.Prime := by
  exact hPpool p (Finset.mem_sdiff.mp hp).1

/-- The fixed record modulus has exactly the advertised set and number of
prime factors. -/
theorem recordModulus_primeFactors_spec
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    record.modulus.1.primeFactors ⊆ Ppool ∧
      record.modulus.1.primeFactors.card = poolDepth ∧
      primeProduct record.modulus.1.primeFactors = record.modulus.1 := by
  exact primeFactors_spec_of_mem_modulusReservoir hPpool record.modulus.2

/-- Every prime left in the fresh pool is prime to the fixed record modulus
at the level required by the determinant theorem. -/
theorem not_dvd_recordModulus_of_mem_recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    {p : ℕ} (hp : p ∈ recordFreshDeterminantPrimePool record) :
    ¬ p ∣ record.modulus.1 := by
  intro hpdvd
  have hspec := recordModulus_primeFactors_spec hPpool record
  have hmodulus_ne : record.modulus.1 ≠ 0 := by
    rw [← hspec.2.2]
    exact primeProduct_ne_zero (fun q hq ↦ hPpool q (hspec.1 hq))
  have hpFactor : p ∈ record.modulus.1.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨prime_of_mem_recordFreshDeterminantPrimePool hPpool record hp,
        hpdvd, hmodulus_ne⟩
  exact (Finset.mem_sdiff.mp hp).2 hpFactor

/-- Equivalently, the entire fresh squarefree prime product is coprime to
the record modulus. -/
theorem primeProduct_recordFreshDeterminantPrimePool_coprime_recordModulus
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    Nat.Coprime (primeProduct (recordFreshDeterminantPrimePool record))
      record.modulus.1 := by
  rw [primeProduct, Nat.coprime_prod_left_iff]
  intro p hp
  exact (prime_of_mem_recordFreshDeterminantPrimePool hPpool record hp).coprime_iff_not_dvd.mpr
    (not_dvd_recordModulus_of_mem_recordFreshDeterminantPrimePool
      hPpool record hp)

/-- Removing the fixed record factors loses exactly `poolDepth` primes. -/
theorem card_recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount) :
    (recordFreshDeterminantPrimePool record).card =
      Ppool.card - poolDepth := by
  have hspec := recordModulus_primeFactors_spec hPpool record
  rw [recordFreshDeterminantPrimePool,
    Finset.card_sdiff_of_subset hspec.1, hspec.2.1]

/-- The exact room condition for choosing `detDepth` fresh determinant
primes. -/
theorem detDepth_le_card_recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount detDepth : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hroom : poolDepth + detDepth ≤ Ppool.card) :
    detDepth ≤ (recordFreshDeterminantPrimePool record).card := by
  rw [card_recordFreshDeterminantPrimePool hPpool record]
  omega

/-- In particular, a pool twice as large as the record depth leaves a
second reservoir of the same depth. -/
theorem poolDepth_le_card_recordFreshDeterminantPrimePool
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hroom : 2 * poolDepth ≤ Ppool.card) :
    poolDepth ≤ (recordFreshDeterminantPrimePool record).card := by
  apply detDepth_le_card_recordFreshDeterminantPrimePool hPpool record
  omega

/-- The fresh determinant reservoir is inhabited under the exact room
hypothesis. -/
theorem recordFresh_modulusReservoir_nonempty
    {Ppool : Finset ℕ} {poolDepth markCount detDepth : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hroom : poolDepth + detDepth ≤ Ppool.card) :
    (modulusReservoir (recordFreshDeterminantPrimePool record)
      detDepth).Nonempty := by
  have hdepth := detDepth_le_card_recordFreshDeterminantPrimePool
    hPpool record hroom
  obtain ⟨s, hs⟩ := Finset.powersetCard_nonempty.mpr hdepth
  exact ⟨primeProduct s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩

/-- Exact size of the fresh modulus reservoir. -/
theorem card_recordFresh_modulusReservoir
    {Ppool : Finset ℕ} {poolDepth markCount : ℕ}
    (hPpool : ∀ p ∈ Ppool, p.Prime)
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (detDepth : ℕ) :
    (modulusReservoir (recordFreshDeterminantPrimePool record)
      detDepth).card = Nat.choose (Ppool.card - poolDepth) detDepth := by
  calc
    (modulusReservoir (recordFreshDeterminantPrimePool record)
        detDepth).card =
        Nat.choose (recordFreshDeterminantPrimePool record).card detDepth :=
      card_modulusReservoir_of_primes
        (fun p hp ↦ prime_of_mem_recordFreshDeterminantPrimePool
          hPpool record hp) detDepth
    _ = Nat.choose (Ppool.card - poolDepth) detDepth := by
      rw [card_recordFreshDeterminantPrimePool hPpool record]

/-- Any lower bound already known for all depth-`detDepth` products from
the original pool restricts verbatim to the fresh determinant pool. -/
theorem recordFresh_modulusReservoir_lower_bound
    {Ppool : Finset ℕ} {poolDepth markCount detDepth B : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hlower : ∀ q : ReservoirModulus Ppool detDepth, B ≤ q.1) :
    ∀ q : ReservoirModulus (recordFreshDeterminantPrimePool record)
        detDepth,
      B ≤ q.1 := by
  intro q
  exact hlower ⟨q.1, mem_modulusReservoir_of_subset
    (recordFreshDeterminantPrimePool_subset record) q.2⟩

/-- The exact adapter from the surface index's subtype-form lower bound to
the raw membership-form lower bound expected by the decoupled determinant
theorem. -/
theorem recordFresh_modulusReservoir_lower_bound_raw_of_subtype
    {Ppool : Finset ℕ} {poolDepth markCount detDepth B : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hlower : ∀ q : ReservoirModulus Ppool detDepth, B ≤ q.1) :
    ∀ q ∈ modulusReservoir
        (recordFreshDeterminantPrimePool record) detDepth,
      B ≤ q := by
  intro q hq
  exact recordFresh_modulusReservoir_lower_bound record hlower ⟨q, hq⟩

/-- The same inheritance in the raw finite-set form used by the decoupled
surface theorem. -/
theorem recordFresh_modulusReservoir_lower_bound_raw
    {Ppool : Finset ℕ} {poolDepth markCount detDepth B : ℕ}
    (record : RankSevenPersistentRecord Ppool poolDepth markCount)
    (hlower : ∀ q ∈ modulusReservoir Ppool detDepth, B ≤ q) :
    ∀ q ∈ modulusReservoir
        (recordFreshDeterminantPrimePool record) detDepth,
      B ≤ q := by
  intro q hq
  exact hlower q (mem_modulusReservoir_of_subset
    (recordFreshDeterminantPrimePool_subset record) hq)

end TranslatedDepthSeven
