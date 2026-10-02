import TranslatedDepthSeven.BertrandReservoir

/-!
# A finite pool selected from one comparable-prime interval

This file contains only finite-set combinatorics.  It assumes that the
interval `(floor x, floor (2x)]` contains at least `M` primes and selects
exactly `M` of them.  No assertion about how large `x` must be is made here.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- All primes in the natural-number interval
`(floor x, floor (2x)]`. -/
def comparablePrimeCandidates (x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊).filter Nat.Prime

theorem mem_comparablePrimeCandidates_iff {x : ℝ} {p : ℕ} :
    p ∈ comparablePrimeCandidates x ↔
      p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊2 * x⌋₊ := by
  simp only [comparablePrimeCandidates, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨hp, hlo, hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hlo, hhi⟩, hp⟩

/-- A fixed choice of exactly `M` primes in the comparable interval.  The
hypothesis is precisely the finite cardinality assertion needed to make the
choice. -/
def comparablePrimePool (x : ℝ) (M : ℕ)
    (hM : M ≤ (comparablePrimeCandidates x).card) : Finset ℕ :=
  Classical.choose (Finset.exists_subset_card_eq hM)

theorem comparablePrimePool_subset (x : ℝ) (M : ℕ)
    (hM : M ≤ (comparablePrimeCandidates x).card) :
    comparablePrimePool x M hM ⊆ comparablePrimeCandidates x :=
  (Classical.choose_spec (Finset.exists_subset_card_eq hM)).1

theorem card_comparablePrimePool (x : ℝ) (M : ℕ)
    (hM : M ≤ (comparablePrimeCandidates x).card) :
    (comparablePrimePool x M hM).card = M :=
  (Classical.choose_spec (Finset.exists_subset_card_eq hM)).2

theorem prime_and_bounds_of_mem_comparablePrimePool
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {p : ℕ} (hp : p ∈ comparablePrimePool x M hM) :
    p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊2 * x⌋₊ :=
  mem_comparablePrimeCandidates_iff.mp
    (comparablePrimePool_subset x M hM hp)

theorem prime_of_mem_comparablePrimePool
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {p : ℕ} (hp : p ∈ comparablePrimePool x M hM) : p.Prime :=
  (prime_and_bounds_of_mem_comparablePrimePool hp).1

theorem bounds_of_mem_comparablePrimePool
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {p : ℕ} (hp : p ∈ comparablePrimePool x M hM) :
    ⌊x⌋₊ + 1 ≤ p ∧ p ≤ ⌊2 * x⌋₊ := by
  obtain ⟨-, hlo, hhi⟩ := prime_and_bounds_of_mem_comparablePrimePool hp
  exact ⟨Nat.succ_le_iff.mpr hlo, hhi⟩

/-- Uniform lower and upper product bounds for every subset of the pool. -/
theorem comparable_primeProduct_bounds
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {s : Finset ℕ} (hs : s ⊆ comparablePrimePool x M hM) :
    (⌊x⌋₊ + 1) ^ s.card ≤ primeProduct s ∧
      primeProduct s ≤ ⌊2 * x⌋₊ ^ s.card := by
  constructor
  · simpa [primeProduct, Finset.prod_const] using
      (Finset.prod_le_prod (s := s)
        (fun _ _ ↦ Nat.zero_le (⌊x⌋₊ + 1))
        (fun p hp ↦ (bounds_of_mem_comparablePrimePool (hs hp)).1))
  · exact Finset.prod_le_pow_card s id ⌊2 * x⌋₊ fun p hp ↦
      (bounds_of_mem_comparablePrimePool (hs hp)).2

theorem comparable_primeProduct_squarefree
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {s : Finset ℕ} (hs : s ⊆ comparablePrimePool x M hM) :
    Squarefree (primeProduct s) :=
  primeProduct_squarefree fun _ hp ↦ prime_of_mem_comparablePrimePool (hs hp)

/-- On fixed-cardinality subsets of the selected prime pool, the product map
is injective (in fact the cardinality assumption is not needed). -/
theorem comparable_primeProduct_injective
    {x : ℝ} {M k : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {s t : Finset ℕ}
    (hs : s ∈ (comparablePrimePool x M hM).powersetCard k)
    (ht : t ∈ (comparablePrimePool x M hM).powersetCard k)
    (heq : primeProduct s = primeProduct t) : s = t := by
  exact primeProduct_injective_on_prime_sets
    (fun p hp ↦ prime_of_mem_comparablePrimePool
      ((Finset.mem_powersetCard.mp hs).1 hp))
    (fun p hp ↦ prime_of_mem_comparablePrimePool
      ((Finset.mem_powersetCard.mp ht).1 hp)) heq

theorem card_comparable_modulusReservoir
    {x : ℝ} {M : ℕ} (hM : M ≤ (comparablePrimeCandidates x).card)
    (k : ℕ) :
    (modulusReservoir (comparablePrimePool x M hM) k).card =
      Nat.choose M k := by
  rw [card_modulusReservoir_of_primes
    (fun p hp ↦ prime_of_mem_comparablePrimePool hp),
    card_comparablePrimePool]

/-- Exact product bounds for a `k`-element subset. -/
theorem comparable_fixedCard_primeProduct_bounds
    {x : ℝ} {M k : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {s : Finset ℕ} (hs : s ⊆ comparablePrimePool x M hM)
    (hcard : s.card = k) :
    (⌊x⌋₊ + 1) ^ k ≤ primeProduct s ∧
      primeProduct s ≤ ⌊2 * x⌋₊ ^ k := by
  simpa [hcard] using comparable_primeProduct_bounds hs

/-- If two `k`-subsets differ by one exchange, their least common multiple
is the product over their `k+1`-element union and obeys the corresponding
comparable-prime bounds. -/
theorem comparable_oneExchange_lcm_bounds
    {x : ℝ} {M k : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {s t : Finset ℕ} (hs : s ⊆ comparablePrimePool x M hM)
    (ht : t ⊆ comparablePrimePool x M hM) (hcard : s.card = k)
    (hex : OneExchange s t) :
    (⌊x⌋₊ + 1) ^ k ≤ Nat.lcm (primeProduct s) (primeProduct t) ∧
      Nat.lcm (primeProduct s) (primeProduct t) ≤ ⌊2 * x⌋₊ ^ (k + 1) := by
  have huPrime : ∀ p ∈ comparablePrimePool x M hM, p.Prime :=
    fun p hp ↦ prime_of_mem_comparablePrimePool hp
  have hsPrime : ∀ p ∈ s, p.Prime := fun p hp ↦ huPrime p (hs hp)
  have htPrime : ∀ p ∈ t, p.Prime := fun p hp ↦ huPrime p (ht hp)
  have hprodPos : 0 < primeProduct t :=
    Nat.pos_of_ne_zero (primeProduct_ne_zero htPrime)
  constructor
  · have hlower := (comparable_fixedCard_primeProduct_bounds hs hcard).1
    exact hlower.trans (Nat.le_of_dvd
      (Nat.lcm_pos (Nat.pos_of_ne_zero (primeProduct_ne_zero hsPrime)) hprodPos)
      (Nat.dvd_lcm_left _ _))
  · rw [lcm_primeProducts huPrime hs ht]
    have hbound := (comparable_primeProduct_bounds (Finset.union_subset hs ht)).2
    simpa [card_union_eq_succ_of_oneExchange hex, hcard] using hbound

/-- After deleting an arbitrary finite bad set, the surviving pool still has
at least `M - bad.card` elements. -/
theorem card_allowed_comparablePrimePool_ge
    {x : ℝ} {M : ℕ} (hM : M ≤ (comparablePrimeCandidates x).card)
    (bad : Finset ℕ) :
    M - bad.card ≤ (comparablePrimePool x M hM \ bad).card := by
  have hdecomp := Finset.card_sdiff_add_card_inter
    (comparablePrimePool x M hM) bad
  have hinter : (comparablePrimePool x M hM ∩ bad).card ≤ bad.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [card_comparablePrimePool x M hM] at hdecomp
  omega

theorem exists_comparable_fixedCard_subset_after_deletion
    {x : ℝ} {M k : ℕ} (hM : M ≤ (comparablePrimeCandidates x).card)
    (bad : Finset ℕ) (hroom : bad.card + k ≤ M) :
    ∃ s ⊆ comparablePrimePool x M hM \ bad, s.card = k := by
  apply Finset.exists_subset_card_eq
  have hlower := card_allowed_comparablePrimePool_ge hM bad
  omega

theorem comparable_oneExchange_connected_after_deletion
    {x : ℝ} {M k : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    (bad : Finset ℕ) {s t : Finset ℕ}
    (hs : s ⊆ comparablePrimePool x M hM \ bad)
    (ht : t ⊆ comparablePrimePool x M hM \ bad)
    (hscard : s.card = k) (htcard : t.card = k) :
    Relation.ReflTransGen OneExchange s t :=
  oneExchange_connected hs ht (hscard.trans htcard.symm)

/-- Nonemptiness, squarefreeness, and exchange-connectivity of the surviving
fixed-cardinality reservoir. -/
theorem surviving_comparable_reservoir
    {x : ℝ} {M k : ℕ} (hM : M ≤ (comparablePrimeCandidates x).card)
    (bad : Finset ℕ) (hroom : bad.card + k ≤ M) :
    (∃ q ∈ modulusReservoir (comparablePrimePool x M hM \ bad) k,
      Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ comparablePrimePool x M hM \ bad →
        t ⊆ comparablePrimePool x M hM \ bad →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  obtain ⟨s, hs, hcard⟩ :=
    exists_comparable_fixedCard_subset_after_deletion hM bad hroom
  refine ⟨⟨primeProduct s, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hs, hcard⟩, rfl⟩
  · exact primeProduct_squarefree fun p hp ↦
      prime_of_mem_comparablePrimePool (Finset.mem_sdiff.mp (hs hp)).1
  · intro s' t' hs' ht' hscard htcard
    exact comparable_oneExchange_connected_after_deletion bad
      hs' ht' hscard htcard

/-- The selected comparable-interval primes dividing a nonzero integer
certificate. -/
def comparableIntegerBadPrimes (x : ℝ) (M : ℕ)
    (hM : M ≤ (comparablePrimeCandidates x).card) (D : ℤ) : Finset ℕ :=
  (comparablePrimePool x M hM).filter fun p ↦ (p : ℤ) ∣ D

theorem mem_comparableIntegerBadPrimes_iff
    {x : ℝ} {M : ℕ} {hM : M ≤ (comparablePrimeCandidates x).card}
    {D : ℤ} {p : ℕ} :
    p ∈ comparableIntegerBadPrimes x M hM D ↔
      p ∈ comparablePrimePool x M hM ∧ (p : ℤ) ∣ D := by
  simp [comparableIntegerBadPrimes]

/-- A nonzero certificate smaller than `(floor x + 1)^b` is divisible by
fewer than `b` selected comparable primes.  The assumption on the lower
endpoint is written explicitly. -/
theorem card_comparableIntegerBadPrimes_lt
    {x : ℝ} {M b : ℕ} (hM : M ≤ (comparablePrimeCandidates x).card)
    (hlower : 1 < ⌊x⌋₊ + 1) {D : ℤ} (hD : D ≠ 0)
    (hsize : D.natAbs < (⌊x⌋₊ + 1) ^ b) :
    (comparableIntegerBadPrimes x M hM D).card < b := by
  let bad := comparableIntegerBadPrimes x M hM D
  have hbad : bad ⊆ comparablePrimePool x M hM := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hdiv : ∀ p ∈ bad, p ∣ D.natAbs := by
    intro p hp
    exact Int.natCast_dvd.mp (Finset.mem_filter.mp hp).2
  have hprodD : primeProduct bad ∣ D.natAbs :=
    primeProduct_dvd_of_each_dvd
      (fun p hp ↦ prime_of_mem_comparablePrimePool hp) hbad hdiv
  have hprod_le : primeProduct bad ≤ D.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hprodD
  have hlowerProd : (⌊x⌋₊ + 1) ^ bad.card ≤ primeProduct bad :=
    (comparable_primeProduct_bounds hbad).1
  exact (Nat.pow_lt_pow_iff_right hlower).mp
    (hlowerProd.trans_lt (hprod_le.trans_lt hsize))

/-- The selected comparable primes dividing at least one of two integer
certificates. -/
def comparableIntegerBadPrimesTwo (x : ℝ) (M : ℕ)
    (hM : M ≤ (comparablePrimeCandidates x).card) (D₁ D₂ : ℤ) : Finset ℕ :=
  comparableIntegerBadPrimes x M hM D₁ ∪
    comparableIntegerBadPrimes x M hM D₂

theorem card_comparableIntegerBadPrimesTwo_lt
    {x : ℝ} {M b₁ b₂ : ℕ}
    (hM : M ≤ (comparablePrimeCandidates x).card)
    (hlower : 1 < ⌊x⌋₊ + 1)
    {D₁ D₂ : ℤ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hsize₁ : D₁.natAbs < (⌊x⌋₊ + 1) ^ b₁)
    (hsize₂ : D₂.natAbs < (⌊x⌋₊ + 1) ^ b₂) :
    (comparableIntegerBadPrimesTwo x M hM D₁ D₂).card < b₁ + b₂ := by
  have h₁ := card_comparableIntegerBadPrimes_lt hM hlower hD₁ hsize₁
  have h₂ := card_comparableIntegerBadPrimes_lt hM hlower hD₂ hsize₂
  have hu := Finset.card_union_le
    (comparableIntegerBadPrimes x M hM D₁)
    (comparableIntegerBadPrimes x M hM D₂)
  simpa only [comparableIntegerBadPrimesTwo] using
    hu.trans_lt (Nat.add_lt_add h₁ h₂)

/-- One explicit certificate deletes fewer than `b` primes, so the surviving
`k`-subset reservoir is nonempty and exchange-connected when `b+k ≤ M`. -/
theorem surviving_comparable_reservoir_oneInteger
    {x : ℝ} {M b k : ℕ}
    (hM : M ≤ (comparablePrimeCandidates x).card)
    (hlower : 1 < ⌊x⌋₊ + 1)
    {D : ℤ} (hD : D ≠ 0)
    (hsize : D.natAbs < (⌊x⌋₊ + 1) ^ b)
    (hroom : b + k ≤ M) :
    (∃ q ∈ modulusReservoir
        (comparablePrimePool x M hM \
          comparableIntegerBadPrimes x M hM D) k,
      Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ comparablePrimePool x M hM \
          comparableIntegerBadPrimes x M hM D →
        t ⊆ comparablePrimePool x M hM \
          comparableIntegerBadPrimes x M hM D →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  have hbad := card_comparableIntegerBadPrimes_lt hM hlower hD hsize
  have hroom' :
      (comparableIntegerBadPrimes x M hM D).card + k ≤ M := by omega
  exact surviving_comparable_reservoir hM
    (comparableIntegerBadPrimes x M hM D) hroom'

/-- Two explicit certificates delete fewer than `b₁+b₂` primes, with the
same nonemptiness and exchange-connectivity conclusion. -/
theorem surviving_comparable_reservoir_twoIntegers
    {x : ℝ} {M b₁ b₂ k : ℕ}
    (hM : M ≤ (comparablePrimeCandidates x).card)
    (hlower : 1 < ⌊x⌋₊ + 1)
    {D₁ D₂ : ℤ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hsize₁ : D₁.natAbs < (⌊x⌋₊ + 1) ^ b₁)
    (hsize₂ : D₂.natAbs < (⌊x⌋₊ + 1) ^ b₂)
    (hroom : b₁ + b₂ + k ≤ M) :
    (∃ q ∈ modulusReservoir
        (comparablePrimePool x M hM \
          comparableIntegerBadPrimesTwo x M hM D₁ D₂) k,
      Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ comparablePrimePool x M hM \
          comparableIntegerBadPrimesTwo x M hM D₁ D₂ →
        t ⊆ comparablePrimePool x M hM \
          comparableIntegerBadPrimesTwo x M hM D₁ D₂ →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  have hbad := card_comparableIntegerBadPrimesTwo_lt
    hM hlower hD₁ hD₂ hsize₁ hsize₂
  have hroom' :
      (comparableIntegerBadPrimesTwo x M hM D₁ D₂).card + k ≤ M := by omega
  exact surviving_comparable_reservoir hM
    (comparableIntegerBadPrimesTwo x M hM D₁ D₂) hroom'

end

end TranslatedDepthSeven
