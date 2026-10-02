import PrimeNumberTheoremAnd.Consequences

/-!
# Comparable prime reservoirs

This file extracts from the prime number theorem a concrete fact used to build
finite reservoirs: the number of primes in a dyadic interval tends to infinity.
No asymptotic estimate is retained as an additional hypothesis.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

/-- The (real-valued) difference of the prime-counting function at the two
ends of a dyadic interval tends to infinity. -/
theorem dyadicPrimeCountingDiff_tendsto :
    Tendsto
      (fun x : ℝ =>
        (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) -
          (Nat.primeCounting ⌊x⌋₊ : ℝ))
      atTop atTop := by
  convert tendsto_by_squeeze (1 : ℝ) zero_lt_one using 1 <;> norm_num

/-- A quantitative form of the dyadic reservoir.  The deliberately
non-optimal constant `1/4` is convenient and more than sufficient for the
fixed-cardinality applications. -/
theorem eventually_quarter_x_div_log_le_dyadicPrimeCountingDiff :
    ∀ᶠ x : ℝ in atTop,
      (1 / 4 : ℝ) * (x / Real.log x) ≤
        (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) -
          (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  simp only [div_one] at hc
  have hfirst := smaller_terms (ε := (1 : ℝ)) zero_lt_one c hc
    (1 / 16 : ℝ) (by norm_num)
  have hsecond := second_smaller_terms c hc (1 / 16 : ℝ) (by norm_num)
  have hlog : ∀ᶠ x : ℝ in atTop, 4 * Real.log 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 * Real.log 2))
  filter_upwards [hfirst, hsecond, hlog,
    eventually_ge_atTop (2 : ℝ)] with x hx1 hx2 hxlog hx
  rw [show (1 + (1 : ℝ)) * x = 2 * x by ring] at hx1
  have hp2 := hpi (2 * x)
  have hpx := hpi x
  rw [show (1 + c (2 * x)) * (2 * x / Real.log (2 * x)) =
      (1 + c (2 * x)) * (2 * x) / Real.log (2 * x) by ring,
    ← hp2] at hx1
  rw [show (1 + c x) * (x / Real.log x) =
      (1 + c x) * x / Real.log x by ring, ← hpx] at hx2
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log (2 * x) := Real.log_pos (by nlinarith)
  have hsplit : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  have hlogCompare : Real.log (2 * x) ≤ (5 / 4 : ℝ) * Real.log x := by
    rw [hsplit]
    linarith
  have hquot : (8 / 5 : ℝ) * (x / Real.log x) ≤ 2 * x / Real.log (2 * x) := by
    apply (le_div_iff₀ hlog2).2
    calc
      (8 / 5 : ℝ) * (x / Real.log x) * Real.log (2 * x) ≤
          (8 / 5 : ℝ) * (x / Real.log x) * ((5 / 4 : ℝ) * Real.log x) :=
        mul_le_mul_of_nonneg_left hlogCompare (by positivity)
      _ = 2 * x := by field_simp; ring
  norm_num at hx1 hx2 ⊢
  linarith

/-- The number of primes in the integer interval
`(⌊x⌋₊, ⌊2x⌋₊]`. -/
noncomputable def dyadicPrimeCount (x : ℝ) : ℕ :=
  Nat.primeCounting ⌊2 * x⌋₊ - Nat.primeCounting ⌊x⌋₊

/-- The concrete finite set counted by `dyadicPrimeCount`. -/
noncomputable def dyadicPrimes (x : ℝ) : Finset ℕ :=
  (⌊2 * x⌋₊ + 1).primesBelow \ (⌊x⌋₊ + 1).primesBelow

theorem mem_dyadicPrimes {x : ℝ} {p : ℕ} :
    p ∈ dyadicPrimes x ↔
      p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊2 * x⌋₊ := by
  simp only [dyadicPrimes, Finset.mem_sdiff, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpUpper, hpPrime⟩, hpLower⟩
    refine ⟨hpPrime, ?_, by omega⟩
    by_contra h
    apply hpLower
    exact ⟨by omega, hpPrime⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨⟨by omega, hpPrime⟩, ?_⟩
    rintro ⟨h, -⟩
    omega

theorem card_dyadicPrimes (x : ℝ) :
    (dyadicPrimes x).card = dyadicPrimeCount x := by
  by_cases hx : ⌊x⌋₊ ≤ ⌊2 * x⌋₊
  · have hsub : (⌊x⌋₊ + 1).primesBelow ⊆
        (⌊2 * x⌋₊ + 1).primesBelow := by
      intro p hp
      rw [Nat.mem_primesBelow] at hp ⊢
      exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hx), hp.2⟩
    rw [dyadicPrimes, Finset.card_sdiff_of_subset hsub,
      Nat.primesBelow_card_eq_primeCounting',
      Nat.primesBelow_card_eq_primeCounting']
    rfl
  · have hrev : ⌊2 * x⌋₊ < ⌊x⌋₊ := Nat.lt_of_not_ge hx
    have hempty : dyadicPrimes x = ∅ := by
      ext p
      simp only [mem_dyadicPrimes, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.card_empty, dyadicPrimeCount, Nat.sub_eq_zero_of_le]
    exact Nat.monotone_primeCounting (Nat.le_of_lt hrev)

theorem eventually_floor_le_floor_two :
    ∀ᶠ x : ℝ in atTop, ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact Nat.floor_mono (by linarith)

/-- Natural-valued quantitative form of the reservoir estimate. -/
theorem eventually_ceil_quarter_x_div_log_le_dyadicPrimeCount :
    ∀ᶠ x : ℝ in atTop,
      ⌈(1 / 4 : ℝ) * (x / Real.log x)⌉₊ ≤ dyadicPrimeCount x := by
  filter_upwards [eventually_quarter_x_div_log_le_dyadicPrimeCountingDiff,
    eventually_floor_le_floor_two] with x hx hfloor
  apply Nat.ceil_le.mpr
  rw [dyadicPrimeCount, Nat.cast_sub]
  · exact hx
  · exact Nat.monotone_primeCounting hfloor

/-- The natural-valued dyadic prime count tends to infinity. -/
theorem dyadicPrimeCount_tendsto :
    Tendsto dyadicPrimeCount atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  apply dyadicPrimeCountingDiff_tendsto.congr'
  filter_upwards [eventually_floor_le_floor_two] with x hx
  rw [dyadicPrimeCount, Nat.cast_sub]
  exact Nat.monotone_primeCounting hx

/-- For every prescribed cardinality, every sufficiently large dyadic
interval contains at least that many primes. -/
theorem eventually_many_primes_in_dyadic_interval (N : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      N ≤ Nat.primeCounting ⌊2 * x⌋₊ - Nat.primeCounting ⌊x⌋₊ := by
  exact dyadicPrimeCount_tendsto.eventually (eventually_ge_atTop N)

/-- A direct finite-set form: for every `N`, sufficiently large dyadic
intervals contain a set of at least `N` distinct primes. -/
theorem eventually_large_dyadicPrime_finset (N : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      N ≤ (dyadicPrimes x).card ∧
        ∀ p ∈ dyadicPrimes x,
          p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊2 * x⌋₊ := by
  filter_upwards [eventually_many_primes_in_dyadic_interval N] with x hx
  exact ⟨by simpa [card_dyadicPrimes] using hx,
    fun p hp ↦ mem_dyadicPrimes.mp hp⟩

end TranslatedDepthSeven
