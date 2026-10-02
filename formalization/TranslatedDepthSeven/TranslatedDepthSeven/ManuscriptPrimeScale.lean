import TranslatedDepthSeven.ComparablePrimePoolBridge

/-!
# The comparable-prime reservoir at logarithmic manuscript scale

This file specializes the quantitative dyadic consequence of the prime
number theorem to the interval

`(floor (C * log H), floor (2 * C * log H)]`.

If `C >= 8 * M0`, that interval eventually contains at least

`ceil (M0 * log H / log (log H))`

primes.  The constant `8` is deliberately non-optimal.  The proof uses the
already established lower bound `(1 / 4) * x / log x` and the elementary
eventual comparison

`log (C * log H) <= 2 * log (log H)`.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- The elementary real-variable comparison behind the manuscript-scale
reservoir.  Its hypotheses are pointwise and contain no asymptotic or
number-theoretic assumption. -/
theorem manuscriptPrimeScale_ratio_le
    {C M0 H : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M0)
    (hroom : 8 * M0 ≤ C) (hH : 1 < H)
    (hloglog : 0 < Real.log (Real.log H))
    (hlogC : Real.log C ≤ Real.log (Real.log H)) :
    M0 * (Real.log H / Real.log (Real.log H)) ≤
      (1 / 4 : ℝ) *
        ((C * Real.log H) / Real.log (C * Real.log H)) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hlogCnonneg : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogmul :
      Real.log (C * Real.log H) =
        Real.log C + Real.log (Real.log H) := by
    rw [Real.log_mul hCpos.ne' hlogH.ne']
  have hdenpos : 0 < Real.log (C * Real.log H) := by
    rw [hlogmul]
    linarith
  have hdenle :
      Real.log (C * Real.log H) ≤
        2 * Real.log (Real.log H) := by
    rw [hlogmul]
    linarith
  have hfirst :
      M0 * Real.log (C * Real.log H) ≤
        M0 * (2 * Real.log (Real.log H)) :=
    mul_le_mul_of_nonneg_left hdenle hM0
  have hsecond :
      (8 * M0) * Real.log (Real.log H) ≤
        C * Real.log (Real.log H) :=
    mul_le_mul_of_nonneg_right hroom hloglog.le
  have hcross :
      M0 * Real.log (C * Real.log H) ≤
        ((1 / 4 : ℝ) * C) * Real.log (Real.log H) := by
    nlinarith
  rw [show M0 * (Real.log H / Real.log (Real.log H)) =
      (M0 * Real.log H) / Real.log (Real.log H) by ring,
    show (1 / 4 : ℝ) *
        ((C * Real.log H) / Real.log (C * Real.log H)) =
      (((1 / 4 : ℝ) * C) * Real.log H) /
        Real.log (C * Real.log H) by ring]
  apply (div_le_div_iff₀ hloglog hdenpos).2
  nlinarith

/-- The logarithmic scale used for the prime interval tends to infinity for
every fixed positive multiplier. -/
theorem tendsto_const_mul_log_atTop {C : ℝ} (hC : 0 < C) :
    Tendsto (fun H : ℝ ↦ C * Real.log H) atTop atTop :=
  Real.tendsto_log_atTop.const_mul_atTop hC

/-- Quantitative dyadic PNT at the manuscript scale.  The demand is allowed
to grow like `log H / log (log H)`; it is not a fixed-cardinality statement. -/
theorem eventually_manuscriptPrimeScale_le_dyadicPrimeCount
    {C M0 : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M0)
    (hroom : 8 * M0 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      ⌈M0 * (Real.log H / Real.log (Real.log H))⌉₊ ≤
        dyadicPrimeCount (C * Real.log H) := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hscale := tendsto_const_mul_log_atTop hCpos
  have hpnt := hscale.eventually
    eventually_ceil_quarter_x_div_log_le_dyadicPrimeCount
  have hloglogTop :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hpnt, eventually_gt_atTop (1 : ℝ),
    hloglogTop.eventually_gt_atTop (0 : ℝ),
    hloglogTop.eventually (eventually_ge_atTop (Real.log C))]
      with H hpntH hH hloglog hlogC
  exact (Nat.ceil_mono (manuscriptPrimeScale_ratio_le
    hC hM0 hroom hH hloglog hlogC)).trans hpntH

/-- The same conclusion stated as a cardinality lower bound for the concrete
finite set of primes in the interval. -/
theorem eventually_manuscriptPrimeScale_le_candidateCard
    {C M0 : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M0)
    (hroom : 8 * M0 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      ⌈M0 * (Real.log H / Real.log (Real.log H))⌉₊ ≤
        (comparablePrimeCandidates (C * Real.log H)).card := by
  filter_upwards [eventually_manuscriptPrimeScale_le_dyadicPrimeCount
    hC hM0 hroom] with H hH
  rw [comparablePrimeCandidates_eq_dyadicPrimes, card_dyadicPrimes]
  exact hH

/-- A concrete pool form of the scale bridge: for all sufficiently large
`H`, there is a finite set of exactly the demanded number of distinct primes,
and every one lies in the same dyadic interval. -/
theorem eventually_exists_manuscriptPrimePool
    {C M0 : ℝ} (hC : 1 ≤ C) (hM0 : 0 ≤ M0)
    (hroom : 8 * M0 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      ∃ P : Finset ℕ,
        P.card =
            ⌈M0 * (Real.log H / Real.log (Real.log H))⌉₊ ∧
          ∀ p ∈ P,
            p.Prime ∧
              ⌊C * Real.log H⌋₊ < p ∧
              p ≤ ⌊2 * (C * Real.log H)⌋₊ := by
  filter_upwards [eventually_manuscriptPrimeScale_le_candidateCard
    hC hM0 hroom] with H hcard
  obtain ⟨P, hPsubset, hPcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨P, hPcard, ?_⟩
  intro p hp
  exact mem_comparablePrimeCandidates_iff.mp (hPsubset hp)

end

end TranslatedDepthSeven
