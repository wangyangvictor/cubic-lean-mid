import TranslatedDepthSeven.ComparablePrimePool
import TranslatedDepthSeven.ReservoirSubpower

/-!
# Certificate deletion at the comparable-prime scale

Let the available primes lie in the single interval

`(floor (C * log H), floor (2 * C * log H)]`

and let the reservoir depth be

`ceil (B * log H / log (log H))`.

This file proves the elementary real-variable comparison needed to delete
the primes dividing a nonzero integer certificate of size at most `H ^ A`.
The sharp comparison used below is `A < B`; a separate corollary records the
deliberately non-optimal sufficient condition `4 * A + 4 <= B`.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- Pointwise form of the certificate-size comparison.  The two hypotheses
on `H` are precisely the eventual real-variable conditions used in its
proof. -/
theorem certificate_lt_comparableBase_pow_reservoirDepth
    {A B C H : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hC : 1 ≤ C)
    (hH : 1 < H) (hloglog : 0 < Real.log (Real.log H))
    {D : ℕ} (hD : (D : ℝ) ≤ H ^ A) :
    D < (⌊C * Real.log H⌋₊ + 1) ^ reservoirDepth B H := by
  have hHpos : 0 < H := zero_lt_one.trans hH
  have hlogHpos : 0 < Real.log H := Real.log_pos hH
  have hBpos : 0 < B := lt_of_le_of_lt hA hAB
  have hscaleLower : Real.log H ≤ C * Real.log H := by
    nlinarith
  have hscaleFloor :
      C * Real.log H < ((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using (Nat.lt_floor_add_one (C * Real.log H))
  have hbaseLower :
      Real.log H < ((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) :=
    hscaleLower.trans_lt hscaleFloor
  have hbasePos :
      0 < ((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) := by
    positivity
  have hlogBase :
      Real.log (Real.log H) ≤
        Real.log (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hlogHpos hbaseLower.le
  have hdepth :
      B * Real.log H / Real.log (Real.log H) ≤
        (reservoirDepth B H : ℝ) := by
    exact Nat.le_ceil _
  have hdepthLog :
      B * Real.log H ≤
        (reservoirDepth B H : ℝ) *
          Real.log (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ)) := by
    calc
      B * Real.log H =
          (B * Real.log H / Real.log (Real.log H)) *
            Real.log (Real.log H) := by field_simp
      _ ≤ (reservoirDepth B H : ℝ) * Real.log (Real.log H) := by
        exact mul_le_mul_of_nonneg_right hdepth hloglog.le
      _ ≤ (reservoirDepth B H : ℝ) *
          Real.log (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogBase (Nat.cast_nonneg _)
  have hlogStrict :
      Real.log (H ^ A) <
        (reservoirDepth B H : ℝ) *
          Real.log (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ)) := by
    rw [Real.log_rpow hHpos]
    exact (mul_lt_mul_of_pos_right hAB hlogHpos).trans_le hdepthLog
  have hpow :
      H ^ A < (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) ^
        reservoirDepth B H) := by
    exact Real.lt_pow_of_log_lt hbasePos hlogStrict
  have hcast :
      (D : ℝ) < (((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) ^
        reservoirDepth B H) := hD.trans_lt hpow
  exact_mod_cast hcast

/-- At the same pointwise scale, the lower endpoint of the prime interval is
strictly larger than one. -/
theorem one_lt_comparableBase
    {C H : ℝ} (hC : 1 ≤ C)
    (hH : 1 < H) (hloglog : 0 < Real.log (Real.log H)) :
    1 < ⌊C * Real.log H⌋₊ + 1 := by
  have hlogHpos : 0 < Real.log H := Real.log_pos hH
  have hlogHone : 1 < Real.log H :=
    (Real.log_pos_iff hlogHpos.le).mp hloglog
  have hscaleLower : Real.log H ≤ C * Real.log H := by
    nlinarith
  have hscaleFloor :
      C * Real.log H < ((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using (Nat.lt_floor_add_one (C * Real.log H))
  have hreal :
      (1 : ℝ) < ((⌊C * Real.log H⌋₊ + 1 : ℕ) : ℝ) :=
    hlogHone.trans (hscaleLower.trans_lt hscaleFloor)
  exact_mod_cast hreal

/-- Eventual form under the sharp coefficient hypothesis `A < B`. -/
theorem eventually_certificate_lt_comparableBase_pow_reservoirDepth_of_lt
    {A B C : ℝ} (hA : 0 ≤ A) (hAB : A < B) (hC : 1 ≤ C) :
    ∀ᶠ H : ℝ in atTop, ∀ D : ℕ,
      (D : ℝ) ≤ H ^ A →
        D < (⌊C * Real.log H⌋₊ + 1) ^ reservoirDepth B H := by
  have hloglogTop :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hloglogTop.eventually_gt_atTop (0 : ℝ)] with H hH hloglog
  intro D hD
  exact certificate_lt_comparableBase_pow_reservoirDepth
    hA hAB hC hH hloglog hD

/-- A deliberately non-optimal coefficient condition convenient for later
applications.  It implies the sharp inequality `A < B`. -/
theorem eventually_certificate_lt_comparableBase_pow_reservoirDepth
    {A B C : ℝ} (hA : 0 ≤ A) (hsafe : 4 * A + 4 ≤ B)
    (hC : 1 ≤ C) :
    ∀ᶠ H : ℝ in atTop, ∀ D : ℕ,
      (D : ℝ) ≤ H ^ A →
        D < (⌊C * Real.log H⌋₊ + 1) ^ reservoirDepth B H := by
  have hAB : A < B := by linarith
  exact eventually_certificate_lt_comparableBase_pow_reservoirDepth_of_lt
    hA hAB hC

/-- One nonzero certificate of size at most `H ^ A` deletes fewer than one
reservoir-depth's worth of selected comparable primes. -/
theorem eventually_card_comparableIntegerBadPrimes_lt_depth
    {A B C : ℝ} (hA : 0 ≤ A) (hsafe : 4 * A + 4 ≤ B)
    (hC : 1 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      ∀ (M : ℕ)
        (hM : M ≤ (comparablePrimeCandidates (C * Real.log H)).card)
        (D : ℤ),
        D ≠ 0 → (D.natAbs : ℝ) ≤ H ^ A →
          (comparableIntegerBadPrimes
            (C * Real.log H) M hM D).card < reservoirDepth B H := by
  have hAB : A < B := by linarith
  have hloglogTop :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hloglogTop.eventually_gt_atTop (0 : ℝ)] with H hH hloglog
  intro M hM D hD hsize
  apply card_comparableIntegerBadPrimes_lt hM
    (one_lt_comparableBase hC hH hloglog) hD
  exact certificate_lt_comparableBase_pow_reservoirDepth
    hA hAB hC hH hloglog hsize

/-- Two nonzero certificates, each of size at most `H ^ A`, delete fewer
than two reservoir-depth terms in total. -/
theorem eventually_card_comparableIntegerBadPrimesTwo_lt_two_depth
    {A B C : ℝ} (hA : 0 ≤ A) (hsafe : 4 * A + 4 ≤ B)
    (hC : 1 ≤ C) :
    ∀ᶠ H : ℝ in atTop,
      ∀ (M : ℕ)
        (hM : M ≤ (comparablePrimeCandidates (C * Real.log H)).card)
        (D₁ D₂ : ℤ),
        D₁ ≠ 0 → D₂ ≠ 0 →
        (D₁.natAbs : ℝ) ≤ H ^ A →
        (D₂.natAbs : ℝ) ≤ H ^ A →
          (comparableIntegerBadPrimesTwo
            (C * Real.log H) M hM D₁ D₂).card <
              reservoirDepth B H + reservoirDepth B H := by
  have hAB : A < B := by linarith
  have hloglogTop :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hloglogTop.eventually_gt_atTop (0 : ℝ)] with H hH hloglog
  intro M hM D₁ D₂ hD₁ hD₂ hsize₁ hsize₂
  apply card_comparableIntegerBadPrimesTwo_lt hM
    (one_lt_comparableBase hC hH hloglog) hD₁ hD₂
  · exact certificate_lt_comparableBase_pow_reservoirDepth
      hA hAB hC hH hloglog hsize₁
  · exact certificate_lt_comparableBase_pow_reservoirDepth
      hA hAB hC hH hloglog hsize₂

end

end TranslatedDepthSeven
