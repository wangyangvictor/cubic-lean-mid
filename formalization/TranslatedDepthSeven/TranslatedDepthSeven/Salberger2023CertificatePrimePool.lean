import TranslatedDepthSeven.ComparablePrimePoolBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A uniform prime pool for logarithmic-height curve certificates

For fixed `A ≥ 0`, `β > 0`, and `k`, a single pool of `O((1 + log V)^k)` primes
in `(4 V^β, 8 V^β]` detects every nonzero integer of size at most
`V^(A(1 + log V)^k)`.  The pool and its threshold do not depend on a curve
degree or on the individual integer.  Prime supply is the already proved
dyadic consequence of the prime number theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 800000

/-- The explicit number of comparable primes needed for a certificate
whose logarithmic height is bounded by `A (1 + log V)^k log V`. -/
def curveCertificatePrimeCount (A β V : ℝ) (k : ℕ) : ℕ :=
  ⌈((A + 1) / β) * (1 + Real.log V) ^ k⌉₊

theorem curveCertificate_lt_comparableBase_pow
    {A β V : ℝ} (k : ℕ) (hA : 0 ≤ A) (hβ : 0 < β) (hV : 1 < V)
    {D : ℕ} (hD : (D : ℝ) ≤ V ^ (A * (1 + Real.log V) ^ k)) :
    D < (⌊4 * V ^ β⌋₊ + 1) ^ curveCertificatePrimeCount A β V k := by
  let base : ℕ := ⌊4 * V ^ β⌋₊ + 1
  let M := curveCertificatePrimeCount A β V k
  have hVpos : 0 < V := zero_lt_one.trans hV
  have hlog : 0 < Real.log V := Real.log_pos hV
  have hpow : 0 < V ^ β := Real.rpow_pos_of_pos hVpos _
  have hbase : V ^ β ≤ (base : ℝ) := by
    have hf := Nat.lt_floor_add_one (4 * V ^ β)
    dsimp only [base]
    push_cast
    push_cast at hf
    linarith
  have hlogbase : β * Real.log V ≤ Real.log (base : ℝ) := by
    have h := Real.log_le_log hpow hbase
    rwa [Real.log_rpow hVpos] at h
  have hM : ((A + 1) / β) * (1 + Real.log V) ^ k ≤ (M : ℝ) :=
    Nat.le_ceil _
  have hlogbound : (A + 1) * (1 + Real.log V) ^ k * Real.log V ≤
      (M : ℝ) * Real.log (base : ℝ) := by
    calc
      (A + 1) * (1 + Real.log V) ^ k * Real.log V =
          (((A + 1) / β) * (1 + Real.log V) ^ k) * (β * Real.log V) := by
        field_simp
      _ ≤ (M : ℝ) * (β * Real.log V) :=
        mul_le_mul_of_nonneg_right hM (mul_nonneg hβ.le hlog.le)
      _ ≤ (M : ℝ) * Real.log (base : ℝ) :=
        mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg _)
  have hstrict : Real.log (V ^ (A * (1 + Real.log V) ^ k)) <
      (M : ℝ) * Real.log (base : ℝ) := by
    rw [Real.log_rpow hVpos]
    have hg : 0 < (1 + Real.log V) ^ k * Real.log V := by positivity
    nlinarith
  have hreal := hD.trans_lt
    (Real.lt_pow_of_log_lt (by positivity : (0 : ℝ) < base) hstrict)
  exact_mod_cast hreal

/-- There are enough primes in the one dyadic interval, uniformly in every
integer certificate.  The demand is a fixed power of `1 + log V`. -/
theorem eventually_curveCertificatePrimeCount_le_candidateCard
    {A β : ℝ} (k : ℕ) (hA : 0 ≤ A) (hβ : 0 < β) :
    ∀ᶠ V : ℝ in atTop,
      curveCertificatePrimeCount A β V k ≤
        (comparablePrimeCandidates (4 * V ^ β)).card := by
  let C : ℝ := (A + 1) / β
  let L : ℝ := C * 2 ^ k + 1
  let B : ℝ := Real.log 4 + β
  have hC : 0 < C := by dsimp [C]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hB : 0 < B := by
    dsimp [B]
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ) hβ).bound
    (show 0 < (L * B)⁻¹ by positivity)
  have hscale : Tendsto (fun V : ℝ ↦ 4 * V ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).const_mul_atTop (by norm_num)
  have hsupply := hscale.eventually
    eventually_ceil_quarter_x_div_log_le_dyadicPrimeCount
  filter_upwards [hsmall, hsupply, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with V hsmall hsupply hV hlog
  have hVpos : 0 < V := zero_lt_one.trans hV
  have hpow : 0 < V ^ β := Real.rpow_pos_of_pos hVpos _
  have hlognonneg : 0 ≤ Real.log V := by linarith
  have hsmall' : (Real.log V) ^ (k + 1) ≤ (L * B)⁻¹ * V ^ β := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlognonneg (k + 1)),
      abs_of_pos hpow] using hsmall
  have hbudget : L * B * (Real.log V) ^ (k + 1) ≤ V ^ β := by
    have h := mul_le_mul_of_nonneg_left hsmall' (mul_pos hL hB).le
    calc
      L * B * (Real.log V) ^ (k + 1) ≤
          (L * B) * ((L * B)⁻¹ * V ^ β) := h
      _ = V ^ β := by field_simp
  have hM : (curveCertificatePrimeCount A β V k : ℝ) ≤ L * (Real.log V) ^ k := by
    have hc := Nat.ceil_lt_add_one
      (show 0 ≤ C * (1 + Real.log V) ^ k by positivity)
    have hsum : (1 + Real.log V) ^ k ≤ 2 ^ k * (Real.log V) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have hone : 1 ≤ (Real.log V) ^ k := one_le_pow₀ hlog
    have hmul := mul_le_mul_of_nonneg_left hsum hC.le
    change (⌈C * (1 + Real.log V) ^ k⌉₊ : ℝ) ≤ L * (Real.log V) ^ k
    dsimp only [L]
    nlinarith
  have hlogx : Real.log (4 * V ^ β) = Real.log 4 + β * Real.log V := by
    rw [Real.log_mul (by norm_num) hpow.ne', Real.log_rpow hVpos]
  have hlogxpos : 0 < Real.log (4 * V ^ β) := by
    rw [hlogx]
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hlogxbound : Real.log (4 * V ^ β) ≤ B * Real.log V := by
    rw [hlogx]
    dsimp only [B]
    have : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith
  have hroom : (curveCertificatePrimeCount A β V k : ℝ) ≤
      (1 / 4 : ℝ) * ((4 * V ^ β) / Real.log (4 * V ^ β)) := by
    rw [show (1 / 4 : ℝ) * ((4 * V ^ β) / Real.log (4 * V ^ β)) =
        V ^ β / Real.log (4 * V ^ β) by ring]
    apply (le_div_iff₀ hlogxpos).mpr
    calc
      (curveCertificatePrimeCount A β V k : ℝ) * Real.log (4 * V ^ β) ≤
          (L * (Real.log V) ^ k) * (B * Real.log V) :=
        mul_le_mul hM hlogxbound hlogxpos.le (by positivity)
      _ = L * B * (Real.log V) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ V ^ β := hbudget
  have hceil : curveCertificatePrimeCount A β V k ≤
      ⌈(1 / 4 : ℝ) * ((4 * V ^ β) / Real.log (4 * V ^ β))⌉₊ := by
    exact_mod_cast hroom.trans (Nat.le_ceil _)
  rw [comparablePrimeCandidates_eq_dyadicPrimes, card_dyadicPrimes]
  exact hceil.trans hsupply

/-- One fixed finite set of primes detects every bounded nonzero
certificate.  Its constant and eventual threshold depend only on `A, β`.
This is the uniform prime-cover supply needed when curve degrees vary. -/
theorem eventually_exists_curveCertificatePrimePool
    {A β : ℝ} (k : ℕ) (hA : 0 ≤ A) (hβ : 0 < β) :
    ∀ᶠ V : ℝ in atTop,
      ∃ P : Finset ℕ,
        (P.card : ℝ) ≤ ((A + 1) / β + 1) * (1 + Real.log V) ^ k ∧
        (∀ p ∈ P, p.Prime ∧ 4 * V ^ β < (p : ℝ) ∧
          (p : ℝ) ≤ 8 * V ^ β) ∧
        (∀ D : ℤ, D ≠ 0 → (D.natAbs : ℝ) ≤ V ^ (A * (1 + Real.log V) ^ k) →
          ∃ p ∈ P, ¬ (p : ℤ) ∣ D) := by
  filter_upwards [eventually_curveCertificatePrimeCount_le_candidateCard k hA hβ,
    eventually_gt_atTop (1 : ℝ)] with V hsupply hV
  let M := curveCertificatePrimeCount A β V k
  let P := comparablePrimePool (4 * V ^ β) M hsupply
  have hcard : P.card = M := card_comparablePrimePool _ _ _
  have hlog : 0 < Real.log V := Real.log_pos hV
  have hC : 0 < (A + 1) / β := by positivity
  have hbase : 1 < ⌊4 * V ^ β⌋₊ + 1 := by
    have hpow : 1 ≤ V ^ β := Real.one_le_rpow hV.le hβ.le
    have hf := Nat.lt_floor_add_one (4 * V ^ β)
    have : (1 : ℝ) < ((⌊4 * V ^ β⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      push_cast at hf
      linarith
    exact_mod_cast this
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hcard]
    have hc := Nat.ceil_lt_add_one
      (show 0 ≤ ((A + 1) / β) * (1 + Real.log V) ^ k by positivity)
    have hone : 1 ≤ (1 + Real.log V) ^ k := one_le_pow₀ (by linarith)
    change (⌈((A + 1) / β) * (1 + Real.log V) ^ k⌉₊ : ℝ) ≤ _
    nlinarith
  · intro p hp
    obtain ⟨hpPrime, hpLow, hpHigh⟩ :=
      prime_and_bounds_of_mem_comparablePrimePool hp
    refine ⟨hpPrime, (Nat.floor_lt (by positivity)).mp hpLow, ?_⟩
    have hf : ((⌊2 * (4 * V ^ β)⌋₊ : ℕ) : ℝ) ≤ 2 * (4 * V ^ β) :=
      Nat.floor_le (by positivity)
    have hpHigh' : (p : ℝ) ≤ ⌊2 * (4 * V ^ β)⌋₊ := by exact_mod_cast hpHigh
    linarith
  · intro D hD hsize
    have hsmall := curveCertificate_lt_comparableBase_pow k hA hβ hV hsize
    have hbad := card_comparableIntegerBadPrimes_lt hsupply hbase hD hsmall
    by_contra! h
    have hfull : comparableIntegerBadPrimes (4 * V ^ β) M hsupply D = P := by
      ext p
      simp only [mem_comparableIntegerBadPrimes_iff]
      exact ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, h p hp⟩⟩
    rw [hfull, hcard] at hbad
    exact (Nat.lt_irrefl M) hbad

end

end TranslatedDepthSeven
