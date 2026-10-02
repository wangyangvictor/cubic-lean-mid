import TranslatedDepthSeven.PrimeWeightedLogFactorial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-! Elementary removal of higher prime powers from the weighted von
Mangoldt estimate. All sums use actual primes; no prime number theorem or
additional literature proposition is supplied. -/

namespace TranslatedDepthSeven.PrimeWeightedMertens
noncomputable section
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

private def tailSeries : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

private theorem tailSeries_nonneg : 0 ≤ tailSeries := by
  apply tsum_nonneg
  intro n
  positivity

private theorem tailSeries_summable :
    Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

private theorem log_div_sq_le (p : ℕ) (hp : 0 < p) :
    Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : Real.log (p : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div hpR.le (by norm_num : (0 : ℝ) < 1 / 2)
    nlinarith
  calc
    _ ≤ (2 * (p : ℝ) ^ (1 / 2 : ℝ)) / (p : ℝ) ^ 2 := by
      gcongr
    _ = 2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      rw [mul_div_assoc, ← Real.rpow_natCast (p : ℝ) 2,
        ← Real.rpow_sub hpR]
      norm_num only [Nat.cast_ofNat]
      rw [Real.rpow_neg hpR.le]

/-- A summable majorant for each genuine higher-prime-power term. -/
theorem log_div_pow_le (p k : ℕ) (hp : 2 ≤ p) (hk : 2 ≤ k) :
    Real.log (p : ℝ) / (p : ℝ) ^ k ≤
      (2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) * (1 / 2 : ℝ) ^ (k - 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hpow : (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ (k - 2) := by gcongr
  have heq : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  calc
    _ = (Real.log (p : ℝ) / (p : ℝ) ^ 2) / (p : ℝ) ^ (k - 2) := by
      rw [heq, div_div]
    _ ≤ (2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) / (2 : ℝ) ^ (k - 2) := by
      apply div_le_div₀
      · positivity
      · exact log_div_sq_le p (by omega)
      · positivity
      · exact hpow
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow]; norm_num

private theorem geometric_tail_sum_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2)) ≤ 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa using sum_geometric_two_le (K + 1 - 2)

/-- Uniform bound for any finite collection of bases at least two and any
finite collection of higher exponents. -/
theorem sum_higher_power_log_le (K : ℕ) (bases : ℕ → Finset ℕ)
    (hbases : ∀ k ∈ Finset.Icc 2 K, ∀ p ∈ bases k, 2 ≤ p) :
    (∑ k ∈ Finset.Icc 2 K, ∑ p ∈ bases k,
      Real.log (p : ℝ) / (p : ℝ) ^ k) ≤ 4 * tailSeries := by
  have hlocal (k : ℕ) (hk : k ∈ Finset.Icc 2 K) :
      (∑ p ∈ bases k, Real.log (p : ℝ) / (p : ℝ) ^ k) ≤
        (2 * tailSeries) * (1 / 2 : ℝ) ^ (k - 2) := by
    calc
      _ ≤ ∑ p ∈ bases k,
          (2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) * (1 / 2 : ℝ) ^ (k - 2) := by
        apply Finset.sum_le_sum
        intro p hp
        exact log_div_pow_le p k (hbases k hk p hp) (Finset.mem_Icc.mp hk).1
      _ = (2 * (∑ p ∈ bases k, ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹)) *
          (1 / 2 : ℝ) ^ (k - 2) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := by
        gcongr
        exact tailSeries_summable.sum_le_tsum (bases k) (fun n _hn => by positivity)
  calc
    _ ≤ ∑ k ∈ Finset.Icc 2 K, (2 * tailSeries) * (1 / 2 : ℝ) ^ (k - 2) :=
      Finset.sum_le_sum hlocal
    _ = (2 * tailSeries) * (∑ k ∈ Finset.Icc 2 K, (1 / 2 : ℝ) ^ (k - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * tailSeries) * 2 :=
      mul_le_mul_of_nonneg_left (geometric_tail_sum_le K)
        (mul_nonneg (by norm_num) tailSeries_nonneg)
    _ = _ := by ring

private theorem Ioc_zero_eq_Icc_one (N : ℕ) :
    Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

private def powerBases (N k : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (k : ℝ))⌋₊).filter Nat.Prime

private def exponentLimit (N : ℕ) : ℕ := ⌊Real.log (N : ℝ) / Real.log 2⌋₊

private theorem weighted_sum_eq_prime_power_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) =
      ∑ k ∈ Finset.Icc 1 (exponentLimit N),
        ∑ p ∈ powerBases N k, Real.log (p : ℝ) / (p : ℝ) ^ k := by
  have hfilter : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) =
      ∑ n ∈ (Finset.Ioc 0 N).filter IsPrimePow,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    rw [Ioc_zero_eq_Icc_one, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hn : IsPrimePow n
    · simp [hn]
    · simp [hn, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
  rw [hfilter]
  have h := Chebyshev.sum_PrimePow_eq_sum_sum
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ)) (Nat.cast_nonneg N)
  simp only [Nat.floor_natCast] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  have hkp : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2
  rw [ArithmeticFunction.vonMangoldt_apply_pow hkp,
    ArithmeticFunction.vonMangoldt_apply_prime hpp, Nat.cast_pow]

/-- The total contribution of genuine higher prime powers is bounded by
one absolute convergent-series constant, independently of the cutoff. -/
theorem weighted_vonMangoldt_sub_prime_sum_bounds (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) ∧
      (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) ≤
          4 * tailSeries := by
  let g : ℕ → ℝ := fun k => ∑ p ∈ powerBases N k, Real.log (p : ℝ) / (p : ℝ) ^ k
  have hK : 1 ≤ exponentLimit N := by
    apply (Nat.one_le_floor_iff _).2
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNR
  have hinterval : Finset.Ioc 1 (exponentLimit N) = Finset.Icc 2 (exponentLimit N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsplit : (∑ k ∈ Finset.Icc 1 (exponentLimit N), g k) =
      g 1 + ∑ k ∈ Finset.Icc 2 (exponentLimit N), g k := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hK, hinterval]
  have hone : g 1 =
      ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
    simp [g, powerBases, Ioc_zero_eq_Icc_one]
  have herror : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)) -
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) =
        ∑ k ∈ Finset.Icc 2 (exponentLimit N), g k := by
    rw [weighted_sum_eq_prime_power_sum]
    change (∑ k ∈ Finset.Icc 1 (exponentLimit N), g k) - _ = _
    rw [hsplit, hone, add_sub_cancel_left]
  rw [herror]
  constructor
  · apply Finset.sum_nonneg
    intro k _hk
    apply Finset.sum_nonneg
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (by positivity)
  · exact sum_higher_power_log_le (exponentLimit N) (powerBases N)
      (fun k _hk p hp => (Finset.mem_filter.mp hp).2.two_le)

/-- Elementary Mertens estimate with coefficient exactly one and one
absolute error constant before every positive natural cutoff. -/
theorem exists_abs_weighted_prime_log_sub_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) -
        Real.log (N : ℝ)| ≤ C := by
  let C : ℝ := Real.log 4 + 5 + 4 * tailSeries
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [C]
    nlinarith [tailSeries_nonneg]
  refine ⟨C, hC, ?_⟩
  intro N hN
  by_cases htwo : 2 ≤ N
  · let S : ℝ := ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
    let P : ℝ := ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
    have herror := weighted_vonMangoldt_sub_prime_sum_bounds N htwo
    have hPS : |P - S| ≤ 4 * tailSeries := by
      rw [abs_sub_comm, abs_of_nonneg herror.1]
      exact herror.2
    have hS := PrimeWeightedLogFactorial.abs_weighted_vonMangoldt_sub_log_le N hN
    calc
      _ = |(P - S) + (S - Real.log (N : ℝ))| := by dsimp [P]; congr 1; ring
      _ ≤ |P - S| + |S - Real.log (N : ℝ)| := abs_add_le _ _
      _ ≤ C := by dsimp [C]; linarith
  · have hnone : N = 1 := by omega
    subst N
    have hempty : ({1} : Finset ℕ).filter Nat.Prime = ∅ := by decide
    simpa only [Finset.Icc_self, hempty, Finset.sum_empty, Nat.cast_one,
      Real.log_one, sub_zero, abs_zero] using hC

end
end TranslatedDepthSeven.PrimeWeightedMertens
