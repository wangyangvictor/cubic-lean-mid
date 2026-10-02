import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Uniform epsilon absorption of prime-factor weights

For fixed K and positive epsilon, the product of K times the prime valuations
of m is bounded by one constant times m^epsilon, uniformly for positive m.
The proof separates finitely many small primes from the remaining primes;
a weighted geometric series controls every exponent at a small prime.
-/

noncomputable section

namespace CubicTenVariables.PrimeFactorEpsilonBound

open scoped BigOperators
open Filter

/-- Exponential growth bounds every nonnegative integer, with one constant
for all integers, including zero. -/
theorem exists_linear_le_geometric (r : ℝ) (hr : 1 < r) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ a : ℕ, (a : ℝ) ≤ T * r ^ a := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hρ0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hρ : ‖r⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
    exact inv_lt_one_of_one_lt₀ hr
  have hs : Summable (fun a : ℕ => (a : ℝ) * (r⁻¹) ^ a) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hρ
  let T : ℝ := ∑' a : ℕ, (a : ℝ) * (r⁻¹) ^ a
  have hnonneg (a : ℕ) : 0 ≤ (a : ℝ) * (r⁻¹) ^ a :=
    mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hρ0 a)
  refine ⟨T, tsum_nonneg hnonneg, ?_⟩
  intro a
  have ha : (a : ℝ) * (r⁻¹) ^ a ≤ T := by
    simpa only [Finset.sum_singleton] using
      hs.sum_le_tsum ({a} : Finset ℕ) (fun b _ => hnonneg b)
  have hmul := mul_le_mul_of_nonneg_right ha (pow_nonneg hr0.le a)
  have hcancel : (r⁻¹) ^ a * r ^ a = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
  simpa only [mul_assoc, hcancel, mul_one] using hmul

private theorem weight_le_large_prime_power (K a : ℕ) (hK : 1 ≤ K)
    (ha : 1 ≤ a) (t : ℝ) (ht : 2 * (K : ℝ) ≤ t) :
    ((K * a : ℕ) : ℝ) ≤ t ^ a := by
  have hKa : K ≤ K ^ a := le_self_pow₀ hK (Nat.ne_zero_of_lt ha)
  have ha2 : a ≤ 2 ^ a := (show a < 2 ^ a from Nat.lt_two_pow_self).le
  have hnat : K * a ≤ (2 * K) ^ a := by
    calc
      K * a ≤ K ^ a * 2 ^ a := Nat.mul_le_mul hKa ha2
      _ = (2 * K) ^ a := by rw [mul_pow, mul_comm]
  have hcast : ((K * a : ℕ) : ℝ) ≤ (2 * (K : ℝ)) ^ a := by
    exact_mod_cast hnat
  exact hcast.trans (pow_le_pow_left₀ (by positivity) ht a)

/-- One constant absorbs all prime-factor weights, uniformly over every
positive integer. In particular the empty product at m=1 is included. -/
theorem exists_uniform_prime_factor_bound (K : ℕ) (hK : 1 ≤ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m : ℕ, 1 ≤ m →
      ((∏ p ∈ m.primeFactors, K * m.factorization p : ℕ) : ℝ) ≤
        A * (m : ℝ) ^ ε := by
  classical
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨T, hT, hlinear⟩ := exists_linear_le_geometric r hr
  let C : ℝ := max 1 ((K : ℝ) * T)
  have hC : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hKC : (K : ℝ) * T ≤ C := le_max_right _ _
  have hlimit : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → 2 * (K : ℝ) ≤ (p : ℝ) ^ ε :=
    eventually_atTop.mp (hlimit.eventually (eventually_ge_atTop (2 * (K : ℝ))))
  refine ⟨C ^ P, one_le_pow₀ hC, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt hm
  have hlocal (p : ℕ) (hp : p ∈ m.primeFactors) :
      ((K * m.factorization p : ℕ) : ℝ) ≤
        (if p < P then C else 1) * ((p : ℝ) ^ (m.factorization p)) ^ ε := by
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha : 1 ≤ m.factorization p :=
      hpprime.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    have hpr : r ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
    have heq : ((p : ℝ) ^ (m.factorization p)) ^ ε =
        ((p : ℝ) ^ ε) ^ (m.factorization p) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm,
        Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    rw [heq]
    by_cases hsmall : p < P
    · rw [if_pos hsmall]
      calc
        ((K * m.factorization p : ℕ) : ℝ) = (K : ℝ) * (m.factorization p : ℝ) := by simp
        _ ≤ (K : ℝ) * (T * r ^ m.factorization p) :=
          mul_le_mul_of_nonneg_left (hlinear _) (Nat.cast_nonneg K)
        _ = ((K : ℝ) * T) * r ^ m.factorization p := by ring
        _ ≤ C * ((p : ℝ) ^ ε) ^ m.factorization p :=
          mul_le_mul hKC (pow_le_pow_left₀ (zero_lt_one.trans hr).le hpr _)
            (pow_nonneg (zero_lt_one.trans hr).le _) hC0
    · rw [if_neg hsmall, one_mul]
      exact weight_le_large_prime_power K _ hK ha _ (hP p (Nat.le_of_not_gt hsmall))
  have hcard : (m.primeFactors.filter (fun p => p < P)).card ≤ P := by
    calc
      _ ≤ (Finset.range P).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = P := Finset.card_range P
  have hcoeff : (∏ p ∈ m.primeFactors, if p < P then C else 1) ≤ C ^ P := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    exact pow_le_pow_right₀ hC hcard
  have hproduct : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ ε) =
      (m : ℝ) ^ ε := by
    rw [Real.finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ε]
    congr 1
    have he := Nat.factorization_prod_pow_eq_self hm0
    rw [Nat.prod_factorization_eq_prod_primeFactors] at he
    exact_mod_cast he
  calc
    ((∏ p ∈ m.primeFactors, K * m.factorization p : ℕ) : ℝ) =
        ∏ p ∈ m.primeFactors, ((K * m.factorization p : ℕ) : ℝ) := by simp
    _ ≤ ∏ p ∈ m.primeFactors,
        (if p < P then C else 1) * ((p : ℝ) ^ m.factorization p) ^ ε :=
      Finset.prod_le_prod (fun p _ => Nat.cast_nonneg _) hlocal
    _ = (∏ p ∈ m.primeFactors, if p < P then C else 1) *
        (∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ ε) :=
      Finset.prod_mul_distrib
    _ ≤ C ^ P * (∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ ε) :=
      mul_le_mul_of_nonneg_right hcoeff
        (Finset.prod_nonneg fun p _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg p) _) _)
    _ = C ^ P * (m : ℝ) ^ ε := by rw [hproduct]

end CubicTenVariables.PrimeFactorEpsilonBound
