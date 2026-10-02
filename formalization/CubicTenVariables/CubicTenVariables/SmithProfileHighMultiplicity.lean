import CubicTenVariables.SmithProfileMultiplicity
import CubicTenVariables.SmithProfileNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact high-branch Smith-profile exponents

These identities hold for every length and dimension, with valuations in
`[0,a]`. The clipped natural threshold `a-(t-a)` is proved equivalent to
the signed threshold in the actual manuscript penalty. The scalar result
normalizes the admissible-count factor times the Gauss square root.
No matrix, profile-distribution, or exponential-sum estimate is assumed
or asserted by this numerical module.
-/

noncomputable section
namespace CubicTenVariables.SmithProfileHighMultiplicity
open SmithProfileMultiplicity SmithProfileNumerics
open scoped BigOperators

variable {n : ℕ}

/-- Counting levels at or above a valuation, with natural truncation. -/
theorem sum_profile_eq_sum_tsub (j : Fin n → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, profile j i) = ∑ ν : Fin n, (k - j ν) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have he (ν : Fin n) : k + 1 - j ν = k - j ν + if j ν ≤ k then 1 else 0 := by
      split_ifs <;> omega
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    congr 1
    simp only [profile, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The high weight is two on the full interval, minus one on its initial
segment; this additive form avoids subtraction of sums. -/
theorem weighted_profile_add_prefix (j : Fin n → ℕ) (a b : ℕ) :
    (∑ i ∈ Finset.range a, (if i < a-b then 1 else 2) * profile j i) +
      (∑ i ∈ Finset.range (a-b), profile j i) =
        2 * ∑ i ∈ Finset.range a, profile j i := by
  rw [← sum_profile_truncated j (Nat.sub_le a b)]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> omega

/-- The exact doubled exponent for an arbitrary nonnegative offset b.
All sums are over actual finite valuations or their cumulative counts. -/
theorem high_exponent_add_twice_penalty_of_offset (j : Fin n → ℕ)
    (a b : ℕ) (hj : ∀ ν, j ν ≤ a) :
    2 * (∑ ν : Fin n, (b - min b (a-j ν))) + n*a +
      (∑ ν : Fin n, min (b+j ν) a) +
      (∑ i ∈ Finset.range a, (if i < a-b then 1 else 2) * profile j i) =
        2*n*(a+b) := by
  have hscalar (ν : Fin n) :
      2*(b-min b (a-j ν)) + a + min (b+j ν) a + 2*(a-j ν) =
        2*(a+b) + (a-b-j ν) := by
    have hν := hj ν
    omega
  have hs :
      2 * (∑ ν : Fin n, (b - min b (a-j ν))) + n*a +
        (∑ ν : Fin n, min (b+j ν) a) + 2*(∑ ν : Fin n, (a-j ν)) =
      2*n*(a+b) + ∑ ν : Fin n, (a-b-j ν) := by
    calc
      _ = ∑ ν : Fin n,
          (2*(b-min b (a-j ν)) + a + min (b+j ν) a + 2*(a-j ν)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = ∑ ν : Fin n, (2*(a+b) + (a-b-j ν)) := Finset.sum_congr rfl (fun ν _ => hscalar ν)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
        ring
  have hw := weighted_profile_add_prefix j a b
  rw [sum_profile_eq_sum_tsub, sum_profile_eq_sum_tsub] at hw
  omega

/-- The source's exact high-branch doubled-exponent identity. The natural
identity also includes the boundary `a=t`; the penalty comparison below
uses the strict high branch. -/
theorem high_exponent_add_twice_penalty (j : Fin n → ℕ)
    {a t : ℕ} (hj : ∀ ν, j ν ≤ a) (hat : a ≤ t) :
    2 * (∑ ν : Fin n, ((t-a) - min (t-a) (a-j ν))) + n*a +
      (∑ ν : Fin n, min ((t-a)+j ν) a) +
      (∑ i ∈ Finset.range a, (if i < a-(t-a) then 1 else 2) * profile j i) =
        2*n*t := by
  simpa only [Nat.add_sub_of_le hat] using
    high_exponent_add_twice_penalty_of_offset j a (t-a) hj

/-- The natural weight agrees with twice the literal signed-threshold
rational penalty, including t>2a. No condition on i is needed. -/
theorem high_weight_eq_twice_penalty {a t : ℕ} (hat : a < t) (i : ℕ) :
    ((if i < a-(t-a) then 1 else 2 : ℕ) : ℚ) =
      2 * penaltyWeight a t i := by
  have hc : i < a-(t-a) ↔ (i : ℤ) < 2*(a : ℤ)-(t : ℤ) := by omega
  unfold penaltyWeight
  rw [if_neg (not_le.mpr hat)]
  by_cases hi : i < a-(t-a)
  · rw [if_pos hi, if_pos (hc.mp hi)]
    norm_num
  · rw [if_neg hi, if_neg (mt hc.mpr hi)]
    norm_num

/-- The natural weighted count is twice the actual real penalty sum. -/
theorem weighted_profile_cast_eq_twice_penalty (j : Fin n → ℕ)
    {a t : ℕ} (hat : a < t) :
    ((∑ i ∈ Finset.range a,
      (if i < a-(t-a) then 1 else 2) * profile j i : ℕ) : ℝ) =
      2 * ∑ i ∈ Finset.range a, (penaltyWeight a t i : ℝ) * (profile j i : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range a,
        ((if i < a-(t-a) then 1 else 2 : ℕ) : ℝ) * (profile j i : ℝ) := by
      push_cast
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hi : ((if i < a-(t-a) then 1 else 2 : ℕ) : ℝ) =
          2 * (penaltyWeight a t i : ℝ) := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (high_weight_eq_twice_penalty hat i)
        simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat] using h
      rw [hi]
      ring

/-- The exact real exponent left by the admissible count and Gauss square root. -/
theorem high_exponent_real (j : Fin n → ℕ) {a t : ℕ}
    (hj : ∀ ν, j ν ≤ a) (hat : a < t) :
    ((∑ ν : Fin n, ((t-a) - min (t-a) (a-j ν)) : ℕ) : ℝ) +
      (((n*a + ∑ ν : Fin n, min ((t-a)+j ν) a : ℕ) : ℝ) / 2) =
        ((n*t : ℕ) : ℝ) -
          ∑ i ∈ Finset.range a, (penaltyWeight a t i : ℝ) * (profile j i : ℝ) := by
  have hR :
      2 * ((∑ ν : Fin n, ((t-a) - min (t-a) (a-j ν)) : ℕ) : ℝ) +
        ((n*a : ℕ) : ℝ) + ((∑ ν : Fin n, min ((t-a)+j ν) a : ℕ) : ℝ) +
        ((∑ i ∈ Finset.range a,
          (if i < a-(t-a) then 1 else 2) * profile j i : ℕ) : ℝ) =
        2 * ((n*t : ℕ) : ℝ) := by
    have h := high_exponent_add_twice_penalty j hj hat.le
    rw [mul_assoc 2 n t] at h
    exact_mod_cast h
  rw [weighted_profile_cast_eq_twice_penalty j hat] at hR
  push_cast at hR ⊢
  linarith

/-- Scalar normalization with positive real base, independent of any profile. -/
theorem pow_mul_sqrt_pow_eq_rpow (p : ℝ) (hp : 0 < p) (E N : ℕ) :
    p^E * Real.sqrt (p^N) = Real.rpow p ((E : ℝ) + (N : ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast p N, ← Real.rpow_mul hp.le,
    ← Real.rpow_natCast p E, ← Real.rpow_add hp]
  congr 1
  ring

/-- The exact higher-terminal numerical factor, in the manuscript's real
power convention. The statement includes all finite lengths and dimensions. -/
theorem high_factor_eq_rpow (p : ℝ) (hp : 0 < p) (j : Fin n → ℕ)
    {a t : ℕ} (hj : ∀ ν, j ν ≤ a) (hat : a < t) :
    p^(∑ ν : Fin n, ((t-a) - min (t-a) (a-j ν))) *
      Real.sqrt (p^(n*a + ∑ ν : Fin n, min ((t-a)+j ν) a)) =
        Real.rpow p (((n*t : ℕ) : ℝ) -
          ∑ i ∈ Finset.range a, (penaltyWeight a t i : ℝ) * (profile j i : ℝ)) := by
  rw [pow_mul_sqrt_pow_eq_rpow p hp, high_exponent_real j hj hat]

end CubicTenVariables.SmithProfileHighMultiplicity
