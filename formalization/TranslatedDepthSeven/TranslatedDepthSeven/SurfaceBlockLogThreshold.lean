import TranslatedDepthSeven.AffinePlaneMonomialWeights
import TranslatedDepthSeven.PrimeWeightedRange
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Literal logarithmic normalization of the surface-block determinant
bound. The prime cutoff error is retained; no claim is made that a fixed
block works as the prime cutoff grows. -/

namespace TranslatedDepthSeven.SurfaceBlockLogThreshold
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem block_count_formula (d k : ℕ) :
    ((d * affinePlaneMonomialCount k : ℕ) : ℝ) =
      (d : ℝ) * (k + 1) * (k + 2) / 2 := by
  have hc : 2 * (affinePlaneMonomialCount k : ℝ) =
      ((k : ℝ) + 1) * (k + 2) := by
    exact_mod_cast two_mul_affinePlaneMonomialCount k
  push_cast
  nlinarith [congrArg (fun x : ℝ => (d : ℝ) * x) hc]

theorem block_count_pos (d k : ℕ) (hd : 0 < d) :
    0 < d * affinePlaneMonomialCount k := by
  have hc := two_mul_affinePlaneMonomialCount k
  have hcount : 0 < affinePlaneMonomialCount k := by nlinarith
  exact Nat.mul_pos hd hcount

theorem block_weight_eq_count_mul (d k : ℕ) :
    ((d * affinePlaneMonomialWeight k : ℕ) : ℝ) =
      ((d * affinePlaneMonomialCount k : ℕ) : ℝ) * (2 * (k : ℝ) / 3) := by
  have hc : 2 * (affinePlaneMonomialCount k : ℝ) =
      ((k : ℝ) + 1) * (k + 2) := by
    exact_mod_cast two_mul_affinePlaneMonomialCount k
  have hw : 3 * (affinePlaneMonomialWeight k : ℝ) =
      (k : ℝ) * (k + 1) * (k + 2) := by
    exact_mod_cast three_mul_affinePlaneMonomialWeight k
  have hratio : 3 * (affinePlaneMonomialWeight k : ℝ) =
      2 * k * (affinePlaneMonomialCount k : ℝ) := by
    nlinarith [congrArg (fun x : ℝ => (k : ℝ) * x) hc]
  push_cast
  nlinarith [congrArg (fun x : ℝ => (d : ℝ) * x) hratio]

/-- The exact normalized affine weight of the actual monomial block. -/
theorem block_weight_div_count (d k : ℕ) (hd : 0 < d) :
    ((d * affinePlaneMonomialWeight k : ℕ) : ℝ) /
      ((d * affinePlaneMonomialCount k : ℕ) : ℝ) = 2 * (k : ℝ) / 3 := by
  have hn : ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (block_count_pos d k hd).ne'
  rw [block_weight_eq_count_mul]
  field_simp

private theorem log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
  have hn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have h := Real.log_le_log (by positivity) hn
  simpa only [Real.log_pow] using h

private theorem generic_log_bound (n w b D H R : ℕ)
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    Real.log ((n.factorial * (D * H ^ b) ^ n * R ^ w : ℕ) : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) +
        (n : ℝ) * (Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ)) +
          (w : ℝ) * Real.log (R : ℝ) := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hH0 : (H : ℝ) ≠ 0 := by positivity
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  rw [Real.log_mul (mul_ne_zero hfac (pow_ne_zero n (mul_ne_zero hD0 (pow_ne_zero b hH0))))
      (pow_ne_zero w hR0),
    Real.log_mul hfac (pow_ne_zero n (mul_ne_zero hD0 (pow_ne_zero b hH0))),
    Real.log_pow, Real.log_pow,
    Real.log_mul hD0 (pow_ne_zero b hH0), Real.log_pow]
  linarith [log_factorial_le n]

/-- The literal determinant-height expression, with the linear-coordinate
height factor (d+1)^3 retained exactly. -/
theorem log_block_bound_le (d k b D H B : ℕ)
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hB : 1 ≤ B) :
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) ≤
      ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
        (Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
          Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
            (2 * (k : ℝ) / 3) *
              (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ))) := by
  have hR : 1 ≤ (d + 1) ^ 3 * B := by
    change 0 < (d + 1) ^ 3 * B
    positivity
  have h := generic_log_bound (d * affinePlaneMonomialCount k)
    (d * affinePlaneMonomialWeight k) b D H ((d + 1) ^ 3 * B) hD hH hR
  have heq : Real.log ((((d + 1) ^ 3) * B : ℕ) : ℝ) =
      3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [heq, block_weight_eq_count_mul] at h
  convert h using 1
  ring

/-- The normalized archimedean bound, with exact affine-weight coefficient
2k/3 and no asymptotic error or point-count premise. -/
theorem normalized_log_block_bound_le (d k b D H B : ℕ) (hd : 0 < d)
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hB : 1 ≤ B) :
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) /
      ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ≤
        Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
          Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
            (2 * (k : ℝ) / 3) *
              (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) := by
  have hn : (0 : ℝ) < (d * affinePlaneMonomialCount k : ℕ) := by
    exact_mod_cast block_count_pos d k hd
  apply (div_le_iff₀ hn).2
  simpa only [mul_comm] using log_block_bound_le d k b D H B hD hH hB

private theorem rpow_three_halves (x : ℝ) (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Exact conversion of a normalized scalar inequality to the current
mixed-prime determinant threshold. The negative unweighted-prime term is
retained, so increasing the cutoff with fixed degree is not justified. -/
theorem log_block_bound_lt_mixed_gain (d k b D H B : ℕ) (hd : 0 < d)
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (K A S T : ℝ)
    (hgain : Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
      Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
        (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) <
          (2 * Real.sqrt 2 / 3) / Real.sqrt K *
            Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) * S -
              (Real.sqrt 2 * A / Real.sqrt K) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) - 2 * T) :
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
      (2 * Real.sqrt 2 / 3) / Real.sqrt K *
        ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) * S -
          (Real.sqrt 2 * A / Real.sqrt K) *
            (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
              Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
          2 * (d * affinePlaneMonomialCount k : ℕ) * T := by
  have hn : (0 : ℝ) < (d * affinePlaneMonomialCount k : ℕ) := by
    exact_mod_cast block_count_pos d k hd
  have h := (log_block_bound_le d k b D H B hD hH hB).trans_lt
    (mul_lt_mul_of_pos_left hgain hn)
  rw [rpow_three_halves _ hn]
  convert h using 1
  ring

/-- The square-root row count retains the sharp degree dependence. -/
theorem sharp_gain_coefficient_ge (d k : ℕ) :
    (2 / 3 : ℝ) * Real.sqrt (d : ℝ) * ((k : ℝ) + 1) ≤
      (2 * Real.sqrt 2 / 3) *
        Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) := by
  have hsq : (Real.sqrt (d : ℝ) * ((k : ℝ) + 1)) ^ 2 ≤
      2 * ((d * affinePlaneMonomialCount k : ℕ) : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), block_count_formula]
    nlinarith [show (0 : ℝ) ≤ (d : ℝ) * ((k : ℝ) + 1) by positivity]
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hs
  have h := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2 / 3)
  convert h using 1 <;> ring

/-- Concrete large-prime-family version of the sufficient scalar
inequality. Its negative cutoff term remains `2 log(4) N`; no degree or
cutoff existence is assumed or asserted. The constant C is absolute and
precedes every surface degree, height, cutoff and excluded certificate. -/
theorem exists_largePrimeRange_log_threshold :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d k b D H B N E Dc : ℕ, ∀ K A : ℝ,
      0 < d → 1 ≤ D → 1 ≤ H → 1 ≤ B → 0 < K →
      1 ≤ Real.log (H : ℝ) → ⌈Real.log (H : ℝ)⌉₊ ≤ N →
      0 < Dc → Dc ≤ H ^ E →
      (Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
        Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
          (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) <
            (2 * Real.sqrt 2 / 3) / Real.sqrt K *
              Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                (Real.log (N : ℝ) - Real.log (Real.log (H : ℝ)) - C - E) -
              (Real.sqrt 2 * A / Real.sqrt K) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) -
              2 * Real.log 4 * (N : ℝ)) →
      Real.log (((d * affinePlaneMonomialCount k).factorial *
        (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
          (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
        (2 * Real.sqrt 2 / 3) / Real.sqrt K *
          ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
          (∑ p ∈ PrimeWeightedRange.largePrimesAvoiding H N Dc,
            Real.log (p : ℝ) / (p : ℝ)) -
          (Real.sqrt 2 * A / Real.sqrt K) *
            (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
              Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
          2 * (d * affinePlaneMonomialCount k : ℕ) *
            (∑ p ∈ PrimeWeightedRange.largePrimesAvoiding H N Dc, Real.log (p : ℝ)) := by
  obtain ⟨C, hC, hrange⟩ := PrimeWeightedRange.exists_largePrimeRange_estimates
  refine ⟨C, hC, ?_⟩
  intro d k b D H B N E Dc K A hd hD hH hB hK hlogH hN hDc hheight hscalar
  obtain ⟨hweighted, hunweighted⟩ := hrange H N E Dc hlogH hN hDc hheight
  apply log_block_bound_lt_mixed_gain d k b D H B hd hD hH hB K A
  apply hscalar.trans_le
  have hc : 0 ≤ (2 * Real.sqrt 2 / 3) / Real.sqrt K *
      Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) := by positivity
  have hw := mul_le_mul_of_nonneg_left hweighted hc
  linarith

/-- Packet version: the exact local divisor q^E contributes E log(q).
The modulus is a literal positive natural and the exponent is arbitrary;
no local divisibility is asserted by this numerical conversion. -/
theorem log_block_bound_lt_packet_mixed_gain
    (d k b D H B E q : ℕ) (hd : 0 < d) (_hq : 0 < q)
    (hD : 1 ≤ D) (hH : 1 ≤ H) (hB : 1 ≤ B) (K A S T : ℝ)
    (hgain : Real.log ((d * affinePlaneMonomialCount k : ℕ) : ℝ) +
      Real.log (D : ℝ) + (b : ℝ) * Real.log (H : ℝ) +
        (2 * (k : ℝ) / 3) * (3 * Real.log ((d : ℝ) + 1) + Real.log (B : ℝ)) <
          ((E : ℝ) / ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) * Real.log (q : ℝ) +
          ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
            Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) * S -
              (Real.sqrt 2 * A / Real.sqrt K) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ) - 2 * T)) :
    Real.log (((d * affinePlaneMonomialCount k).factorial *
      (D * H ^ b) ^ (d * affinePlaneMonomialCount k) *
        (((d + 1) ^ 3) * B) ^ (d * affinePlaneMonomialWeight k) : ℕ) : ℝ) <
      (E : ℝ) * Real.log (q : ℝ) +
        ((2 * Real.sqrt 2 / 3) / Real.sqrt K *
          ((d * affinePlaneMonomialCount k : ℕ) : ℝ) ^ (3 / 2 : ℝ) * S -
            (Real.sqrt 2 * A / Real.sqrt K) *
              (((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
                Real.sqrt ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) -
            2 * (d * affinePlaneMonomialCount k : ℕ) * T) := by
  have hn : (0 : ℝ) < (d * affinePlaneMonomialCount k : ℕ) := by
    exact_mod_cast block_count_pos d k hd
  have he : ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
      ((E : ℝ) / ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) = E := by
    field_simp
  have h := (log_block_bound_le d k b D H B hD hH hB).trans_lt
    (mul_lt_mul_of_pos_left hgain hn)
  have hm : ((d * affinePlaneMonomialCount k : ℕ) : ℝ) *
      (((E : ℝ) / ((d * affinePlaneMonomialCount k : ℕ) : ℝ)) * Real.log (q : ℝ)) =
        (E : ℝ) * Real.log (q : ℝ) := by rw [← mul_assoc, he]
  rw [mul_add, hm] at h
  rw [rpow_three_halves _ hn]
  convert h using 1
  ring

end
end TranslatedDepthSeven.SurfaceBlockLogThreshold
