import CubicTenVariables.SmithProfileMultiplicity
import CubicTenVariables.SmithProfileNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact conversion of the low terminal kernel exponent to the source's
rational profile penalties. These identities hold for arbitrary profile
lengths, including t=0, and arbitrary coordinate dimension. -/

noncomputable section
namespace CubicTenVariables.SmithProfileLowExponent
open SmithProfileMultiplicity SmithProfileNumerics
open scoped BigOperators

theorem twice_low_penalty {n a t : ℕ} (j : Fin n → ℕ) (hta : t ≤ a) :
    2 * (∑ i ∈ Finset.range a,
      (penaltyWeight a t i : ℝ) * (profile j i : ℝ)) =
      ((∑ i ∈ Finset.range a, if i < t then profile j i else 0 : ℕ) : ℝ) := by
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < t
  · norm_num [penaltyWeight, hta, hi]
    ring
  · simp [penaltyWeight, hta, hi]

/-- The actual source exponent is half of the integer squared-norm
exponent in the branch t<=a. No upper bound on the j entries is needed. -/
theorem low_exponent_half {n a t : ℕ} (j : Fin n → ℕ) (hta : t ≤ a) :
    ((n*t + ∑ ν : Fin n, min (j ν) t : ℕ) : ℝ) / 2 =
      ((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
        (penaltyWeight a t i : ℝ) * (profile j i : ℝ) := by
  have hn := squared_exponent_add_twice_penalty j hta
  have hr : ((n*t + ∑ ν : Fin n, min (j ν) t : ℕ) : ℝ) +
      ((∑ i ∈ Finset.range a, if i < t then profile j i else 0 : ℕ) : ℝ) =
      2 * ((n*t : ℕ) : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_assoc] using hn :
      n*t + (∑ ν : Fin n, min (j ν) t) +
        (∑ i ∈ Finset.range a, if i < t then profile j i else 0) = 2 * (n*t))
  rw [← twice_low_penalty j hta] at hr
  linarith

/-- The kernel square root is exactly the manuscript's real power,
with its rational half-penalty interpreted in the real exponent. -/
theorem low_factor_eq_rpow {n a t : ℕ} (p : ℝ) (hp : 0 < p)
    (j : Fin n → ℕ) (hta : t ≤ a) :
    Real.sqrt (p ^ (n*t + ∑ ν : Fin n, min (j ν) t)) =
      Real.rpow p (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
        (penaltyWeight a t i : ℝ) * (profile j i : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hp.le]
  congr 1
  simpa only [div_eq_mul_inv, one_mul] using low_exponent_half j hta

end CubicTenVariables.SmithProfileLowExponent
