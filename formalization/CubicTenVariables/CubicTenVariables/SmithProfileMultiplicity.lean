import Mathlib.Tactic

/-!
The exact multiplicity/profile identity in the t <= a branch of the
terminal Smith estimate. These are finite combinatorial statements about
the displayed valuations; no Smith form or matrix-kernel formula is assumed
or constructed here.
-/

namespace CubicTenVariables.SmithProfileMultiplicity
open scoped BigOperators

variable {n : ℕ}

/-- The cumulative multiplicity c_i = #{nu : j_nu <= i}. -/
def profile (j : Fin n → ℕ) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun ν => j ν ≤ i)).card

theorem profile_le (j : Fin n → ℕ) (i : ℕ) : profile j i ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem profile_mono (j : Fin n → ℕ) : Monotone (profile j) := by
  intro i k hik
  apply Finset.card_le_card
  intro ν hν
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hν ⊢
  exact hν.trans hik

theorem sum_greater_indicator_add_profile (j : Fin n → ℕ) (i : ℕ) :
    (∑ ν : Fin n, if i < j ν then 1 else 0) + profile j i = n := by
  simp only [profile, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  have he (ν : Fin n) : (if i < j ν then 1 else 0) +
      (if j ν ≤ i then 1 else 0) = (1 : ℕ) := by
    split_ifs <;> omega
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]

/-- Double counting the levels below each truncated Smith valuation. The
additive form avoids any truncated-subtraction ambiguity. -/
theorem sum_min_add_sum_profile (j : Fin n → ℕ) (t : ℕ) :
    (∑ ν : Fin n, min (j ν) t) +
      (∑ i ∈ Finset.range t, profile j i) = n * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he (ν : Fin n) : min (j ν) (t+1) =
        min (j ν) t + if t < j ν then 1 else 0 := by
      split_ifs <;> omega
    simp only [he, Finset.sum_add_distrib, Finset.sum_range_succ]
    have hc := sum_greater_indicator_add_profile j t
    calc
      _ = ((∑ ν : Fin n, min (j ν) t) + ∑ i ∈ Finset.range t, profile j i) +
          ((∑ ν : Fin n, if t < j ν then 1 else 0) + profile j t) := by omega
      _ = n * t + n := by rw [ih, hc]
      _ = n * (t+1) := by ring

theorem sum_min_eq_sub_sum_profile (j : Fin n → ℕ) (t : ℕ) :
    (∑ ν : Fin n, min (j ν) t) = n * t - ∑ i ∈ Finset.range t, profile j i := by
  have h := sum_min_add_sum_profile j t
  omega

/-- With t <= a the penalty can be written on the full profile of length a,
exactly as twice lambda_i in the first branch of the manuscript. -/
theorem sum_profile_truncated (j : Fin n → ℕ) {t a : ℕ} (hta : t ≤ a) :
    (∑ i ∈ Finset.range a, if i < t then profile j i else 0) =
      ∑ i ∈ Finset.range t, profile j i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Exact exponent bookkeeping for the squared quadratic estimate. The
left side is nt plus the truncated valuation sum; the third summand on
the left is twice the Smith penalty. -/
theorem squared_exponent_add_twice_penalty (j : Fin n → ℕ)
    {t a : ℕ} (hta : t ≤ a) :
    n*t + (∑ ν : Fin n, min (j ν) t) +
      (∑ i ∈ Finset.range a, if i < t then profile j i else 0) = 2*n*t := by
  rw [sum_profile_truncated j hta]
  have h := sum_min_add_sum_profile j t
  calc
    _ = n*t + n*t := by omega
    _ = 2*n*t := by ring

end CubicTenVariables.SmithProfileMultiplicity
