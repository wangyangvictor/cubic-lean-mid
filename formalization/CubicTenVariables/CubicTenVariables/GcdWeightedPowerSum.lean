import CubicTenVariables.DivisiblePowerSum
import Mathlib.NumberTheory.Divisors

/-! Positive power sums with an actual gcd weight. The divisor expansion
retains the cutoff s ≤ 2X, so the positive power s^(k-1) is bounded by the
interval endpoint rather than by the exceptional integer. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GcdWeightedPowerSum
open scoped BigOperators Classical

private theorem divisor_term_le (a X : ℝ) (hX : 1 ≤ X)
    (s k : ℕ) (hs : 1 ≤ s) (hsX : (s : ℝ) ≤ 2*X) (hk : 1 ≤ k) :
    (s : ℝ)^k * ((2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ)) ≤
      (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ)) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have h2X : 0 < 2*X := by positivity
  calc
    _ = (s : ℝ)^l * ((2 : ℝ)^(a+1)*X^(a+1)) := by
      rw [pow_succ]
      field_simp
    _ ≤ (2*X)^l * ((2 : ℝ)^(a+1)*X^(a+1)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg s) hsX l)
        (by positivity)
    _ = (2*X)^((l : ℝ)+(a+1)) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le,
        ← Real.rpow_natCast,← Real.rpow_add h2X]
    _ = _ := by
      have he : (l : ℝ)+(a+1) = a+(↑(l+1) : ℝ) := by push_cast; ring
      rw [he,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le]

/-- The bound applies to any finite subfamily of the positive integers up
to the real endpoint 2X. Both exponents and the divisor count are literal. -/
theorem sum_le (a X : ℝ) (ha : 0 ≤ a) (hX : 1 ≤ X)
    (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X) :
    (∑ u ∈ Q, (u : ℝ)^a*(Nat.gcd u Δ : ℝ)^k) ≤
      (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ))*(Δ.divisors.card : ℝ) := by
  let S := Δ.divisors.filter (fun s : ℕ => (s : ℝ) ≤ 2*X)
  have hΔ0 : Δ ≠ 0 := by omega
  have hnonneg (u s : ℕ) :
      0 ≤ if s ∣ u then (s : ℝ)^k*(u : ℝ)^a else 0 := by
    split_ifs <;> positivity
  have hexpand (u : ℕ) (hu : u ∈ Q) :
      (u : ℝ)^a*(Nat.gcd u Δ : ℝ)^k ≤
        ∑ s ∈ S, if s ∣ u then (s : ℝ)^k*(u : ℝ)^a else 0 := by
    have hg : Nat.gcd u Δ ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right u Δ,hΔ0⟩,?_⟩
      have hgu : (Nat.gcd u Δ : ℝ) ≤ u := by
        exact_mod_cast Nat.le_of_dvd (hQ u hu).1 (Nat.gcd_dvd_left u Δ)
      exact hgu.trans (hQ u hu).2
    have hb := Finset.single_le_sum (fun s _ => hnonneg u s) hg
    simpa only [if_pos (Nat.gcd_dvd_left u Δ),mul_comm] using hb
  have hsum (s : ℕ) (hs : s ∈ S) :
      (∑ u ∈ Q, if s ∣ u then (s : ℝ)^k*(u : ℝ)^a else 0) ≤
        (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ)) := by
    obtain ⟨hsΔ,hsX⟩ := Finset.mem_filter.mp hs
    have hs1 : 1 ≤ s := Nat.pos_of_mem_divisors hsΔ
    have hb := DivisiblePowerSum.sum_le a X ha hX s hs1
      (Q.filter fun u => s ∣ u) (fun u hu =>
        ⟨(hQ u (Finset.mem_filter.mp hu).1).1,
          (hQ u (Finset.mem_filter.mp hu).1).2,(Finset.mem_filter.mp hu).2⟩)
    calc
      _ = (s : ℝ)^k * ∑ u ∈ Q.filter (fun u => s ∣ u), (u : ℝ)^a := by
        rw [Finset.mul_sum,Finset.sum_filter]
      _ ≤ (s : ℝ)^k * ((2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := divisor_term_le a X hX s k hs1 hsX hk
  calc
    _ ≤ ∑ u ∈ Q, ∑ s ∈ S, if s ∣ u then (s : ℝ)^k*(u : ℝ)^a else 0 :=
      Finset.sum_le_sum hexpand
    _ = ∑ s ∈ S, ∑ u ∈ Q, if s ∣ u then (s : ℝ)^k*(u : ℝ)^a else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _s ∈ S, (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ)) :=
      Finset.sum_le_sum hsum
    _ = (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ))*(S.card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _) :
        (S.card : ℝ) ≤ Δ.divisors.card) (by positivity)

/-- The existing literal closed dyadic interval [X,2X]. -/
theorem dyadic_sum_le (a X : ℝ) (ha : 0 ≤ a) (hX : 1 ≤ X)
    (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    (∑ u ∈ DyadicPowerSum.interval X, (u : ℝ)^a*(Nat.gcd u Δ : ℝ)^k) ≤
      (2 : ℝ)^(a+(k : ℝ))*X^(a+(k : ℝ))*(Δ.divisors.card : ℝ) :=
  sum_le a X ha hX Δ k hΔ hk _ (fun u hu =>
    ⟨DyadicPowerSum.positive_of_mem_interval X hX u hu,
      ((DyadicPowerSum.mem_interval X hX u).mp hu).2⟩)

/-- The prime-factor exponent needed in the fixed-frequency estimate. -/
theorem prime_sum_le (X : ℝ) (hX : 1 ≤ X) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (Q : Finset ℕ) (hQ : ∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X) :
    (∑ u ∈ Q, (u : ℝ)^((11 : ℝ)/2)*(Nat.gcd u Δ : ℝ)) ≤
      (2 : ℝ)^((13 : ℝ)/2)*X^((13 : ℝ)/2)*(Δ.divisors.card : ℝ) := by
  simpa only [Nat.cast_one,pow_one,show (11 : ℝ)/2+1 = 13/2 by norm_num] using
    sum_le ((11 : ℝ)/2) X (by norm_num) hX Δ 1 hΔ (by norm_num) Q hQ

/-- The prime-square-factor exponent needed in the fixed-frequency estimate. -/
theorem square_sum_le (X : ℝ) (hX : 1 ≤ X) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (Q : Finset ℕ) (hQ : ∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X) :
    (∑ u ∈ Q, (u : ℝ)^11*(Nat.gcd u Δ : ℝ)^2) ≤
      (2 : ℝ)^13*X^13*(Δ.divisors.card : ℝ) := by
  have hb := sum_le 11 X (by norm_num) hX Δ 2 hΔ (by norm_num) Q hQ
  norm_num only [Nat.cast_ofNat,show (11 : ℝ)+2 = 13 by norm_num,
    Real.rpow_ofNat] at hb
  simpa only [show (2 : ℝ)^13 = 8192 by norm_num] using hb

end CubicTenVariables.GcdWeightedPowerSum
