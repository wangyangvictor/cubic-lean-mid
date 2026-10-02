import CubicTenVariables.DyadicPowerSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-! Elementary positive-multiple power sums with a literal divisor saving.
The exact count of positive multiples is already in Mathlib. Applying it
to the integer floor of the real endpoint introduces no additive error,
so the bound remains valid when the divisor exceeds the whole interval. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DivisiblePowerSum
open scoped BigOperators

/-- Positive natural multiples of s in the closed real interval (0,2X]. -/
def interval (X : ℝ) (s : ℕ) : Finset ℕ :=
  (Finset.range (⌊2*X⌋₊+1)).filter (fun u => u ≠ 0 ∧ s ∣ u)

theorem mem_interval (X : ℝ) (hX : 1 ≤ X) (s u : ℕ) :
    u ∈ interval X s ↔ 0 < u ∧ (u : ℝ) ≤ 2*X ∧ s ∣ u := by
  simp only [interval, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hu,hpos,hdiv⟩
    refine ⟨Nat.pos_of_ne_zero hpos,?_,hdiv⟩
    exact (show (u : ℝ) ≤ (⌊2*X⌋₊ : ℝ) by exact_mod_cast hu).trans
      (Nat.floor_le (by linarith))
  · rintro ⟨hpos,hu,hdiv⟩
    exact ⟨Nat.le_floor hu,ne_of_gt hpos,hdiv⟩

/-- Exact cardinality, including an empty range and divisor zero. -/
theorem card_interval (X : ℝ) (s : ℕ) :
    (interval X s).card = ⌊2*X⌋₊ / s := by
  exact Nat.card_multiples' ⌊2*X⌋₊ s

/-- No additive endpoint loss occurs for positive multiples. -/
theorem card_interval_le (X : ℝ) (hX : 1 ≤ X) (s : ℕ) (hs : 1 ≤ s) :
    ((interval X s).card : ℝ) ≤ 2*X/(s : ℝ) := by
  have hs0 : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  rw [card_interval]
  exact Nat.cast_div_le.trans
    (div_le_div_of_nonneg_right (Nat.floor_le (by linarith)) hs0.le)

/-- The literal interval is empty when its smallest possible positive
multiple exceeds the upper endpoint. -/
theorem interval_eq_empty_of_lt (X : ℝ) (hX : 1 ≤ X) (s : ℕ)
    (hsX : 2*X < (s : ℝ)) : interval X s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu0,huX,hsu⟩ := (mem_interval X hX s u).mp hu
  have hsuR : (s : ℝ) ≤ u := by exact_mod_cast Nat.le_of_dvd hu0 hsu
  linarith

/-- The same cardinality bound holds for any actual finite subfamily. -/
theorem card_le (X : ℝ) (hX : 1 ≤ X) (s : ℕ) (hs : 1 ≤ s)
    (Q : Finset ℕ) (hQ : ∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X ∧ s ∣ u) :
    (Q.card : ℝ) ≤ 2*X/(s : ℝ) := by
  have hsub : Q ⊆ interval X s := fun u hu => (mem_interval X hX s u).mpr (hQ u hu)
  exact (show (Q.card : ℝ) ≤ (interval X s).card by
    exact_mod_cast Finset.card_le_card hsub).trans (card_interval_le X hX s hs)

/-- Any finite family of positive multiples admits the explicit constant
2^(a+1), for every nonnegative real exponent a. -/
theorem sum_le (a X : ℝ) (ha : 0 ≤ a) (hX : 1 ≤ X) (s : ℕ) (hs : 1 ≤ s)
    (Q : Finset ℕ) (hQ : ∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X ∧ s ∣ u) :
    (∑ u ∈ Q, (u : ℝ)^a) ≤ (2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  calc
    (∑ u ∈ Q, (u : ℝ)^a) ≤ ∑ _u ∈ Q, (2*X)^a :=
      Finset.sum_le_sum fun u hu => Real.rpow_le_rpow (Nat.cast_nonneg u) (hQ u hu).2.1 ha
    _ = (Q.card : ℝ)*(2*X)^a := by simp
    _ ≤ (2*X/(s : ℝ))*(2*X)^a :=
      mul_le_mul_of_nonneg_right (card_le X hX s hs Q hQ)
        (Real.rpow_nonneg (by positivity) _)
    _ = (2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add hX0,
        Real.rpow_one,Real.rpow_one]
      ring

theorem interval_sum_le (a X : ℝ) (ha : 0 ≤ a) (hX : 1 ≤ X)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ u ∈ interval X s, (u : ℝ)^a) ≤ (2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ) :=
  sum_le a X ha hX s hs _ (fun u hu => (mem_interval X hX s u).mp hu)

/-- Directly compatible with the project's existing closed dyadic interval. -/
theorem dyadic_sum_le (a X : ℝ) (ha : 0 ≤ a) (hX : 1 ≤ X)
    (s : ℕ) (hs : 1 ≤ s) :
    (∑ u ∈ (DyadicPowerSum.interval X).filter (fun u => s ∣ u), (u : ℝ)^a) ≤
      (2 : ℝ)^(a+1)*X^(a+1)/(s : ℝ) := by
  apply sum_le a X ha hX s hs
  intro u hu
  obtain ⟨hu,hdiv⟩ := Finset.mem_filter.mp hu
  exact ⟨DyadicPowerSum.positive_of_mem_interval X hX u hu,
    ((DyadicPowerSum.mem_interval X hX u).mp hu).2,hdiv⟩

/-- The uniform constant depends only on the real exponent and precedes
all real endpoints, positive divisors, and finite subfamilies. -/
theorem exists_bound (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : ℕ, 1 ≤ s →
      ∀ Q : Finset ℕ, (∀ u ∈ Q, 0 < u ∧ (u : ℝ) ≤ 2*X ∧ s ∣ u) →
        (∑ u ∈ Q, (u : ℝ)^a) ≤ C*X^(a+1)/(s : ℝ) := by
  refine ⟨(2 : ℝ)^(a+1),Real.one_le_rpow (by norm_num) (by linarith),?_⟩
  exact fun X hX s hs Q hQ => sum_le a X ha hX s hs Q hQ

end CubicTenVariables.DivisiblePowerSum
