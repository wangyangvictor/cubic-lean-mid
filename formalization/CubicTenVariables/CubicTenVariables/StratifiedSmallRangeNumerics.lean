import CubicTenVariables.StratifiedSieveNumerics
import CubicTenVariables.DyadicPowerSum

/-! Summing the product-modulus progression factors in the small-product
range, with the precise denominator exponents of the stratified sieve. -/
noncomputable section
namespace CubicTenVariables.StratifiedSmallRangeNumerics
open scoped BigOperators

theorem product_exponents {s : ℕ} (R d : Fin s → ℝ) (hR : ∀ i, 0 < R i)
    (α δ : ℝ) :
    (∏ i, (R i)^(d i+δ-α+1)) =
      (∏ i, R i)^δ/(∏ i, (R i)^(α-d i-1)) := by
  rw [← Real.finset_prod_rpow Finset.univ R (fun i _ => (hR i).le),
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_sub (hR i)]
  congr 1
  ring

/-- The exact sum of progression weights over any subset of dyadic tuples.
The product threshold c may be any fixed positive constant. -/
theorem sum_le {s : ℕ} (d R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (T c α δ : ℝ) (hT : 0 < T) (hc : 0 < c) (hα : 0 ≤ α)
    (hprod : (∏ i, R i) ≤ c*T) (Q : Finset (Fin s → ℕ))
    (hQ : ∀ q ∈ Q, ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) :
    (∑ q ∈ Q, (1+T/(∏ i, (q i : ℝ)))^α*
      (∏ i, (q i : ℝ)^(d i+δ))) ≤
      ((1+(2:ℝ)^s*c)^α*(∏ i, 3*(2:ℝ)^(max (d i+δ-α) 0)))*
        T^α*((∏ i, R i)^δ/(∏ i, (R i)^(α-d i-1))) := by
  classical
  have hR0 (i) : 0 < R i := lt_of_lt_of_le zero_lt_one (hR i)
  have hfiber (q) (hq : q ∈ Q) :
      (1+T/(∏ i, (q i : ℝ)))^α*(∏ i, (q i : ℝ)^(d i+δ)) ≤
        (1+(2:ℝ)^s*c)^α*T^α*(∏ i, (q i : ℝ)^(d i+δ-α)) := by
    apply StratifiedSieveNumerics.weighted_product (fun i => (q i : ℝ)) d
      T ((2:ℝ)^s*c) α δ
    · intro i
      exact lt_of_lt_of_le (hR0 i) (hQ q hq i).1
    · exact hT
    · positivity
    · calc
        (∏ i, (q i : ℝ)) ≤ ∏ i, 2*R i := Finset.prod_le_prod
          (fun i _ => Nat.cast_nonneg _) (fun i _ => (hQ q hq i).2)
        _ = (2:ℝ)^s*(∏ i, R i) := by rw [Finset.prod_mul_distrib]; simp
        _ ≤ (2:ℝ)^s*(c*T) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := by ring
    · exact hα
  have hdyad := DyadicPowerSum.tuple_sum_le (fun i => d i+δ-α) R hR Q hQ
  have hcoef : 0 ≤ (1+(2:ℝ)^s*c)^α*T^α := by positivity
  calc
    _ ≤ ∑ q ∈ Q, (1+(2:ℝ)^s*c)^α*T^α*(∏ i, (q i : ℝ)^(d i+δ-α)) :=
      Finset.sum_le_sum hfiber
    _ = (1+(2:ℝ)^s*c)^α*T^α*(∑ q ∈ Q, ∏ i, (q i : ℝ)^(d i+δ-α)) := by
      rw [Finset.mul_sum]
    _ ≤ (1+(2:ℝ)^s*c)^α*T^α*((∏ i, 3*(2:ℝ)^(max (d i+δ-α) 0))*
        (∏ i, (R i)^(d i+δ-α+1))) := mul_le_mul_of_nonneg_left hdyad hcoef
    _ = _ := by
      rw [product_exponents R d hR0 α δ]
      ring

end CubicTenVariables.StratifiedSmallRangeNumerics
