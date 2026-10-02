import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Real inequalities and a finite product threshold crossing used by the
stratified sieve. No counting or geometric estimate is an assumption. -/
noncomputable section
namespace CubicTenVariables.StratifiedSieveNumerics
open scoped BigOperators

/-- In the small-product range, the progression factor is a pure power up
to an explicit constant. -/
theorem small_modulus (T Q c α : ℝ) (hT : 0 < T) (hQ : 0 < Q)
    (hc : 0 < c) (hQT : Q ≤ c*T) (hα : 0 ≤ α) :
    (1+T/Q)^α ≤ (1+c)^α*T^α/Q^α := by
  have h1 : 1 ≤ c*T/Q := (one_le_div hQ).mpr hQT
  have hbase : 1+T/Q ≤ (1+c)*(T/Q) := by
    calc
      _ ≤ c*T/Q+T/Q := add_le_add h1 le_rfl
      _ = _ := by ring
  calc
    _ ≤ ((1+c)*(T/Q))^α :=
      Real.rpow_le_rpow (by positivity) hbase hα
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (div_nonneg hT.le hQ.le),
        Real.div_rpow hT.le hQ.le]
      ring

/-- Exact distribution of the denominator through the product weights. -/
theorem weighted_product {s : ℕ} (q d : Fin s → ℝ) (T c α δ : ℝ)
    (hq : ∀ i, 0 < q i) (hT : 0 < T) (hc : 0 < c)
    (hQT : (∏ i, q i) ≤ c*T) (hα : 0 ≤ α) :
    (1+T/(∏ i, q i))^α*(∏ i, (q i)^(d i+δ)) ≤
      (1+c)^α*T^α*(∏ i, (q i)^(d i+δ-α)) := by
  have hQ : 0 < ∏ i, q i := Finset.prod_pos fun i _ => hq i
  have hweights : 0 ≤ ∏ i, (q i)^(d i+δ) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hq i).le _
  have hprod : (∏ i, q i)^α = ∏ i, (q i)^α :=
    (Real.finset_prod_rpow Finset.univ q (fun i _ => (hq i).le) α).symm
  calc
    _ ≤ ((1+c)^α*T^α/(∏ i, q i)^α)*(∏ i, (q i)^(d i+δ)) :=
      mul_le_mul_of_nonneg_right (small_modulus T _ c α hT hQ hc hQT hα) hweights
    _ = ((1+c)^α*T^α)*((∏ i, (q i)^(d i+δ))/(∏ i, (q i)^α)) := by
      rw [hprod]
      ring
    _ = ((1+c)^α*T^α)*(∏ i, (q i)^(d i+δ)/(q i)^α) := by
      rw [Finset.prod_div_distrib]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.rpow_sub (hq i) (d i+δ) α).symm

/-- Product of the scales strictly after the selected index. -/
def tailProduct {s : ℕ} (R : Fin s → ℝ) (j : Fin s) : ℝ :=
  ∏ i, if j < i then R i else 1

theorem tailProduct_eq_filtered {s : ℕ} (R : Fin s → ℝ) (j : Fin s) :
    tailProduct R j=∏ i ∈ Finset.univ.filter (fun i => j < i), R i := by
  simp only [tailProduct,Finset.prod_filter]

theorem tailProduct_pos {s : ℕ} (R : Fin s → ℝ) (hR : ∀ i, 0 < R i)
    (j : Fin s) : 0 < tailProduct R j := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact hR i
  · exact zero_lt_one

theorem tailProduct_zero {s : ℕ} (R : Fin (s+1) → ℝ) :
    tailProduct R 0 = ∏ i : Fin s, R i.succ := by
  simp [tailProduct,Fin.prod_univ_succ]

theorem tailProduct_succ {s : ℕ} (R : Fin (s+1) → ℝ) (j : Fin s) :
    tailProduct R j.succ=tailProduct (fun i => R i.succ) j := by
  simp [tailProduct,Fin.prod_univ_succ]

/-- Crossing the fixed threshold is enough: no ordering of the scales is
required, and the empty tail is the literal product 1. -/
theorem exists_threshold_pivot (C T : ℝ) (hC : 1 ≤ C) (hT : 1 < T) :
    ∀ (s : ℕ) (R : Fin s → ℝ), (∀ i, 2*C ≤ R i) →
      2*C*T < ∏ i, R i →
      ∃ j : Fin s, tailProduct R j ≤ 2*C*T ∧ 2*C*T ≤ R j*tailProduct R j := by
  intro s
  induction s with
  | zero =>
    intro R hR hprod
    simp only [Fin.prod_univ_zero] at hprod
    nlinarith
  | succ s ih =>
    intro R hR hprod
    by_cases htail : (∏ i : Fin s, R i.succ) ≤ 2*C*T
    · refine ⟨0,?_,?_⟩
      · simpa only [tailProduct_zero] using htail
      · rw [Fin.prod_univ_succ] at hprod
        simpa only [tailProduct_zero] using hprod.le
    · obtain ⟨j,hlo,hhi⟩ := ih (fun i => R i.succ) (fun i => hR i.succ)
        (lt_of_not_ge htail)
      exact ⟨j.succ,by simpa only [tailProduct_succ] using hlo,
        by simpa only [tailProduct_succ] using hhi⟩

/-- The crossing index also meets the exact large-modulus sieve threshold. -/
theorem exists_pivot {s : ℕ} (C T : ℝ) (hC : 1 ≤ C) (hT : 1 < T)
    (R : Fin s → ℝ) (hR : ∀ i, 2*C ≤ R i) (hprod : 2*C*T < ∏ i, R i) :
    ∃ j : Fin s, tailProduct R j ≤ 2*C*T ∧
      2*C*T ≤ R j*tailProduct R j ∧ C*(1+T/tailProduct R j) ≤ R j := by
  obtain ⟨j,hlo,hhi⟩ := exists_threshold_pivot C T hC hT s R hR hprod
  refine ⟨j,hlo,hhi,?_⟩
  have htail : 0 < tailProduct R j :=
    tailProduct_pos R (fun i => lt_of_lt_of_le (by linarith) (hR i)) j
  have hdivide : 2*C*T/tailProduct R j ≤ R j := (div_le_iff₀ htail).mpr hhi
  have he : 2*C*T/tailProduct R j = 2*C*(T/tailProduct R j) := by ring
  rw [he] at hdivide
  nlinarith [hR j]

end CubicTenVariables.StratifiedSieveNumerics
