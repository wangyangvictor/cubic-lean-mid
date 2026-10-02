import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Elementary dyadic power sums for arbitrary real exponents. All intervals
are closed and their real endpoints need not be integral. -/
noncomputable section
namespace CubicTenVariables.DyadicPowerSum
open scoped BigOperators

/-- Literal natural integers in the closed real interval `[R,2R]`. -/
def interval (R : ℝ) : Finset ℕ :=
  (Finset.range (⌊2*R⌋₊+1)).filter (fun q => R ≤ (q : ℝ))

theorem mem_interval (R : ℝ) (hR : 1 ≤ R) (q : ℕ) :
    q ∈ interval R ↔ R ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*R := by
  simp only [interval,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  constructor
  · intro h
    exact ⟨h.2,(show (q : ℝ) ≤ (⌊2*R⌋₊ : ℝ) by exact_mod_cast h.1).trans
      (Nat.floor_le (by linarith))⟩
  · intro h
    exact ⟨Nat.le_floor h.2,h.1⟩

theorem positive_of_mem_interval (R : ℝ) (hR : 1 ≤ R) (q : ℕ)
    (hq : q ∈ interval R) : 0 < q := by
  have he : (1 : ℝ) ≤ q := hR.trans ((mem_interval R hR q).mp hq).1
  have : 1 ≤ q := by exact_mod_cast he
  omega

/-- A uniform cardinality bound includes both closed endpoints. -/
theorem card_le (R : ℝ) (hR : 1 ≤ R) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, R ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*R) :
    (Q.card : ℝ) ≤ 3*R := by
  have hsub : Q ⊆ Finset.range (⌊2*R⌋₊+1) := by
    intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor (hQ q hq).2))
  have hcard : Q.card ≤ ⌊2*R⌋₊+1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hfloor : (⌊2*R⌋₊ : ℝ) ≤ 2*R := Nat.floor_le (by linarith)
  have hcast : (Q.card : ℝ) ≤ (⌊2*R⌋₊ : ℝ)+1 := by exact_mod_cast hcard
  linarith

/-- Positive exponents use the upper endpoint; negative exponents use the
lower endpoint. The maximum keeps both cases in a single formula. -/
theorem term_le (a R : ℝ) (hR : 1 ≤ R) (q : ℕ)
    (hq : R ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*R) :
    (q : ℝ)^a ≤ (2 : ℝ)^(max a 0)*R^a := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    calc
      _ ≤ (2*R)^a := Real.rpow_le_rpow (Nat.cast_nonneg q) hq.2 ha
      _ = _ := Real.mul_rpow (by norm_num) (zero_le_one.trans hR)
  · rw [max_eq_right (le_of_not_ge ha),Real.rpow_zero,one_mul]
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hR) hq.1 (le_of_not_ge ha)

/-- An explicit bound for any subset of the dyadic interval, for all real a. -/
theorem sum_le (a R : ℝ) (hR : 1 ≤ R) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, R ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*R) :
    (∑ q ∈ Q, (q : ℝ)^a) ≤ (3*(2 : ℝ)^(max a 0))*R^(a+1) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  calc
    _ ≤ ∑ _q ∈ Q, (2 : ℝ)^(max a 0)*R^a :=
      Finset.sum_le_sum (fun q hq => term_le a R hR q (hQ q hq))
    _ = (Q.card : ℝ)*((2 : ℝ)^(max a 0)*R^a) := by simp
    _ ≤ (3*R)*((2 : ℝ)^(max a 0)*R^a) :=
      mul_le_mul_of_nonneg_right (card_le R hR Q hQ)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hR0.le _))
    _ = (3*(2 : ℝ)^(max a 0))*R^(a+1) := by
      rw [Real.rpow_add hR0,Real.rpow_one]
      ring

theorem interval_sum_le (a R : ℝ) (hR : 1 ≤ R) :
    (∑ q ∈ interval R, (q : ℝ)^a) ≤ (3*(2 : ℝ)^(max a 0))*R^(a+1) :=
  sum_le a R hR _ (fun q hq => (mem_interval R hR q).mp hq)

/-- The exact Cartesian product of the literal intervals. -/
def tuples {s : ℕ} (R : Fin s → ℝ) : Finset (Fin s → ℕ) :=
  Fintype.piFinset fun i => interval (R i)

theorem mem_tuples {s : ℕ} (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (q : Fin s → ℕ) :
    q ∈ tuples R ↔ ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i := by
  simp only [tuples,Fintype.mem_piFinset,mem_interval _ (hR _)]

/-- Exact finite factorization, with no constraints or estimates suppressed. -/
theorem sum_tuples_eq {s : ℕ} (a R : Fin s → ℝ) :
    (∑ q ∈ tuples R, ∏ i, (q i : ℝ)^(a i)) =
      ∏ i, ∑ q ∈ interval (R i), (q : ℝ)^(a i) := by
  exact (Finset.prod_univ_sum (fun i => interval (R i)) (fun i q => (q : ℝ)^(a i))).symm

/-- Any finite tuple family is bounded by the independent-coordinate sum.
Additional arithmetic restrictions may therefore be retained in that family. -/
theorem tuple_sum_le {s : ℕ} (a R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (T : Finset (Fin s → ℕ))
    (hT : ∀ q ∈ T, ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) :
    (∑ q ∈ T, ∏ i, (q i : ℝ)^(a i)) ≤
      (∏ i, 3*(2 : ℝ)^(max (a i) 0)) * (∏ i, (R i)^(a i+1)) := by
  have hsub : T ⊆ tuples R := fun q hq => (mem_tuples R hR q).mpr (hT q hq)
  calc
    _ ≤ ∑ q ∈ tuples R, ∏ i, (q i : ℝ)^(a i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun q _ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ∏ i, ∑ q ∈ interval (R i), (q : ℝ)^(a i) := sum_tuples_eq a R
    _ ≤ ∏ i, (3*(2 : ℝ)^(max (a i) 0))*(R i)^(a i+1) :=
      Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg fun q _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun i _ => interval_sum_le (a i) (R i) (hR i))
    _ = _ := Finset.prod_mul_distrib

theorem coefficient_one_le (a : ℝ) : 1 ≤ 3*(2 : ℝ)^(max a 0) := by
  have he : 1 ≤ (2 : ℝ)^(max a 0) := Real.one_le_rpow (by norm_num) (le_max_right _ _)
  linarith

/-- The tuple constant is chosen before every real interval endpoint. -/
theorem exists_tuple_bound {s : ℕ} (a : Fin s → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R : Fin s → ℝ, (∀ i, 1 ≤ R i) →
      ∀ T : Finset (Fin s → ℕ),
      (∀ q ∈ T, ∀ i, R i ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 2*R i) →
      (∑ q ∈ T, ∏ i, (q i : ℝ)^(a i)) ≤ C*(∏ i, (R i)^(a i+1)) :=
  ⟨∏ i,3*(2 : ℝ)^(max (a i) 0),
    by
      have he := Finset.prod_le_prod (s := Finset.univ)
        (f := fun _i : Fin s => (1 : ℝ)) (g := fun i => 3*(2 : ℝ)^(max (a i) 0))
        (fun _ _ => zero_le_one) (fun i _ => coefficient_one_le (a i))
      simpa only [Finset.prod_const_one] using he,
    fun R hR T hT => tuple_sum_le a R hR T hT⟩

end CubicTenVariables.DyadicPowerSum
