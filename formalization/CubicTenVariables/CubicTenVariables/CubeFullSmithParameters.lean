import CubicTenVariables.SmithProfileBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! The literal cube-full parameters in the selected ten-variable Smith route. -/

noncomputable section
namespace CubicTenVariables.CubeFullSmithParameters
open scoped BigOperators

/-- Every occurring prime has exponent at least three. Positivity is stated separately. -/
def CubeFull (r : ℕ) : Prop := ∀ p ∈ r.primeFactors, 3 ≤ r.factorization p

def b (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors, p^(r.factorization p / 3)
def z (r i : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => r.factorization p % 3 = i), p
def A (r : ℕ) : ℕ := b r * z r 2
def T (r : ℕ) : ℕ := b r * z r 1

theorem b_pos (r : ℕ) : 0 < b r :=
  Finset.prod_pos (fun _p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

theorem z_pos (r i : ℕ) : 0 < z r i :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

theorem A_pos (r : ℕ) : 0 < A r := Nat.mul_pos (b_pos r) (z_pos r 2)
theorem T_pos (r : ℕ) : 0 < T r := Nat.mul_pos (b_pos r) (z_pos r 1)

@[simp] theorem b_one : b 1 = 1 := by simp [b]
@[simp] theorem z_one (i : ℕ) : z 1 i = 1 := by simp [z]
@[simp] theorem A_one : A 1 = 1 := by simp [A]
@[simp] theorem T_one : T 1 = 1 := by simp [T]

theorem factorization_prime_power_prod (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime) (f : ℕ → ℕ) (p : ℕ) :
    (∏ q ∈ s, q^(f q)).factorization p = if p ∈ s then f p else 0 := by
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hs q hq).ne_zero)]
  calc
    (∑ q ∈ s, (q^(f q)).factorization p) = ∑ q ∈ s, if q = p then f q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(hs q hq).factorization_pow]
      simp only [Finsupp.single_apply, eq_comm]
    _ = _ := by simp

theorem factorization_b (r p : ℕ) : (b r).factorization p = r.factorization p / 3 := by
  rw [b, factorization_prime_power_prod _ (fun q hq => Nat.prime_of_mem_primeFactors hq)]
  by_cases hp : p ∈ r.primeFactors
  · simp [hp]
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp, hz]

theorem factorization_z (r i p : ℕ) :
    (z r i).factorization p = if p ∈ r.primeFactors ∧ r.factorization p % 3 = i then 1 else 0 := by
  unfold z
  have h := factorization_prime_power_prod
    (r.primeFactors.filter (fun q => r.factorization q % 3 = i))
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1) (fun _ => 1) p
  simpa only [pow_one, Finset.mem_filter] using h

theorem factorization_A (r p : ℕ) :
    (A r).factorization p = r.factorization p / 3 +
      if p ∈ r.primeFactors ∧ r.factorization p % 3 = 2 then 1 else 0 := by
  rw [A, Nat.factorization_mul (b_pos r).ne' (z_pos r 2).ne', Finsupp.add_apply,
    factorization_b, factorization_z]

theorem factorization_T (r p : ℕ) :
    (T r).factorization p = r.factorization p / 3 +
      if p ∈ r.primeFactors ∧ r.factorization p % 3 = 1 then 1 else 0 := by
  rw [T, Nat.factorization_mul (b_pos r).ne' (z_pos r 1).ne', Finsupp.add_apply,
    factorization_b, factorization_z]

theorem factorization_A_of_mem (r p : ℕ) (hp : p ∈ r.primeFactors) :
    (A r).factorization p = r.factorization p / 3 +
      if r.factorization p % 3 = 2 then 1 else 0 := by simp [factorization_A, hp]

theorem factorization_T_of_mem (r p : ℕ) (hp : p ∈ r.primeFactors) :
    (T r).factorization p = r.factorization p / 3 +
      if r.factorization p % 3 = 1 then 1 else 0 := by simp [factorization_T, hp]

/-- The defining product decomposition holds even without cube-fullness. -/
theorem eq_b_cube_z (r : ℕ) (hr : 0 < r) : r = b r ^ 3 * z r 1 * z r 2 ^ 2 := by
  have hb := b_pos r
  have hz1 := z_pos r 1
  have hz2 := z_pos r 2
  apply Nat.eq_of_factorization_eq hr.ne' (by positivity)
  intro p
  rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.factorization_mul (by positivity) (z_pos r 1).ne', Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, smul_eq_mul, factorization_b, factorization_z, factorization_z]
  by_cases hp : p ∈ r.primeFactors
  · simp only [hp, true_and]
    have hmod := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 3)
    have hdiv := Nat.mod_add_div (r.factorization p) 3
    interval_cases h : r.factorization p % 3 <;> simp <;> omega
  · have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hp, hz]

theorem eq_A_sq_mul_T (r : ℕ) (hr : 0 < r) : r = A r ^ 2 * T r := by
  calc
    r = b r ^ 3 * z r 1 * z r 2 ^ 2 := eq_b_cube_z r hr
    _ = A r ^ 2 * T r := by unfold A T; ring

theorem quotient_pos_of_mem (r : ℕ) (hc : CubeFull r) (p : ℕ)
    (hp : p ∈ r.primeFactors) : 1 ≤ r.factorization p / 3 := by
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by simpa using hc p hp)

theorem primeFactors_b (r : ℕ) (hc : CubeFull r) : (b r).primeFactors = r.primeFactors := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_b]
  constructor
  · intro hp
    by_contra hn
    have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hz] at hp
  · intro hp
    exact Nat.ne_of_gt (quotient_pos_of_mem r hc p hp)

theorem primeFactors_A (r : ℕ) (hc : CubeFull r) : (A r).primeFactors = r.primeFactors := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_A]
  constructor
  · intro hp
    by_contra hn
    have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hn, hz] at hp
  · intro hp
    have h := quotient_pos_of_mem r hc p hp
    omega

theorem primeFactors_T (r : ℕ) (hc : CubeFull r) : (T r).primeFactors = r.primeFactors := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_T]
  constructor
  · intro hp
    by_contra hn
    have hz : r.factorization p = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hn, hz] at hp
  · intro hp
    have h := quotient_pos_of_mem r hc p hp
    omega

/-- Radicals are literally products of the same prime supports. -/
theorem radical_A_eq (r : ℕ) (hc : CubeFull r) :
    (∏ p ∈ (A r).primeFactors, p) = ∏ p ∈ r.primeFactors, p := by rw [primeFactors_A r hc]

/-- The three residue-class prime factors partition the prime support. -/
theorem z_product_eq_radical (r : ℕ) :
    z r 0 * z r 1 * z r 2 = ∏ p ∈ r.primeFactors, p := by
  unfold z
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  have hmod := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 3)
  interval_cases h : r.factorization p % 3 <;> simp

theorem z_product_dvd_b (r : ℕ) (hc : CubeFull r) :
    z r 0 * z r 1 * z r 2 ∣ b r := by
  rw [z_product_eq_radical, ← primeFactors_b r hc]
  exact Nat.prod_primeFactors_dvd _

theorem A_sq_dvd_r (r : ℕ) (hr : 0 < r) : A r ^ 2 ∣ r :=
  ⟨T r, eq_A_sq_mul_T r hr⟩

theorem T_dvd_r (r : ℕ) (hr : 0 < r) : T r ∣ r :=
  ⟨A r ^ 2, (eq_A_sq_mul_T r hr).trans (Nat.mul_comm _ _)⟩

/-- The three local estimates specialize to exactly the source's savings. -/
theorem localD_le (r : ℕ) (hc : CubeFull r) (p : ℕ) (hp : p ∈ r.primeFactors) :
    SmithProfileNumerics.localD ((A r).factorization p) ((T r).factorization p) ≤
      10*(r.factorization p : ℚ) - (if r.factorization p % 3 = 0 then 2 else 0) -
        (if r.factorization p % 3 = 1 then 4 else 0) -
        (if r.factorization p % 3 = 2 then 1 else 0) := by
  rw [factorization_A_of_mem r p hp, factorization_T_of_mem r p hp]
  have he := quotient_pos_of_mem r hc p hp
  have hm := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 3)
  have hdiv := Nat.mod_add_div (r.factorization p) 3
  have hd : (r.factorization p : ℚ) = 3*(r.factorization p / 3 : ℕ) +
      (r.factorization p % 3 : ℕ) := by
    exact_mod_cast (show r.factorization p = 3*(r.factorization p / 3) +
      r.factorization p % 3 by omega)
  interval_cases hy : r.factorization p % 3
  · simp only [↓reduceIte, Nat.reduceEqDiff, add_zero]
    have h := SmithProfileBounds.localD_diag_le _ he
    norm_num at hd
    linarith
  · simp only [↓reduceIte, Nat.reduceEqDiff, add_zero]
    have h := SmithProfileBounds.localD_up_le _ he
    norm_num at hd
    linarith
  · simp only [↓reduceIte, Nat.reduceEqDiff, add_zero]
    have h := SmithProfileBounds.localD_down_le _ he
    norm_num at hd
    linarith

end CubicTenVariables.CubeFullSmithParameters
