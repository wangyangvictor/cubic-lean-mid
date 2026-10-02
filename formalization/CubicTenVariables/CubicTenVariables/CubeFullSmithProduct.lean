import CubicTenVariables.CubeFullSmithParameters

/-! Exact real-power assembly of the selected cube-full local Smith savings. -/

noncomputable section
namespace CubicTenVariables.CubeFullSmithProduct
open CubeFullSmithParameters SmithProfileNumerics
open scoped BigOperators

theorem prod_factorization_rpow (r : ℕ) (hr : 0 < r) (u : ℝ) :
    (∏ p ∈ r.primeFactors, (p : ℝ)^((r.factorization p : ℝ)*u)) = (r : ℝ)^u := by
  calc
    _ = ∏ p ∈ r.primeFactors, ((p : ℝ)^(r.factorization p))^u := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    _ = (∏ p ∈ r.primeFactors, (p : ℝ)^(r.factorization p))^u :=
      Real.finset_prod_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) u
    _ = (r : ℝ)^u := by
      congr 1
      have h : (∏ p ∈ r.primeFactors, p^(r.factorization p)) = r := by
        simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
          Nat.factorization_prod_pow_eq_self hr.ne'
      exact_mod_cast h

theorem prod_residue_class_rpow (r i : ℕ) (u : ℝ) :
    (∏ p ∈ r.primeFactors, if r.factorization p % 3 = i then (p : ℝ)^u else 1) =
      (z r i : ℝ)^u := by
  rw [← Finset.prod_filter]
  rw [Real.finset_prod_rpow _ _ (fun p _ => Nat.cast_nonneg p) u]
  congr 1
  simp only [z, Nat.cast_prod]

private theorem local_factor_eq (r p : ℕ) (hp : p ∈ r.primeFactors) :
    (p : ℝ)^(10*(r.factorization p : ℝ) - (if r.factorization p % 3 = 0 then 2 else 0) -
      (if r.factorization p % 3 = 1 then 4 else 0) -
      (if r.factorization p % 3 = 2 then 1 else 0)) =
    (p : ℝ)^((r.factorization p : ℝ)*10) *
      (if r.factorization p % 3 = 0 then (p : ℝ)^(-2 : ℝ) else 1) *
      (if r.factorization p % 3 = 1 then (p : ℝ)^(-4 : ℝ) else 1) *
      (if r.factorization p % 3 = 2 then (p : ℝ)^(-1 : ℝ) else 1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hm := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 3)
  interval_cases hy : r.factorization p % 3
  all_goals simp only [Nat.reduceEqDiff, ↓reduceIte, sub_zero, mul_one]
  all_goals rw [← Real.rpow_add hp0]
  all_goals congr 1; ring

/-- Exact primewise savings identity; no cube-fullness is needed for this algebra. -/
theorem prod_saving_eq (r : ℕ) (hr : 0 < r) :
    (∏ p ∈ r.primeFactors,
      (p : ℝ)^(10*(r.factorization p : ℝ) - (if r.factorization p % 3 = 0 then 2 else 0) -
        (if r.factorization p % 3 = 1 then 4 else 0) -
        (if r.factorization p % 3 = 2 then 1 else 0))) =
      (r : ℝ)^10 * (z r 0 : ℝ)^(-2 : ℝ) *
        (z r 1 : ℝ)^(-4 : ℝ) * (z r 2 : ℝ)^(-1 : ℝ) := by
  calc
    _ = ∏ p ∈ r.primeFactors,
        (p : ℝ)^((r.factorization p : ℝ)*10) *
          (if r.factorization p % 3 = 0 then (p : ℝ)^(-2 : ℝ) else 1) *
          (if r.factorization p % 3 = 1 then (p : ℝ)^(-4 : ℝ) else 1) *
          (if r.factorization p % 3 = 2 then (p : ℝ)^(-1 : ℝ) else 1) :=
      Finset.prod_congr rfl (fun p hp => local_factor_eq r p hp)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, prod_factorization_rpow r hr,
        prod_residue_class_rpow]
      norm_num

/-- The literal product comparison used in the selected n=10 cube-full route.
All real powers retain negative savings; there is no truncated subtraction. -/
theorem prod_localD_le (r : ℕ) (hr : 0 < r) (hc : CubeFull r) :
    (∏ p ∈ r.primeFactors,
      (p : ℝ)^(localD ((A r).factorization p) ((T r).factorization p) : ℝ)) ≤
      (r : ℝ)^10 * (z r 0 : ℝ)^(-2 : ℝ) *
        (z r 1 : ℝ)^(-4 : ℝ) * (z r 2 : ℝ)^(-1 : ℝ) := by
  rw [← prod_saving_eq r hr]
  apply Finset.prod_le_prod
  · intro p _hp
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  · intro p hp
    apply Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ p by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    exact_mod_cast localD_le r hc p hp

/-- Both prime-power parameter products use the original support. -/
theorem prod_A_factorization_rpow (r : ℕ) (hc : CubeFull r) (u : ℝ) :
    (∏ p ∈ r.primeFactors, (p : ℝ)^(((A r).factorization p : ℝ)*u)) = (A r : ℝ)^u := by
  rw [← primeFactors_A r hc]
  exact prod_factorization_rpow (A r) (A_pos r) u

theorem prod_T_factorization_rpow (r : ℕ) (hc : CubeFull r) (u : ℝ) :
    (∏ p ∈ r.primeFactors, (p : ℝ)^(((T r).factorization p : ℝ)*u)) = (T r : ℝ)^u := by
  rw [← primeFactors_T r hc]
  exact prod_factorization_rpow (T r) (T_pos r) u

/-- The local epsilon loss A^(2*epsilon) is bounded by r^epsilon. -/
theorem A_rpow_two_mul_le (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 ≤ ε) :
    (A r : ℝ)^(2*ε) ≤ (r : ℝ)^ε := by
  have hAr : A r ^ 2 ≤ r := Nat.le_of_dvd hr (A_sq_dvd_r r hr)
  have hArR : (A r : ℝ)^2 ≤ (r : ℝ) := by exact_mod_cast hAr
  rw [Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two]
  exact Real.rpow_le_rpow (by positivity) (by nlinarith [hArR]) hε

end CubicTenVariables.CubeFullSmithProduct
