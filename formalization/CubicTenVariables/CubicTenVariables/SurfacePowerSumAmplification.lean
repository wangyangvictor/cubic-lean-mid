import CubicTenVariables.ComplexPowerSumGrowth

/-!
# The elementary part of surface point-count amplification

This file concerns literal finite complex power sums.  The two low-degree
families have roots of norm at most `q`.  A bound for the signed error along
all multiples of one positive integer forces the same bound on every root
of the remaining family.  Repeated roots retain their positive multiplicity.
The geometric realization of these families is a separate literature input.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.SurfacePowerSumAmplification

open scoped BigOperators

def error {n₁ n₂ n₃ : ℕ} (q : ℝ)
    (a : Fin n₁ → ℂ) (b : Fin n₂ → ℂ) (c : Fin n₃ → ℂ) (m : ℕ) : ℂ :=
  -(∑ i, a i ^ m) + (∑ i, b i ^ m) - (∑ i, c i ^ m) - (q : ℂ) ^ m

theorem norm_sum_pow_le {n : ℕ} (a : Fin n → ℂ) (q : ℝ)
    (_hq : 0 ≤ q) (ha : ∀ i, ‖a i‖ ≤ q) (m : ℕ) :
    ‖∑ i, a i ^ m‖ ≤ (n : ℝ) * q ^ m := by
  calc
    ‖∑ i, a i ^ m‖ ≤ ∑ i, ‖a i ^ m‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, q ^ m := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (ha i) m
    _ = (n : ℝ) * q ^ m := by simp

theorem norm_low_le {n₁ n₂ : ℕ} (q : ℝ) (hq : 0 ≤ q)
    (a : Fin n₁ → ℂ) (b : Fin n₂ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ q) (hb : ∀ i, ‖b i‖ ≤ q) (m : ℕ) :
    ‖-(∑ i, a i ^ m) + (∑ i, b i ^ m) - (q : ℂ) ^ m‖ ≤
      ((n₁ : ℝ) + n₂ + 1) * q ^ m := by
  have hqpow : ‖(q : ℂ) ^ m‖ = q ^ m := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have htri : ‖-(∑ i, a i ^ m) + (∑ i, b i ^ m)‖ ≤
      ‖∑ i, a i ^ m‖ + ‖∑ i, b i ^ m‖ := by
    simpa only [norm_neg] using (norm_add_le (-(∑ i, a i ^ m)) (∑ i, b i ^ m))
  calc
    ‖-(∑ i, a i ^ m) + (∑ i, b i ^ m) - (q : ℂ) ^ m‖ ≤
        ‖-(∑ i, a i ^ m) + (∑ i, b i ^ m)‖ + ‖(q : ℂ) ^ m‖ := norm_sub_le _ _
    _ ≤ (‖∑ i, a i ^ m‖ + ‖∑ i, b i ^ m‖) + q ^ m := by
      rw [hqpow]
      exact add_le_add htri le_rfl
    _ ≤ ((n₁ : ℝ) * q ^ m + (n₂ : ℝ) * q ^ m) + q ^ m := by
      exact add_le_add (add_le_add
        (norm_sum_pow_le a q hq ha m) (norm_sum_pow_le b q hq hb m)) le_rfl
    _ = ((n₁ : ℝ) + n₂ + 1) * q ^ m := by ring

/-- An extension-degree error bound rules out all large roots in the only
remaining signed family.  No semisimplicity or distinct-root hypothesis is
used. -/
theorem high_roots_norm_le {n₁ n₂ n₃ : ℕ} (q : ℝ) (hq : 0 < q)
    (a : Fin n₁ → ℂ) (b : Fin n₂ → ℂ) (c : Fin n₃ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ q) (hb : ∀ i, ‖b i‖ ≤ q)
    (d : ℕ) (hd : 1 ≤ d) (C : ℝ)
    (hbound : ∀ m : ℕ, 1 ≤ m → ‖error q a b c (d * m)‖ ≤ C * (q ^ d) ^ m) :
    ∀ i, ‖c i‖ ≤ q := by
  have hsum : ∀ m : ℕ, 1 ≤ m →
      ‖∑ i, c i ^ (d * m)‖ ≤
        (((n₁ : ℝ) + n₂ + 1) + C) * (q ^ d) ^ m := by
    intro m hm
    have heq : (∑ i, c i ^ (d * m)) =
        (-(∑ i, a i ^ (d * m)) + (∑ i, b i ^ (d * m)) - (q : ℂ) ^ (d * m)) -
          error q a b c (d * m) := by
      unfold error
      ring
    rw [heq]
    calc
      _ ≤ ‖-(∑ i, a i ^ (d * m)) + (∑ i, b i ^ (d * m)) - (q : ℂ) ^ (d * m)‖ +
          ‖error q a b c (d * m)‖ := norm_sub_le _ _
      _ ≤ ((n₁ : ℝ) + n₂ + 1) * q ^ (d * m) + C * (q ^ d) ^ m :=
        add_le_add (norm_low_le q hq.le a b ha hb _) (hbound m hm)
      _ = (((n₁ : ℝ) + n₂ + 1) + C) * (q ^ d) ^ m := by
        rw [pow_mul]
        ring
  have h := ComplexPowerSumGrowth.norm_le_of_power_sum_multiples_bound
    Finset.univ c hq d hd (by simpa using hsum)
  intro i
  exact h i (Finset.mem_univ i)

/-- The full error is bounded uniformly at every extension degree after
amplification.  The initial bound and the extension degree disappear from
the resulting constant. -/
theorem error_bound {n₁ n₂ n₃ : ℕ} (q : ℝ) (hq : 0 < q)
    (a : Fin n₁ → ℂ) (b : Fin n₂ → ℂ) (c : Fin n₃ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ q) (hb : ∀ i, ‖b i‖ ≤ q)
    (d : ℕ) (hd : 1 ≤ d) (C : ℝ)
    (hbound : ∀ m : ℕ, 1 ≤ m → ‖error q a b c (d * m)‖ ≤ C * (q ^ d) ^ m)
    (m : ℕ) :
    ‖error q a b c m‖ ≤ ((n₁ : ℝ) + n₂ + n₃ + 1) * q ^ m := by
  have hc := high_roots_norm_le q hq a b c ha hb d hd C hbound
  have heq : error q a b c m =
      (-(∑ i, a i ^ m) + (∑ i, b i ^ m) - (q : ℂ) ^ m) - ∑ i, c i ^ m := by
    unfold error
    ring
  rw [heq]
  calc
    _ ≤ ‖-(∑ i, a i ^ m) + (∑ i, b i ^ m) - (q : ℂ) ^ m‖ +
        ‖∑ i, c i ^ m‖ := norm_sub_le _ _
    _ ≤ ((n₁ : ℝ) + n₂ + 1) * q ^ m + (n₃ : ℝ) * q ^ m :=
      add_le_add (norm_low_le q hq.le a b ha hb m) (norm_sum_pow_le c q hq.le hc m)
    _ = ((n₁ : ℝ) + n₂ + n₃ + 1) * q ^ m := by ring

end CubicTenVariables.SurfacePowerSumAmplification
