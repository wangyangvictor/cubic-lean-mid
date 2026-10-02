import CubicTenVariables.ComplementAllocationBound
import CubicTenVariables.ComplementDeepWeights

/-! Comparison of the actual integer allocation with its dyadic scales.
All constants are absolute, and no depth periodicity or arithmetic mean
estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementDyadicWeight
open scoped BigOperators

/-- There are at most five depth indices, and each dyadic enlargement
costs at most 2^6. The empty tails above depth six are included. -/
theorem weight_le (r : ℕ) (hr : 2 ≤ r) (a b : ℕ → ℕ) (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j)
    (ha : ∀ j ∈ Finset.Icc r 6, (a j : ℝ) ≤ 2*A j)
    (hb : ∀ j ∈ Finset.Icc r 6, (b j : ℝ) ≤ 2*B j) :
    ComplementAllocationBound.weight r a b ≤
      (2 : ℝ)^30*ComplementDeepWeights.weight r A B := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc r 6) :
      (a j : ℝ)^(((j : ℝ)-(r : ℝ))/2)*(b j : ℝ)^((j : ℝ)-(r : ℝ)) ≤
        (2 : ℝ)^6*((A j)^(((j : ℝ)-(r : ℝ))/2)*(B j)^((j : ℝ)-(r : ℝ))) := by
    have hrj : (r : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    have hA0 : 0 ≤ A j := zero_le_one.trans (hA j hj)
    have hB0 : 0 ≤ B j := zero_le_one.trans (hB j hj)
    have hp : (2 : ℝ)^(((j : ℝ)-(r : ℝ))/2)*(2 : ℝ)^((j : ℝ)-(r : ℝ)) ≤
        (2 : ℝ)^6 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      calc
        _ ≤ (2 : ℝ)^(6 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = _ := by norm_num
    calc
      _ ≤ (2*A j)^(((j : ℝ)-(r : ℝ))/2)*(2*B j)^((j : ℝ)-(r : ℝ)) :=
        mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) (ha j hj) (by linarith))
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hb j hj) (by linarith))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (by positivity) _)
      _ = ((2 : ℝ)^(((j : ℝ)-(r : ℝ))/2)*(2 : ℝ)^((j : ℝ)-(r : ℝ)))*
          ((A j)^(((j : ℝ)-(r : ℝ))/2)*(B j)^((j : ℝ)-(r : ℝ))) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA0,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp
        (mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _))
  have hcard : (Finset.Icc r 6).card ≤ 5 := by
    calc
      _ ≤ (Finset.Icc 2 6).card := Finset.card_le_card (by
        intro j hj
        exact Finset.mem_Icc.mpr ⟨hr.trans (Finset.mem_Icc.mp hj).1,(Finset.mem_Icc.mp hj).2⟩)
      _ = _ := by decide
  have hweight : 0 ≤ ComplementDeepWeights.weight r A B :=
    Finset.prod_nonneg (fun j hj => mul_nonneg
      (Real.rpow_nonneg (zero_le_one.trans (hA j hj)) _)
      (Real.rpow_nonneg (zero_le_one.trans (hB j hj)) _))
  calc
    _ ≤ ∏ j ∈ Finset.Icc r 6,
        (2 : ℝ)^6*((A j)^(((j : ℝ)-(r : ℝ))/2)*(B j)^((j : ℝ)-(r : ℝ))) :=
      Finset.prod_le_prod (fun j _ => mul_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hterm
    _ = ((2 : ℝ)^6)^((Finset.Icc r 6).card)*ComplementDeepWeights.weight r A B := by
      rw [Finset.prod_mul_distrib,Finset.prod_const]
      rfl
    _ ≤ ((2 : ℝ)^6)^5*ComplementDeepWeights.weight r A B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) hweight
    _ = _ := by norm_num

/-- The lower dyadic endpoints give the lower bound for the actual high
modulus, retaining the square on every square-prime allocation factor. -/
theorem modulus_le (r : ℕ) (a b : ℕ → ℕ) (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 0 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 0 ≤ B j)
    (ha : ∀ j ∈ Finset.Icc r 6, A j ≤ (a j : ℝ))
    (hb : ∀ j ∈ Finset.Icc r 6, B j ≤ (b j : ℝ)) :
    ComplementDeepWeights.modulus r A B ≤
      ((∏ j ∈ Finset.Icc r 6, a j*(b j)^2 : ℕ) : ℝ) := by
  rw [Nat.cast_prod]
  apply Finset.prod_le_prod (fun j hj => mul_nonneg (hA j hj) (sq_nonneg _))
  intro j hj
  push_cast
  exact mul_le_mul (ha j hj) (pow_le_pow_left₀ (hB j hj) (hb j hj) 2)
    (sq_nonneg _) (Nat.cast_nonneg _)

end CubicTenVariables.ComplementDyadicWeight
