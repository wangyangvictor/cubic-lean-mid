import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Weighted row and column divisibility of determinants

The local determinant method ultimately arranges columns in increasing
p-adic order.  The elementary final step is that a factor `p^(w_j)` from
column `j` contributes the sum of the weights to the determinant valuation.
This file proves that statement directly from the determinant scaling
identity.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

universe u

/-- If every entry in row `i` is divisible by `c i`, the product of all
`c i` divides the determinant. -/
theorem prod_dvd_det_of_rows_dvd
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (c : ι → ℤ)
    (h : ∀ i j, c i ∣ A i j) :
    (∏ i, c i) ∣ A.det := by
  classical
  let B : Matrix ι ι ℤ := fun i j ↦ Classical.choose (h i j)
  have hA : A = Matrix.of (fun i j ↦ c i * B i j) := by
    ext i j
    exact Classical.choose_spec (h i j)
  rw [hA, Matrix.det_mul_column]
  exact dvd_mul_right _ _

/-- Column form of `prod_dvd_det_of_rows_dvd`. -/
theorem prod_dvd_det_of_columns_dvd
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (c : ι → ℤ)
    (h : ∀ i j, c j ∣ A i j) :
    (∏ j, c j) ∣ A.det := by
  have ht : ∀ j i, c j ∣ A.transpose j i := fun j i ↦ h i j
  have hd := prod_dvd_det_of_rows_dvd A.transpose c ht
  rwa [Matrix.det_transpose] at hd

/-- Weighted prime-power column divisibility contributes the sum of the
weights to the determinant valuation. -/
theorem pow_sum_dvd_det_of_columns_pow_dvd
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (p : ℤ) (w : ι → ℕ)
    (h : ∀ i j, p ^ w j ∣ A i j) :
    p ^ (∑ j, w j) ∣ A.det := by
  have hd := prod_dvd_det_of_columns_dvd A (fun j ↦ p ^ w j) h
  simpa only [← Finset.prod_pow_eq_pow_sum Finset.univ w p] using hd

end

end TranslatedDepthSeven
