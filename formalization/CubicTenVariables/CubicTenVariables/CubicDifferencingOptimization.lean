import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! The literal cube-root choice of the integer differencing radius.
Only the displayed numerical box inequality is assumed here. -/

set_option autoImplicit false
namespace CubicTenVariables.CubicDifferencingOptimization

/-- Choosing `B = floor(q^(1/3))` in the ten-variable box inequality
gives the epsilon-free exponent `25/3 = 5*10/6`. -/
theorem bound_of_box_inequality {q A S : ℝ} (hq : 1 ≤ q) (hA : 1 ≤ A)
    (hS : 0 ≤ S)
    (hbox : ∀ B : ℕ, 1 ≤ B →
      ((B : ℝ)+1)^10 * S^2 ≤ A*q^15*(q+(B : ℝ)^3)^5) :
    S ≤ (32*A+1) * q^(25/3 : ℝ) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  let R : ℝ := q^(1/3 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow hq (by norm_num)
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hR3 : R^3 = q := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hq0.le]
    norm_num
  have hB : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff R).mpr hR
  have hBR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0.le
  have hRB : R ≤ (⌊R⌋₊ : ℝ)+1 := (Nat.lt_floor_add_one R).le
  have hB3 : (⌊R⌋₊ : ℝ)^3 ≤ q :=
    (pow_le_pow_left₀ (by positivity) hBR 3).trans_eq hR3
  have hstep : R^10 * S^2 ≤ (32*A) * q^20 := by
    calc
      _ ≤ ((⌊R⌋₊ : ℝ)+1)^10 * S^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR0.le hRB 10) (sq_nonneg S)
      _ ≤ A*q^15*(q+(⌊R⌋₊ : ℝ)^3)^5 := hbox _ hB
      _ ≤ A*q^15*(2*q)^5 := by
        gcongr
        linarith
      _ = _ := by ring
  have hpower : R^10 * q^(50/3 : ℝ) = q^20 := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast hq0.le, ← Real.rpow_add hq0]
    norm_num
  have hsq : S^2 ≤ (32*A) * q^(50/3 : ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hR0 10)).mp
    calc
      _ ≤ (32*A) * q^20 := hstep
      _ = _ := by rw [← hpower]; ring
  have hC : 32*A ≤ (32*A+1)^2 := by nlinarith [sq_nonneg (32*A)]
  have htarget : 0 ≤ (32*A+1)*q^(25/3 : ℝ) := by positivity
  apply (sq_le_sq₀ hS htarget).mp
  calc
    _ ≤ (32*A)*q^(50/3 : ℝ) := hsq
    _ ≤ (32*A+1)^2*q^(50/3 : ℝ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hq0.le _)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hq0.le]
      norm_num

end CubicTenVariables.CubicDifferencingOptimization
