import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-! Exact ten-variable optimization after the integral and shifted-average
bounds. All powers in the saving estimate have real exponents. This module
asserts no bound for an exponential sum or an integral. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.NonzeroFrequencyNumerics

def saving (β : ℝ) : ℝ := min (1/4) β

theorem saving_pos (β : ℝ) (hβ : 0 < β) : 0 < saving β := by
  exact lt_min (by norm_num) hβ

theorem first_term (P R β : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRmax : R ≤ P^((3 : ℝ)/2)) (hβ : 0 < β) :
    R^(-β)*(R/P^((3 : ℝ)/2))^((1 : ℝ)/6) ≤ P^(-saving β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have he : R^(-β)*(R/P^((3 : ℝ)/2))^((1 : ℝ)/6) =
      P^(-((1 : ℝ)/4))*R^((1 : ℝ)/6-β) := by
    rw [Real.div_rpow hR0.le (Real.rpow_nonneg hP0.le _),
      ← Real.rpow_mul hP0.le]
    norm_num
    rw [div_eq_mul_inv,← Real.rpow_neg hP0.le]
    calc
      _ = P^(-((1 : ℝ)/4))*(R^(-β)*R^((1 : ℝ)/6)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hR0, show -β+(1:ℝ)/6=(1:ℝ)/6-β by ring]
  rw [he]
  by_cases hb : (1 : ℝ)/6 ≤ β
  · have hrpow : R^((1 : ℝ)/6-β) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hR (sub_nonpos.mpr hb)
    calc
      _ ≤ P^(-((1 : ℝ)/4))*1 := mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ ≤ P^(-saving β) := by
        rw [mul_one]
        apply Real.rpow_le_rpow_of_exponent_le hP
        have hh : saving β ≤ (1:ℝ)/4 := min_le_left _ _
        linarith
  · have hrpow : R^((1 : ℝ)/6-β) ≤ (P^((3 : ℝ)/2))^((1 : ℝ)/6-β) :=
      Real.rpow_le_rpow hR0.le hRmax (sub_nonneg.mpr (le_of_not_ge hb))
    calc
      _ ≤ P^(-((1 : ℝ)/4))*(P^((3 : ℝ)/2))^((1 : ℝ)/6-β) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = P^(-((3 : ℝ)/2)*β) := by
        rw [← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
        congr 1
        ring
      _ ≤ P^(-saving β) := by
        apply Real.rpow_le_rpow_of_exponent_le hP
        have hh : saving β ≤ β := min_le_right _ _
        linarith

theorem second_term (P R β : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hβ : 0 < β) :
    R^(-β)*(max 1 (P/R))^(-(5 : ℝ)/2) ≤ P^(-saving β) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  by_cases hPR : P ≤ R
  · rw [max_eq_left ((div_le_one hR0).mpr hPR),Real.one_rpow,mul_one]
    exact (Real.rpow_le_rpow_of_nonpos hP0 hPR (neg_nonpos.mpr hβ.le)).trans
      (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg (min_le_right _ _)))
  · have hRP : R ≤ P := le_of_not_ge hPR
    rw [max_eq_right ((one_le_div hR0).mpr hRP)]
    have he : R^(-β)*(P/R)^(-(5 : ℝ)/2) =
        P^(-((5 : ℝ)/2))*R^((5 : ℝ)/2-β) := by
      rw [Real.div_rpow hP0.le hR0.le,div_eq_mul_inv,← Real.rpow_neg hR0.le]
      norm_num
      calc
        _ = P^(-((5 : ℝ)/2))*(R^(-β)*R^((5 : ℝ)/2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hR0, show -β+(5:ℝ)/2=(5:ℝ)/2-β by ring]
    rw [he]
    by_cases hb : (5 : ℝ)/2 ≤ β
    · have hrpow : R^((5 : ℝ)/2-β) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hR (sub_nonpos.mpr hb)
      calc
        _ ≤ P^(-((5 : ℝ)/2))*1 := mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ ≤ P^(-saving β) := by
          rw [mul_one]
          apply Real.rpow_le_rpow_of_exponent_le hP
          have hh : saving β ≤ (1 : ℝ)/4 := min_le_left _ _
          linarith
    · have hrpow : R^((5 : ℝ)/2-β) ≤ P^((5 : ℝ)/2-β) :=
        Real.rpow_le_rpow hR0.le hRP (sub_nonneg.mpr (le_of_not_ge hb))
      calc
        _ ≤ P^(-((5 : ℝ)/2))*P^((5 : ℝ)/2-β) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ = P^(-β) := by rw [← Real.rpow_add hP0]; congr 1; ring
        _ ≤ P^(-saving β) :=
          Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg (min_le_right _ _))

/-- The two endpoints in the n=10 optimization, with rho=7. -/
theorem radial_saving (P R β : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R)
    (hRmax : R ≤ P^((3 : ℝ)/2)) (hβ : 0 < β) :
    R^(-β)*((R/P^((3 : ℝ)/2))^((1 : ℝ)/6)+
      (max 1 (P/R))^(-(5 : ℝ)/2)) ≤ 2*P^(-min (1/4) β) := by
  rw [mul_add]
  have hfirst := first_term P R β hP hR hRmax hβ
  have hsecond := second_term P R β hP hR hβ
  dsimp [saving] at hfirst hsecond
  linarith

/-- Exact identification with the source's three candidate savings. -/
theorem source_saving (b : ℝ) :
    min ((7 : ℝ)/4-3/2) (min ((7 : ℝ)/2-1) (20/3-b)) = saving (20/3-b) := by
  norm_num [saving,← min_assoc]

/-- The natural window radius chosen without any optimization hypothesis. -/
def cubeRootWidth (R : ℝ) : ℕ := ⌈R^((1 : ℝ)/3)⌉₊

theorem cubeRootWidth_bounds (R : ℝ) (hR : 1 ≤ R) :
    R^((1 : ℝ)/3) ≤ (cubeRootWidth R : ℝ) ∧
      (cubeRootWidth R : ℝ) ≤ 2*R^((1 : ℝ)/3) := by
  have hroot : 1 ≤ R^((1 : ℝ)/3) := Real.one_le_rpow hR (by norm_num)
  exact ⟨Nat.le_ceil _, Nat.ceil_le_two_mul (by linarith)⟩

theorem cubeRootWidth_pos (R : ℝ) (hR : 1 ≤ R) : 1 ≤ cubeRootWidth R := by
  have hh : (1 : ℝ) ≤ (cubeRootWidth R : ℝ) :=
    (Real.one_le_rpow hR (by norm_num)).trans (cubeRootWidth_bounds R hR).1
  exact_mod_cast hh

end CubicTenVariables.NonzeroFrequencyNumerics
