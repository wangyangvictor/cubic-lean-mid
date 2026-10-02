import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact real-power comparisons for the required modulus average. -/

namespace CubicTenVariables.OnionAverageExponents

/-- Replacing one positive modulus by the common upper limit preserves
both source factors. -/
theorem single_factor_le (r X V ε : ℝ) (hr : 0 ≤ r) (hrX : r ≤ X)
    (hV : 0 ≤ V) (hε : 0 ≤ ε) :
    r^(6+ε)*(V+r^((1:ℝ)/3))^10 ≤
      X^(6+ε)*(V+X^((1:ℝ)/3))^10 := by
  have hX : 0 ≤ X := hr.trans hrX
  apply mul_le_mul (Real.rpow_le_rpow hr hrX (by positivity))
    (pow_le_pow_left₀ (by positivity)
      (add_le_add (le_refl V) (Real.rpow_le_rpow hr hrX (by norm_num : 0 ≤ (1:ℝ)/3))) 10)
    (by positivity) (Real.rpow_nonneg hX _)

/-- Splitting epsilon between the pointwise bound and the parameter sum
recovers exactly the exponent 13/2+epsilon. -/
theorem combined_exponents (C U X V ε : ℝ) (hX : 0 < X) :
    (C*X^(6+ε/2)*(V+X^((1:ℝ)/3))^10)*
      (U*X^((1:ℝ)/2+ε/2)) =
        (C*U)*X^((13:ℝ)/2+ε)*(V+X^((1:ℝ)/3))^10 := by
  have he : X^(6+ε/2)*X^((1:ℝ)/2+ε/2)=X^((13:ℝ)/2+ε) := by
    rw [← Real.rpow_add hX]
    congr 1
    ring
  calc
    _ = (C*U)*(X^(6+ε/2)*X^((1:ℝ)/2+ε/2))*(V+X^((1:ℝ)/3))^10 := by ring
    _ = _ := by rw [he]

/-- The dyadic interval r<=2R costs only a uniform constant. -/
theorem dyadic_factor_le (R V ε : ℝ) (hR : 0 < R) (hV : 0 ≤ V) :
    (2*R)^((13:ℝ)/2+ε)*(V+(2*R)^((1:ℝ)/3))^10 ≤
      ((2:ℝ)^((13:ℝ)/2+ε)*2^10)*R^((13:ℝ)/2+ε)*
        (V+R^((1:ℝ)/3))^10 := by
  have htwo : (2:ℝ)^((1:ℝ)/3) ≤ 2 := by
    calc
      _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hroot : (2*R)^((1:ℝ)/3) ≤ 2*R^((1:ℝ)/3) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hR.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hR.le _)
  have hbox : (V+(2*R)^((1:ℝ)/3))^10 ≤ (2*(V+R^((1:ℝ)/3)))^10 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 10
  calc
    _ ≤ (2*R)^((13:ℝ)/2+ε)*(2*(V+R^((1:ℝ)/3)))^10 :=
      mul_le_mul_of_nonneg_left hbox (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hR.le, mul_pow]
      ring

end CubicTenVariables.OnionAverageExponents
