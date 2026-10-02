import CubicTenVariables.DeltaMethod
import Mathlib.Data.Nat.Log

/-! Exact boundedness of source arcs and of their finite dyadic scales.
These facts allow the later partition to retain every clipped endpoint. -/
set_option autoImplicit false
namespace CubicTenVariables.CountingArcGeometry
open DeltaMethod

theorem measurableSet_arc (Q q : ℕ) (η : ℝ) : MeasurableSet (arc Q q η) := by
  rw [arc_eq_Ioo]
  exact measurableSet_Ioo

theorem arc_subset_unit (Q q : ℕ) (hQ : 1 ≤ Q) (hq : 1 ≤ q)
    (η : ℝ) (hη : η ≤ 1) : arc Q q η ⊆ Set.Icc (-1:ℝ) 1 := by
  have hbase : (1:ℝ) ≤ (q:ℝ)*(Q:ℝ) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq) (by exact_mod_cast hQ)
  have hb : ((q:ℝ)*(Q:ℝ))^(-1+η) ≤ 1 := by
    calc
      _ ≤ ((q:ℝ)*(Q:ℝ))^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = 1 := Real.rpow_zero _
  intro θ hθ
  exact abs_le.mp ((show |θ| < ((q:ℝ)*(Q:ℝ))^(-1+η) from hθ).le.trans hb)

/-- Every dyadic modulus scale selected by log₂ Q lies between 1 and Q. -/
theorem dyadic_scale_bounds (Q j : ℕ) (hQ : 1 ≤ Q) (hj : j < Nat.log 2 Q+1) :
    1 ≤ (2:ℝ)^j ∧ (2:ℝ)^j ≤ (Q:ℝ) := by
  constructor
  · exact one_le_pow₀ (by norm_num)
  · have hj' : j ≤ Nat.log 2 Q := by omega
    have hb : (2:ℕ)^j ≤ Q :=
      (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hj').trans
        (Nat.pow_log_le_self 2 (by omega))
    exact_mod_cast hb

end CubicTenVariables.CountingArcGeometry
