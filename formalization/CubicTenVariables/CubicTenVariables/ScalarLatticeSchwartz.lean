import CubicTenVariables.SchwartzLatticeSummability
import CubicTenVariables.Literature.ScalarLatticePoisson

/-! Absolute summability on every translated positive scalar lattice, for
the literal coordinate point map in the remaining Poisson statement. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScalarLatticeSchwartz
open scoped SchwartzMap
variable {n : ℕ}

/-- The affine pullback of an actual coordinate Schwartz function. -/
def affinePullback (f : SchwartzMap (Fin n → ℝ) ℂ) (c : ℝ) (hc : 0 < c)
    (a : Fin n → ℝ) : SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.compCLM ℂ
    ((Function.HasTemperateGrowth.const a).add
      ((Function.HasTemperateGrowth.const c).smul
        (ContinuousLinearMap.id ℝ (Fin n → ℝ)).hasTemperateGrowth))
    (by
      refine ⟨1, (‖a‖ + 1) / c, ?_⟩
      intro x
      have hn : c * ‖x‖ ≤ ‖a + c • x‖ + ‖a‖ := by
        simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc] using
          norm_sub_le (a + c • x) a
      calc
        ‖x‖ ≤ (‖a + c • x‖ + ‖a‖) / c := (le_div_iff₀ hc).2 (by nlinarith)
        _ ≤ ((‖a‖ + 1) * (1 + ‖a + c • x‖)) / c :=
          div_le_div_of_nonneg_right (by
            have hp := mul_nonneg (norm_nonneg a) (norm_nonneg (a + c • x))
            nlinarith) hc.le
        _ = (‖a‖ + 1) / c * (1 + ‖a + c • x‖) ^ 1 := by ring) f

@[simp] theorem affinePullback_apply (f : SchwartzMap (Fin n → ℝ) ℂ)
    (c : ℝ) (hc : 0 < c) (a x : Fin n → ℝ) :
    affinePullback f c hc a x = f (a + c • x) := rfl

/-- This is exactly the physical-side summability conclusion of the
scalar-lattice Poisson premise, with no Fourier or Poisson hypothesis. -/
theorem summable_norm_points (f : SchwartzMap (Fin n → ℝ) ℂ)
    (c : ℝ) (hc : 0 < c) (a : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ => ‖f (ScalarLatticePoisson.point c a z)‖) := by
  have hh := SchwartzLatticeSummability.summable_norm_translate (affinePullback f c hc a) 0
  simpa only [zero_add, affinePullback_apply, ScalarLatticePoisson.point, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] using hh

end CubicTenVariables.ScalarLatticeSchwartz
