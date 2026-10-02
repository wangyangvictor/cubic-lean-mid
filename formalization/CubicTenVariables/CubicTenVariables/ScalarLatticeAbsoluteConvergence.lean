import CubicTenVariables.ScalarLatticeSchwartz
import CubicTenVariables.CoordinateFourierSchwartz

/-! Both absolute-convergence conclusions of the literal scalar-lattice
Poisson statement. The equality of the two sums is a separate obligation. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScalarLatticeAbsoluteConvergence
open ScalarLatticePoisson
variable {n : ℕ}

/-- The dual-lattice Fourier values are absolutely summable with the exact
coordinate measure and frequency scaling of the manuscript. -/
theorem summable_norm_fourier (f : SchwartzMap (Fin n → ℝ) ℂ)
    (c : ℝ) (hc : 0 < c) :
    Summable (fun v : Fin n → ℤ => ‖fourier f (fun i => (v i : ℝ) / c)‖) := by
  have hh := ScalarLatticeSchwartz.summable_norm_points
    (CoordinateFourierSchwartz.transform f) c⁻¹ (inv_pos.mpr hc) 0
  simp only [CoordinateFourierSchwartz.transform_apply] at hh
  change Summable (fun z : Fin n → ℤ =>
    ‖fourier f (fun i => (0 : ℝ) + c⁻¹ * (z i : ℝ))‖) at hh
  simpa only [zero_add, div_eq_mul_inv, mul_comm] using hh

/-- Both required summability statements hold without a Poisson input. -/
theorem absolute_convergence (f : SchwartzMap (Fin n → ℝ) ℂ)
    (c : ℝ) (hc : 0 < c) (a : Fin n → ℝ) :
    Summable (fun z : Fin n → ℤ => ‖f (point c a z)‖) ∧
      Summable (fun v : Fin n → ℤ => ‖fourier f (fun i => (v i : ℝ) / c)‖) :=
  ⟨ScalarLatticeSchwartz.summable_norm_points f c hc a, summable_norm_fourier f c hc⟩

end CubicTenVariables.ScalarLatticeAbsoluteConvergence
