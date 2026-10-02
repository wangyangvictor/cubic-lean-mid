import CubicTenVariables.SpherePackingCoordinatePoisson
import CubicTenVariables.ScalarLatticeFourierScaling
import CubicTenVariables.ScalarLatticeAbsoluteConvergence

/-! The complete scalar-lattice Poisson proposition, proved from the reused
multidimensional standard-lattice theorem and scalar change of variables.
The identity, both absolute-convergence assertions, shift sign, covolume,
and product coordinate Lebesgue measure match the original interface. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScalarLatticePoissonProved
open ScalarLatticePoisson
open scoped BigOperators
variable {n : ℕ}

/-- Scaling the translated unit lattice gives the exact scalar-lattice
identity, including the zero-dimensional case. -/
theorem identity (f : SchwartzMap (Fin n → ℝ) ℂ) (c : ℝ) (hc : 0 < c)
    (a : Fin n → ℝ) :
    (∑' z : Fin n → ℤ, f (point c a z)) =
      ((c : ℂ)^n)⁻¹ * ∑' v : Fin n → ℤ,
        phase c a v * fourier f (fun i => (v i : ℝ)/c) := by
  let g := ScalarLatticeSchwartz.affinePullback f c hc 0
  let x : Fin n → ℝ := fun i => a i / c
  have hp (z : Fin n → ℤ) : g (x + fun i => (z i : ℝ)) = f (point c a z) := by
    simp only [g, ScalarLatticeSchwartz.affinePullback_apply, zero_add]
    congr 1
    funext i
    simp only [x, point, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
  have hphase (v : Fin n → ℤ) : phase 1 x v = phase c a v := by
    unfold phase
    congr 2
    simp only [div_one, x]
    congr 1
    simp only [mul_div_assoc, Finset.sum_div]
  calc
    _ = ∑' z : Fin n → ℤ, g (x + fun i => (z i : ℝ)) := by simp_rw [hp]
    _ = ∑' v : Fin n → ℤ, phase 1 x v * fourier g (fun i => (v i : ℝ)) :=
      SpherePackingCoordinatePoisson.standard g x
    _ = ∑' v : Fin n → ℤ,
        ((c : ℂ)^n)⁻¹ * (phase c a v * fourier f (fun i => (v i : ℝ)/c)) := by
      apply tsum_congr
      intro v
      rw [hphase, ScalarLatticeFourierScaling.fourier_affinePullback_zero]
      ring
    _ = _ := tsum_mul_left

/-- An unconditional inhabitant of the exact previously assumed statement. -/
theorem proved : Literature.SteinShakarchi2011Poisson := by
  intro n f c hc a
  obtain ⟨hphysical, hdual⟩ := ScalarLatticeAbsoluteConvergence.absolute_convergence f c hc a
  exact ⟨hphysical, hdual, identity f c hc a⟩

end CubicTenVariables.ScalarLatticePoissonProved
