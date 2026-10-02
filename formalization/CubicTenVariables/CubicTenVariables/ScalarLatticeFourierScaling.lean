import CubicTenVariables.ScalarLatticeSchwartz
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Scalar change of variables for the exact coordinate Fourier integral.
The Jacobian is the reciprocal of `c^n` for the specified product Lebesgue
measure. No Poisson summation statement is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScalarLatticeFourierScaling
open MeasureTheory ScalarLatticePoisson
open scoped BigOperators
variable {n : ℕ}

/-- Positive scalar dilation and the dual frequency have reciprocal scales. -/
theorem fourier_comp_smul (f : (Fin n → ℝ) → ℂ) (c : ℝ) (hc : 0 < c)
    (ξ : Fin n → ℝ) :
    fourier (fun x => f (c • x)) ξ =
      ((c : ℂ)^n)⁻¹ * fourier f (fun i => ξ i / c) := by
  let J : (Fin n → ℝ) → ℂ := fun y => f y * Complex.exp
    (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, (ξ i / c) * y i : ℝ) : ℂ))
  have hkernel (x : Fin n → ℝ) :
      J (c • x) = f (c • x) * Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ)) := by
    have hsum : (∑ i, (ξ i / c) * (c * x i)) = ∑ i, ξ i * x i := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    simpa only [J, Pi.smul_apply, smul_eq_mul, hsum]
  have hs := Measure.integral_comp_smul_of_nonneg volume J c (hR := hc.le)
  rw [Module.finrank_pi, Fintype.card_fin] at hs
  rw [fourier_eq_volume_integral]
  calc
    _ = ∫ x, J (c • x) := integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (hkernel x).symm))
    _ = (c^n)⁻¹ • ∫ x, J x := hs
    _ = _ := by
      rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
      rfl

/-- The Schwartz dilation wrapper has exactly the same Fourier scaling. -/
theorem fourier_affinePullback_zero (f : SchwartzMap (Fin n → ℝ) ℂ)
    (c : ℝ) (hc : 0 < c) (ξ : Fin n → ℝ) :
    fourier (ScalarLatticeSchwartz.affinePullback f c hc 0) ξ =
      ((c : ℂ)^n)⁻¹ * fourier f (fun i => ξ i / c) := by
  have hfun : (ScalarLatticeSchwartz.affinePullback f c hc 0 : (Fin n → ℝ) → ℂ) =
      fun x => f (c • x) := by
    funext x
    simp only [ScalarLatticeSchwartz.affinePullback_apply, zero_add]
  rw [hfun]
  exact fourier_comp_smul f c hc ξ

end CubicTenVariables.ScalarLatticeFourierScaling
