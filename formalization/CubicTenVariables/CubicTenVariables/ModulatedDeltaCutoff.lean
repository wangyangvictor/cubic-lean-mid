import CubicTenVariables.SmoothDeltaNormalization

/-! The literal negative-frequency modulation of the fixed delta cutoff.
This family will supply the near-one Fourier estimate by Poisson summation. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ModulatedDeltaCutoff
open MeasureTheory SmoothDeltaCutoffs
open scoped BigOperators ContDiff FourierTransform SchwartzMap

def modulated (t y : ℝ) : ℂ :=
  (U y : ℂ)*Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((y*t : ℝ) : ℂ))

theorem modulated_contDiff (t : ℝ) : ContDiff ℝ ∞ (modulated t) := by
  unfold modulated
  apply (Complex.ofRealCLM.contDiff.comp U_contDiff).mul
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (contDiff_id.mul contDiff_const))).cexp

theorem modulated_hasCompactSupport (t : ℝ) : HasCompactSupport (modulated t) :=
  (U_hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)).mul_right

def schwartz (t : ℝ) : 𝓢(ℝ,ℂ) :=
  (modulated_hasCompactSupport t).toSchwartzMap (modulated_contDiff t)

@[simp] theorem schwartz_apply (t y : ℝ) : schwartz t y = modulated t y := rfl

@[simp] theorem modulated_zero (y : ℝ) : modulated 0 y = (U y : ℂ) := by
  simp [modulated]

@[simp] theorem modulated_at_zero (t : ℝ) : modulated t 0 = 1 := by
  simp [modulated]

theorem norm_modulated (t y : ℝ) : ‖modulated t y‖ = |U y| := by
  have he : Complex.exp (-2*(Real.pi : ℂ)*Complex.I*((y*t : ℝ) : ℂ)) =
      DeltaMethod.realExponential (-(y*t)) := by
    unfold DeltaMethod.realExponential
    congr 1
    push_cast
    ring
  simp only [modulated,norm_mul,he,DeltaMethod.norm_realExponential,mul_one,
    Complex.norm_real,Real.norm_eq_abs]

/-- Negative modulation shifts the negative-sign Fourier transform by `+t`. -/
theorem fourier_shift (t ξ : ℝ) : (𝓕 (schwartz t)) ξ = (𝓕 (schwartz 0)) (ξ+t) := by
  change 𝓕 (modulated t) ξ = 𝓕 (modulated 0) (ξ+t)
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul,modulated, mul_zero,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,mul_one]
  have he : Complex.exp (Complex.ofReal (-2*Real.pi*y*ξ)*Complex.I) *
      Complex.exp (-2*(Real.pi : ℂ)*Complex.I*Complex.ofReal (y*t)) =
      Complex.exp (Complex.ofReal (-2*Real.pi*y*(ξ+t))*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Complex.exp (Complex.ofReal (-2*Real.pi*y*ξ)*Complex.I) *
      Complex.exp (-2*(Real.pi : ℂ)*Complex.I*Complex.ofReal (y*t))) * (U y : ℂ) := by ring
    _ = _ := by rw [he]

end CubicTenVariables.ModulatedDeltaCutoff
