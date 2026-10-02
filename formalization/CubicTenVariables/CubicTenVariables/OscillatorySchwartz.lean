import CubicTenVariables.OscillatoryLocalization
import CubicTenVariables.PolynomialCalculus
import CubicTenVariables.Literature.ScalarLatticePoisson
import CubicTenVariables.DeltaMethod
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! The literal polynomial oscillatory weight as a Schwartz function.

The domain is the ordinary coordinate space `Fin n → ℝ`. Its volume is the
product of the one-dimensional Lebesgue measures. Smoothness and compact
support, including the effect of scaling the weight, are proved here.
No homogeneity, degree bound, or analytic estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.OscillatorySchwartz
open MvPolynomial MeasureTheory
open scoped BigOperators ContDiff

variable {n : ℕ}

/-- The physical oscillatory weight before inserting a Fourier frequency. -/
def weight (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (P θ : ℝ) (x : Fin n → ℝ) : ℂ :=
  (w (P⁻¹ • x) : ℂ) * Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * ((θ * eval x F : ℝ) : ℂ))

theorem weight_smooth (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (weight F w P θ) := by
  have hwc : ContDiff ℝ ∞ (fun x : Fin n → ℝ => (w (P⁻¹ • x) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hw.comp (contDiff_const.smul contDiff_id))
  have hphase : ContDiff ℝ ∞ (fun x : Fin n → ℝ => ((θ * eval x F : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (PolynomialCalculus.contDiff_eval F))
  exact hwc.mul (contDiff_const.mul hphase).cexp

theorem weight_compact (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hc : HasCompactSupport w)
    (hP : P ≠ 0) : HasCompactSupport (weight F w P θ) := by
  have hs : HasCompactSupport (fun x : Fin n → ℝ => w (P⁻¹ • x)) := by
    exact hc.comp_homeomorph (Homeomorph.smulOfNeZero P⁻¹ (inv_ne_zero hP))
  exact (hs.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right

/-- The Schwartz object has exactly the displayed physical weight as its
underlying function. Positivity of P is the scale convention used later. -/
def schwartz (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (P θ : ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hP : 0 < P) : SchwartzMap (Fin n → ℝ) ℂ :=
  (weight_compact F w P θ hc hP.ne').toSchwartzMap (weight_smooth F w P θ hw)

@[simp] theorem schwartz_apply (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) (hP : 0 < P) (x : Fin n → ℝ) :
    schwartz F w P θ hw hc hP x = weight F w P θ x := rfl

/-- Multiplication by the negative Fourier character gives precisely the
phase convention in `scaledIntegral`. -/
theorem weight_mul_fourier_character (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (β x : Fin n → ℝ) :
    weight F w P θ x * Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, β i*x i : ℝ) : ℂ)) =
    (w (P⁻¹ • x) : ℂ) * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * ((θ * eval x F - ∑ i, β i*x i : ℝ) : ℂ)) := by
  unfold weight
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Exact integral identity, using coordinate product Lebesgue measure. -/
theorem integral_eq_scaledIntegral (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (β : Fin n → ℝ) :
    (∫ x : Fin n → ℝ, weight F w P θ x * Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, β i*x i : ℝ) : ℂ))
      ∂Measure.pi (fun _ : Fin n => volume)) =
    OscillatoryLocalization.scaledIntegral F w P θ β := by
  apply integral_congr_ae
  filter_upwards [] with x
  exact weight_mul_fourier_character F w P θ β x

/-- The physical wave is genuinely integrable. -/
theorem weight_integrable (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) (hP : 0 < P) :
    Integrable (weight F w P θ) :=
  (weight_smooth F w P θ hw).continuous.integrable_of_hasCompactSupport
    (weight_compact F w P θ hc hP.ne')

/-- The Fourier integrand is integrable at every frequency. -/
theorem fourier_integrand_integrable (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) (hP : 0 < P) (β : Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => weight F w P θ x * Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * ((∑ i, β i*x i : ℝ) : ℂ))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · apply (weight_smooth F w P θ hw).continuous.mul
    fun_prop
  · exact (weight_compact F w P θ hc hP.ne').mul_right

/-- The generic Poisson input's Fourier transform is exactly the existing
physical oscillatory integral, with no change of sign or normalization. -/
theorem fourier_weight_eq_scaledIntegral (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (β : Fin n → ℝ) :
    ScalarLatticePoisson.fourier (weight F w P θ) β =
      OscillatoryLocalization.scaledIntegral F w P θ β :=
  integral_eq_scaledIntegral F w P θ β

theorem fourier_eq_scaledIntegral (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (P θ : ℝ) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) (hP : 0 < P) (β : Fin n → ℝ) :
    ScalarLatticePoisson.fourier (schwartz F w P θ hw hc hP) β =
      OscillatoryLocalization.scaledIntegral F w P θ β :=
  integral_eq_scaledIntegral F w P θ β

/-- Evaluating an integral polynomial at an integer vector commutes with
embedding both its coefficients and coordinates in the real numbers. -/
theorem eval_map_integer (G : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) :
    eval (fun i => (x i : ℝ)) (map (Int.castRingHom ℝ) G) = (eval x G : ℝ) := by
  exact (MvPolynomial.map_eval (Int.castRingHom ℝ) x G).symm

/-- At integer arguments the Schwartz wave is the exact summand used by
the delta method; the coordinate scaling is xᵢ/P in every coordinate. -/
theorem weight_integer (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (P : ℕ) (θ : ℝ) (x : Fin n → ℤ) :
    weight (map (Int.castRingHom ℝ) G) w (P : ℝ) θ (fun i => (x i : ℝ)) =
      (w (scaledIntegerPoint P x) : ℂ) * DeltaMethod.realExponential (θ*(eval x G : ℝ)) := by
  have hx : (P : ℝ)⁻¹ • (fun i => (x i : ℝ)) = scaledIntegerPoint P x := by
    ext i
    simp only [Pi.smul_apply,smul_eq_mul,scaledIntegerPoint,div_eq_mul_inv,mul_comm]
  simp only [weight,hx,eval_map_integer,DeltaMethod.realExponential]

end CubicTenVariables.OscillatorySchwartz
