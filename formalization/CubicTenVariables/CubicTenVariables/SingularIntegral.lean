import CubicTenVariables.RealChartWeight
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The literal archimedean oscillatory integrals, with the same positive
exponential sign as the complete sums. Fixed-frequency integrability and
continuity are proved here. Integrability over all frequencies, positivity
of the singular integral, and a counting asymptotic are separate obligations.
-/

noncomputable section
namespace CubicTenVariables
open MvPolynomial MeasureTheory
open scoped Topology

def cubicOscillatoryIntegrand {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) : ℂ :=
  (w x : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (eval x F : ℂ))

def cubicOscillatoryIntegral {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (β : ℝ) : ℂ :=
  ∫ x : Fin n → ℝ, cubicOscillatoryIntegrand F w β x

def cubicSingularIntegralTruncated {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (T : ℝ) : ℂ :=
  ∫ β in (-T)..T, cubicOscillatoryIntegral F w β

/-- This totalized integral must only be used as the analytic singular
integral alongside an actual proof of frequency integrability. -/
def cubicSingularIntegral {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) : ℂ :=
  ∫ β : ℝ, cubicOscillatoryIntegral F w β

theorem cubicOscillatoryIntegrand_norm {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (β : ℝ) (x : Fin n → ℝ) :
    ‖cubicOscillatoryIntegrand F w β x‖ = |w x| := by
  simp [cubicOscillatoryIntegrand, Complex.norm_exp,
    Complex.mul_re, Complex.mul_im]

theorem cubicOscillatoryIntegrand_continuous {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) :
    Continuous (fun z : ℝ × (Fin n → ℝ) ↦ cubicOscillatoryIntegrand F w z.1 z.2) := by
  have hF := MvPolynomial.continuous_eval F
  unfold cubicOscillatoryIntegrand
  fun_prop

theorem cubicOscillatoryIntegrand_hasCompactSupport {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (hw : HasCompactSupport w) (β : ℝ) :
    HasCompactSupport (cubicOscillatoryIntegrand F w β) := by
  have hwc : HasCompactSupport (fun x ↦ (w x : ℂ)) :=
    hw.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)
  exact hwc.mul_right

/-- Ordinary compact-support integrability, for every fixed frequency. -/
theorem cubicOscillatoryIntegrand_integrable {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ)
    (hw : Continuous w) (hc : HasCompactSupport w) (β : ℝ) :
    Integrable (cubicOscillatoryIntegrand F w β) := by
  apply Continuous.integrable_of_hasCompactSupport
    ((cubicOscillatoryIntegrand_continuous F w hw).comp
      (continuous_const.prodMk continuous_id))
  exact cubicOscillatoryIntegrand_hasCompactSupport F w hc β

/-- The literal oscillatory integral has an elementary uniform bound. This
bound alone does not establish integrability over the frequency line. -/
theorem cubicOscillatoryIntegral_norm_le {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (w : (Fin n → ℝ) → ℝ) (β : ℝ) :
    ‖cubicOscillatoryIntegral F w β‖ ≤ ∫ x : Fin n → ℝ, |w x| := by
  simpa only [cubicOscillatoryIntegral, cubicOscillatoryIntegrand_norm] using
    (norm_integral_le_integral_norm (cubicOscillatoryIntegrand F w β))

end CubicTenVariables
