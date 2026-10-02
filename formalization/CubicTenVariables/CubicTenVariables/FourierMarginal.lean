import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Fourier inversion for an actual Schwartz marginal

The exponential has the positive sign used by the cubic oscillatory integral.
All integrals use real Lebesgue measure, with the `2π` normalization.  These
theorems concern a given Schwartz function; they do not assert that any cubic
oscillatory integral has such a marginal.
-/

noncomputable section

namespace CubicTenVariables.FourierMarginal

open MeasureTheory Filter
open scoped Topology FourierTransform

/-- Real-valued Schwartz functions viewed as complex-valued Schwartz functions. -/
def complexify (g : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (Function.HasTemperateGrowth.const (1 : ℂ)) g

@[simp] theorem complexify_apply (g : SchwartzMap ℝ ℝ) (t : ℝ) :
    complexify g t = (g t : ℂ) := by
  simp [complexify, Complex.real_smul]

/-- The literal one-dimensional oscillatory integral, with positive sign. -/
def positiveFourier (g : SchwartzMap ℝ ℝ) (β : ℝ) : ℂ :=
  ∫ t : ℝ, (g t : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (t : ℂ))

/-- The positive-sign oscillatory integral is mathlib's inverse Fourier transform. -/
theorem positiveFourier_eq_fourierInv (g : SchwartzMap ℝ ℝ) :
    positiveFourier g = ((𝓕⁻ (complexify g) : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  funext β
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  unfold positiveFourier
  apply integral_congr_ae
  filter_upwards with t
  simp only [complexify_apply, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- Absolute integrability in the frequency variable follows from the Schwartz property. -/
theorem positiveFourier_integrable (g : SchwartzMap ℝ ℝ) :
    Integrable (positiveFourier g) := by
  rw [positiveFourier_eq_fourierInv]
  exact (𝓕⁻ (complexify g) : SchwartzMap ℝ ℂ).integrable

/-- Fourier inversion at zero, with the exact Lebesgue and `2π` normalization. -/
theorem integral_positiveFourier (g : SchwartzMap ℝ ℝ) :
    (∫ β : ℝ, positiveFourier g β) = (g 0 : ℂ) := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f 0)
    (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap ℝ ℂ) (complexify g))
  change (𝓕 ((𝓕⁻ (complexify g) : SchwartzMap ℝ ℂ) : ℝ → ℂ)) 0 = complexify g 0 at h
  rw [Real.fourier_eq] at h
  rw [positiveFourier_eq_fourierInv]
  simpa using h

/-- Truncation to the actual closed intervals `[-T,T]` converges to the same value. -/
theorem tendsto_setIntegral_positiveFourier (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun T : ℝ => ∫ β in Set.Icc (-T) T, positiveFourier g β)
      atTop (𝓝 (g 0 : ℂ)) := by
  rw [← integral_positiveFourier g]
  exact (aecover_Icc tendsto_neg_atTop_atBot tendsto_id).integral_tendsto_of_countably_generated
    (positiveFourier_integrable g)

/-- The oriented interval integrals used for truncated singular integrals have the same limit. -/
theorem tendsto_intervalIntegral_positiveFourier (g : SchwartzMap ℝ ℝ) :
    Tendsto (fun T : ℝ => ∫ β in (-T)..T, positiveFourier g β)
      atTop (𝓝 (g 0 : ℂ)) := by
  rw [← integral_positiveFourier g]
  exact intervalIntegral_tendsto_integral (positiveFourier_integrable g)
    tendsto_neg_atTop_atBot tendsto_id

/-- A positive value of the marginal at zero gives a strictly positive real full integral. -/
theorem integral_positiveFourier_re_pos (g : SchwartzMap ℝ ℝ) (hg : 0 < g 0) :
    0 < (∫ β : ℝ, positiveFourier g β).re := by
  simpa only [integral_positiveFourier, Complex.ofReal_re] using hg

theorem integral_positiveFourier_im (g : SchwartzMap ℝ ℝ) :
    (∫ β : ℝ, positiveFourier g β).im = 0 := by
  simp only [integral_positiveFourier, Complex.ofReal_im]

/-- A convenient positive-real-value form, still accompanied by actual integrability. -/
theorem exists_positive_integral (g : SchwartzMap ℝ ℝ) (hg : 0 < g 0) :
    Integrable (positiveFourier g) ∧
      ∃ J : ℝ, 0 < J ∧ (∫ β : ℝ, positiveFourier g β) = (J : ℂ) :=
  ⟨positiveFourier_integrable g, g 0, hg, integral_positiveFourier g⟩

end CubicTenVariables.FourierMarginal
