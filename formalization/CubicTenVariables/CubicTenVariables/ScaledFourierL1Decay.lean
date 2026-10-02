import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic

/-! Fourier decay from two scaled derivative integral bounds. This is the
one-dimensional integration-by-parts estimate needed for the smooth delta
kernel. The low-frequency and derivative integral bounds are explicit
hypotheses, to be proved separately for that kernel.

The same low/high-frequency argument appears in OpenAI's PrimeGaps186,
`compactProfile_fourier_decay_bound_order` (commit
61340d0b74163003b32756bb16e91d9209a5e330). Here the inputs are integral
bounds rather than a fixed support and pointwise derivative bounds. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ScaledFourierL1Decay
open MeasureTheory
open scoped FourierTransform ContDiff

/-- The scale belongs inside the frequency weight; the constant contains no
inverse power of that scale. This follows from integration by parts `N` times. -/
theorem one_add_scaled_abs_pow_mul_le
    (f : ℝ → ℂ) (N : ℕ) (hf : ContDiff ℝ N f)
    (hi : ∀ j : ℕ, j ≤ N → Integrable (iteratedDeriv j f))
    (a B : ℝ) (ha : 0 < a)
    (h0 : (∫ x : ℝ, ‖f x‖) ≤ B)
    (hN : a^N * (∫ x : ℝ, ‖iteratedDeriv N f x‖) ≤ B) (ξ : ℝ) :
    (1+a*|ξ|)^N * ‖𝓕 f ξ‖ ≤ (2 : ℝ)^N * B := by
  have hnorm (g : ℝ → ℂ) : ‖𝓕 g ξ‖ ≤ ∫ x : ℝ, ‖g x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) g ξ
  have hlow : ‖𝓕 f ξ‖ ≤ B := (hnorm f).trans h0
  have hD := congrFun (Real.fourier_iteratedDeriv (N := N) hf
    (fun j hj => hi j (by exact_mod_cast hj)) (n := N) le_rfl) ξ
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)‖ =
      2 * Real.pi * |ξ| := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hhigh : (2*Real.pi*|ξ|)^N * ‖𝓕 f ξ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv N f x‖ := by
    calc
      _ = ‖(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))^N • 𝓕 f ξ‖ := by
        rw [norm_smul,norm_pow,hc]
      _ = ‖𝓕 (iteratedDeriv N f) ξ‖ := congrArg norm hD.symm
      _ ≤ _ := hnorm _
  have hpi : 1 ≤ (2*Real.pi)^N :=
    one_le_pow₀ (by linarith [Real.one_le_pi_div_two])
  have hweighted : (a*|ξ|)^N * ‖𝓕 f ξ‖ ≤ B := by
    have hh := (mul_le_mul_of_nonneg_left hhigh (pow_nonneg ha.le N)).trans hN
    have he : a^N * ((2*Real.pi*|ξ|)^N * ‖𝓕 f ξ‖) =
        (2*Real.pi)^N * ((a*|ξ|)^N * ‖𝓕 f ξ‖) := by
      simp only [mul_pow]
      ring
    rw [he] at hh
    exact (le_mul_of_one_le_left
      (mul_nonneg (pow_nonneg (mul_nonneg ha.le (abs_nonneg ξ)) N) (norm_nonneg _))
      hpi).trans hh
  rcases le_total (a*|ξ|) 1 with hsmall | hlarge
  · exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith : 1+a*|ξ| ≤ 2) N)
      (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hlow (pow_nonneg (by norm_num) N))
  · calc
      _ ≤ (2*(a*|ξ|))^N * ‖𝓕 f ξ‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith) N) (norm_nonneg _)
      _ = (2 : ℝ)^N * ((a*|ξ|)^N * ‖𝓕 f ξ‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweighted (pow_nonneg (by norm_num) N)

/-- The equivalent rapid-decay form, valid at zero frequency as well. -/
theorem norm_fourier_le
    (f : ℝ → ℂ) (N : ℕ) (hf : ContDiff ℝ N f)
    (hi : ∀ j : ℕ, j ≤ N → Integrable (iteratedDeriv j f))
    (a B : ℝ) (ha : 0 < a)
    (h0 : (∫ x : ℝ, ‖f x‖) ≤ B)
    (hN : a^N * (∫ x : ℝ, ‖iteratedDeriv N f x‖) ≤ B) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ (2 : ℝ)^N * B * (1+a*|ξ|)^(-(N : ℝ)) := by
  have hp : 0 < 1+a*|ξ| := by positivity
  have h := one_add_scaled_abs_pow_mul_le f N hf hi a B ha h0 hN ξ
  rw [Real.rpow_neg hp.le,Real.rpow_natCast,← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hp N)).mpr
  simpa only [mul_comm] using h

end CubicTenVariables.ScaledFourierL1Decay
