import CubicTenVariables.LocalizedShiftedWindow
import CubicTenVariables.GradientWindowMeasurability
import CubicTenVariables.LocalizedPhaseSubstitution
import CubicTenVariables.LocalSupremumVolumeEstimate

/-! The finite localized dyadic error after the exact phase substitution.
All integrands are actual finite complete sums and physical window volumes;
the shifted-average bound remains an explicit arithmetic antecedent. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.LocalizedWindowIntegral
open MvPolynomial MeasureTheory RealRegularGradientChart DyadicFrequencyError
open LocalSupremumWindow GradientWindowMeasurability DyadicPhaseSubstitution
open LocalizedShiftedWindow AveragedGradientVolume
open scoped BigOperators

def integrand (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (F : MvPolynomial (Fin 10) ℝ)
    (D : Data F) (P R B δ τ : ℝ) : ℝ :=
  ∑ q ∈ moduli R, ∑ a ∈ frequencies 10 B, ‖localizedCompleteCubicSum G q W Ω a‖*
    (volume (GradientWindowScaling.window F D.box P (R*τ) (fun i => (a i : ℝ)) δ)).toReal

def localizedError (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (F : MvPolynomial (Fin 10) ℝ)
    (D : Data F) (P R φ B δ : ℝ) : ℝ :=
  (R^10)⁻¹ * ∫ τ in annulus φ (4*(W:ℝ)*φ), integrand G W Ω F D P R B δ τ

theorem integrand_nonneg (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (F : MvPolynomial (Fin 10) ℝ)
    (D : Data F) (P R B δ τ : ℝ) : 0 ≤ integrand G W Ω F D P R B δ τ := by
  exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun a _ =>
    mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg

theorem integrableOn_integrand (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W)) (F : MvPolynomial (Fin 10) ℝ)
    (hF : F.IsHomogeneous 3) (D : Data F) (P R φ B δ : ℝ) (hP : 0 < P) (_hφ : 0 ≤ φ) :
    IntegrableOn (integrand G W Ω F D P R B δ) (annulus φ (4*(W:ℝ)*φ)) := by
  apply integrable_finset_sum
  intro q _
  apply integrable_finset_sum
  intro a _
  exact (integrableOn_window_real_comp F hF D P hP (fun i => (a i : ℝ)) δ
    (fun τ => R*τ) (measurable_const.mul measurable_id) volume (annulus φ (4*(W:ℝ)*φ))
    (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))).const_mul _

/-- The exact finite average inequality survives phase integration. The
integrability of the actual maximum-volume lattice sum is proved separately. -/
theorem localizedError_le_average (G : MvPolynomial (Fin 10) ℤ) (W : ℕ) (Ω : Set (Fin 10 → ZMod W))
    (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3) (D : Data F)
    (P R φ B δ H : ℝ) (L : ℕ) (hP : 0 < P) (hR : 0 < R) (hφ : 0 ≤ φ)
    (hshift : ∀ v ∈ centers (frequencies 10 B) L, shiftedSum G W Ω R L v ≤ H) :
    localizedError G W Ω F D P R φ B δ ≤
      (R^10)⁻¹ * (H/((2*L+1 : ℕ) : ℝ)^10) *
        ∫ τ in annulus φ (4*(W:ℝ)*φ), volumeSum F D.box P (R*τ) B δ (L : ℝ) := by
  have hd : (0:ℝ) < ((2*L+1 : ℕ) : ℝ)^10 := by positivity
  have hi := integrableOn_integrand G W Ω F hF D P R φ B δ hP hφ
  have hj := integrableOn_volumeSum_comp F hF D P hP B δ (L : ℝ)
    (fun τ => R*τ) (measurable_const.mul measurable_id) volume (annulus φ (4*(W:ℝ)*φ))
    (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))
  have hp (τ : ℝ) : integrand G W Ω F D P R B δ τ ≤
      (H/((2*L+1 : ℕ) : ℝ)^10)*volumeSum F D.box P (R*τ) B δ (L : ℝ) := by
    have hh := weighted_volume_sum_le G W Ω F D.box P R (R*τ) B δ H L hshift
    have hh' : integrand G W Ω F D P R B δ τ ≤
        (H*volumeSum F D.box P (R*τ) B δ (L : ℝ))/((2*L+1 : ℕ) : ℝ)^10 :=
      (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hh)
    convert hh' using 1
    ring
  unfold localizedError
  calc
    _ ≤ (R^10)⁻¹ * ∫ τ in annulus φ (4*(W:ℝ)*φ),
        (H/((2*L+1 : ℕ) : ℝ)^10)*volumeSum F D.box P (R*τ) B δ (L : ℝ) :=
      mul_le_mul_of_nonneg_left (integral_mono hi (hj.const_mul _) hp) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end CubicTenVariables.LocalizedWindowIntegral
