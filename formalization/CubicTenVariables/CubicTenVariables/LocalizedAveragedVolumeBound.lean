import CubicTenVariables.LocalizedWindowIntegral
import CubicTenVariables.DyadicAveragedVolumeBound

/-! Uniform integration of the completed local maximum-volume estimate over
the actual expanded dyadic shell, followed by the shifted-window reduction. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedAveragedVolumeBound
open MvPolynomial MeasureTheory RealRegularGradientChart
open GradientWindowMeasurability DyadicPhaseSubstitution AveragedGradientVolume
open LocalSupremumNumerics GradientVolumeNumerics LocalizedWindowIntegral
open LocalSupremumWindow LocalizedShiftedWindow
open DyadicAveragedVolumeBound (volumeFactor volumeFactor_nonneg)

/-- One constant precedes all analytic parameters; all integrals are of
actual measurable finite local maxima. Both phase signs are retained. -/
theorem exists_integral_bound (F : MvPolynomial (Fin 10) ℝ) (hF : F.IsHomogeneous 3)
    (D : Data F) (W : ℕ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ε P R φ L : ℝ, 0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ → 0 ≤ L →
      (∫ τ in annulus φ (4*(W:ℝ)*φ), volumeSum F D.box P (R*τ)
        (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L) ≤
          C*φ*volumeFactor ε P R φ L := by
  obtain ⟨C,hC,hb⟩ := LocalSupremumVolumeEstimate.exists_bound F hF D 1 (by norm_num)
  have hWreal : (1:ℝ) ≤ W := by exact_mod_cast hW
  have hWC : (1:ℝ) ≤ (W:ℝ)*C := one_le_mul_of_one_le_of_one_le hWreal hC
  refine ⟨8*(W:ℝ)*C,by nlinarith only [hWC],?_⟩
  intro ε P R φ L hε hP hR hφ hL
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hvf := volumeFactor_nonneg ε P R φ L hP0 hR0 hL
  have hi := integrableOn_volumeSum_comp F hF D P hP0
    (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L
    (fun τ => R*τ) (measurable_const.mul measurable_id) volume (annulus φ (4*(W:ℝ)*φ))
    (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))
  have hcst : IntegrableOn (fun _ : ℝ => C*volumeFactor ε P R φ L) (annulus φ (4*(W:ℝ)*φ)) :=
    integrableOn_const (LocalizedPhaseSubstitution.volume_expanded_ne_top φ (W:ℝ))
  have hpoint (τ : ℝ) (hτ : τ ∈ annulus φ (4*(W:ℝ)*φ)) :
      volumeSum F D.box P (R*τ) (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) L ≤
        C*volumeFactor ε P R φ L := by
    have hα : 1*(R*φ) ≤ |R*τ| := by
      rw [one_mul,abs_mul,abs_of_pos hR0]
      exact mul_le_mul_of_nonneg_left hτ.1.le hR0.le
    have hh := hb D.box (fun _ hx => hx) ε P R φ (R*τ) L hε hP hR hφ hL hα
    convert hh using 1
    unfold volumeFactor
    split_ifs <;> ring
  have hmeas : (volume (annulus φ (4*(W:ℝ)*φ))).toReal ≤ 8*(W:ℝ)*φ := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 8*(W:ℝ)*φ)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (LocalizedPhaseSubstitution.volume_expanded_le φ (W:ℝ))
  calc
    _ ≤ ∫ _τ in annulus φ (4*(W:ℝ)*φ), C*volumeFactor ε P R φ L :=
      setIntegral_mono_on hi hcst (measurableSet_annulus _ _) hpoint
    _ = (volume (annulus φ (4*(W:ℝ)*φ))).toReal*(C*volumeFactor ε P R φ L) := by
      simp [MeasureTheory.measureReal_def]
    _ ≤ (8*(W:ℝ)*φ)*(C*volumeFactor ε P R φ L) :=
      mul_le_mul_of_nonneg_right hmeas (mul_nonneg (zero_le_one.trans hC) hvf)
    _ = _ := by ring

/-- The localized error has no remaining integral once a literal uniform
shifted complete-sum bound is supplied. This antecedent is arithmetic, not an
unproved geometric or analytic estimate. -/
theorem exists_localizedError_bound (F : MvPolynomial (Fin 10) ℝ)
    (hF : F.IsHomogeneous 3) (D : Data F) (W : ℕ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : MvPolynomial (Fin 10) ℤ) (Ω : Set (Fin 10 → ZMod W)) (ε P R φ H : ℝ) (L : ℕ),
      0 < ε → 1 ≤ P → 1 ≤ R → 0 < φ → 0 ≤ H →
      (∀ v ∈ centers (frequencies 10 (P^(ε/17)*V P R φ)) L, shiftedSum G W Ω R L v ≤ H) →
      localizedError G W Ω F D P R φ (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) ≤
        C*φ*(H/((2*L+1 : ℕ) : ℝ)^10)*(R^10)⁻¹*volumeFactor ε P R φ (L : ℝ) := by
  obtain ⟨C,hC,hb⟩ := exists_integral_bound F hF D W hW
  refine ⟨C,hC,?_⟩
  intro G Ω ε P R φ H L hε hP hR hφ hH hshift
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have ha := localizedError_le_average G W Ω F hF D P R φ
    (P^(ε/17)*V P R φ) (P^(ε/17)*Vzero P R φ) H L hP0 hR0 hφ.le hshift
  calc
    _ ≤ _ := ha
    _ ≤ (R^10)⁻¹*(H/((2*L+1 : ℕ) : ℝ)^10)*(C*φ*volumeFactor ε P R φ (L : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb ε P R φ L hε hP hR hφ (by positivity)) (by positivity)
    _ = _ := by ring

end CubicTenVariables.LocalizedAveragedVolumeBound
