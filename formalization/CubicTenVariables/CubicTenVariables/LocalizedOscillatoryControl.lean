import CubicTenVariables.DyadicOscillatoryControl
import CubicTenVariables.LocalizedFrequencyComparison

/-! Fixed-factor denominator changes preserve the common frequency cutoff
and gradient width after increasing a single physical-scale threshold.
This covers the lcm(q,W) denominator without replacing it by q. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.LocalizedOscillatoryControl
open MvPolynomial MeasureTheory RealRegularGradientChart OscillatoryLocalization
open LocalSupremumNumerics GradientVolumeNumerics
variable {F : MvPolynomial (Fin 10) ℝ}

theorem exists_threshold (κ η : ℝ) (hκ : 1 ≤ κ) (hη : 0 < η) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → κ ≤ P^(η/2) := by
  refine ⟨max 1 (κ^((η/2)⁻¹)),le_max_left _ _,?_⟩
  intro P hP
  exact (Real.rpow_inv_le_iff_of_pos (zero_le_one.trans hκ)
    (zero_le_one.trans ((le_max_left _ _).trans hP)) (half_pos hη)).mp
      ((le_max_right _ _).trans hP)

theorem frequency_scale_le (P R φ κ η : ℝ) (hP : 0 < P) (hR : 0 ≤ R)
    (hκ : κ ≤ P^(η/2)) : P^(η/2)*V P (κ*R) φ ≤ P^η*V P R φ := by
  have hv : 0 ≤ V P R φ := by unfold V; positivity
  have he : V P (κ*R) φ=κ*V P R φ := by unfold V; ring
  rw [he]
  calc
    _ ≤ P^(η/2)*(P^(η/2)*V P R φ) := by gcongr
    _ = _ := by rw [← mul_assoc,← Real.rpow_add hP]; congr 2; ring

theorem gradient_scale_le (P R φ κ η : ℝ) (hP : 0 < P) (hR : 0 ≤ R)
    (hκ : κ ≤ P^(η/2)) : P^(η/2)*Vzero P (κ*R) φ ≤ P^η*Vzero P R φ := by
  have hv : 0 ≤ Vzero P R φ := by unfold Vzero; positivity
  have he : Vzero P (κ*R) φ=κ*Vzero P R φ := by unfold Vzero; ring
  rw [he]
  calc
    _ ≤ P^(η/2)*(P^(η/2)*Vzero P R φ) := by gcongr
    _ = _ := by rw [← mul_assoc,← Real.rpow_add hP]; congr 2; ring

/-- Uniform rapid decay for any denominator bounded by 2κR, with the
original R in the cutoff. In particular κ=W permits lcm(q,W). -/
theorem exists_rapid_bound 
    (D : Data F) (hF : F.IsHomogeneous 3) (κ : ℝ) (hκ : 1 ≤ κ)
    (η : ℝ) (hη : 0 < η) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ ℓ θ : ℝ, 1 ≤ R → 0 < φ → 0 < ℓ → ℓ ≤ 2*(κ*R) → ℓ ≤ P^2 →
      |θ| ≤ 2*φ → ∀ v : Fin 10 → ℝ, P^η*V P R φ ≤ ‖v‖ →
      ‖scaledIntegral F D.weight.weight P θ (ℓ⁻¹ • v)‖ ≤
        C*P^(-(A : ℝ))*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,P₁,hC,hP₁,hbound⟩ := DyadicOscillatoryControl.exists_rapid_bound
    D hF (η/2) (half_pos hη) A N
  obtain ⟨P₂,hP₂,hslack⟩ := exists_threshold κ η hκ hη
  refine ⟨C,max P₁ P₂,hC,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP R φ ℓ θ hR hφ hℓ hℓR hℓP hθ v hv
  have hPbase : P₁ ≤ P := (le_max_left _ _).trans hP
  apply hbound P hPbase (κ*R) φ ℓ θ
    (one_le_mul_of_one_le_of_one_le hκ hR) hφ hℓ hℓR hℓP hθ v
  exact (frequency_scale_le P R φ κ η (zero_lt_one.trans_le (hP₁.trans hPbase))
    (zero_le_one.trans hR) (hslack P ((le_max_right _ _).trans hP))).trans hv

/-- Uniform physical gradient localization with the original R in its
width and the true denominator ℓ in its oscillatory phase. -/
theorem exists_localization_bound 
    (D : Data F) (hF : F.IsHomogeneous 3) (κ : ℝ) (hκ : 1 ≤ κ)
    (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ ℓ θ : ℝ, 1 ≤ R → 0 < φ → 0 < ℓ → ℓ ≤ 2*(κ*R) → |θ| ≤ 2*φ →
      ∀ v : Fin 10 → ℝ,
      ‖scaledIntegral F D.weight.weight P θ (ℓ⁻¹ • v)‖ ≤
        C*(P^(-(A : ℝ))+
          (volume (GradientWindowScaling.window F D.box P (ℓ*θ) v (P^η*Vzero P R φ))).toReal) := by
  obtain ⟨C,P₁,hC,hP₁,hbound⟩ := DyadicOscillatoryControl.exists_localization_bound
    D hF (η/2) (half_pos hη) A
  obtain ⟨P₂,hP₂,hslack⟩ := exists_threshold κ η hκ hη
  refine ⟨C,max P₁ P₂,hC,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP R φ ℓ θ hR hφ hℓ hℓR hθ v
  have hPbase : P₁ ≤ P := (le_max_left _ _).trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₁.trans hPbase)
  have hw := gradient_scale_le P R φ κ η hPpos (zero_le_one.trans hR)
    (hslack P ((le_max_right _ _).trans hP))
  apply (hbound P hPbase (κ*R) φ ℓ θ
    (one_le_mul_of_one_le_of_one_le hκ hR) hφ hℓ hℓR hθ v).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply add_le_add le_rfl
  apply ENNReal.toReal_mono (PhysicalGradientWindow.volume_window_ne_top F hF D P hPpos _ _ _)
  apply measure_mono
  intro x hx
  exact ⟨hx.1,fun i => (hx.2 i).trans hw⟩

end CubicTenVariables.LocalizedOscillatoryControl
