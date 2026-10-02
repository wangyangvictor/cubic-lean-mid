import CubicTenVariables.DyadicFrequencyError
import CubicTenVariables.DyadicGradientScales
import CubicTenVariables.OscillatoryLocalizationRapidTail
import CubicTenVariables.GradientOscillatoryEstimate
import CubicTenVariables.PhysicalGradientWindow

/-! Oscillatory estimates on the actual fixed regular chart, with a common
dyadic frequency cutoff and gradient width. A smaller upstream exponent
absorbs fixed dyadic constants before the varying analytic parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.DyadicOscillatoryControl
open MvPolynomial MeasureTheory RealRegularGradientChart OscillatoryLocalization
open LocalSupremumNumerics GradientVolumeNumerics
variable {F : MvPolynomial (Fin 10) ℝ}

theorem exists_rapid_bound 
    (D : Data F) (hF : F.IsHomogeneous 3) (η : ℝ) (hη : 0 < η) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ q θ : ℝ, 1 ≤ R → 0 < φ → 0 < q → q ≤ 2*R → q ≤ P^2 →
      |θ| ≤ 2*φ → ∀ v : Fin 10 → ℝ, P^η*V P R φ ≤ ‖v‖ →
      ‖scaledIntegral F D.weight.weight P θ (q⁻¹ • v)‖ ≤
        C*P^(-(A : ℝ))*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,P₁,hC,hP₁,hb⟩ := exists_source_rapid_frequency_bound (by decide)
    F hF D.normalizedWeight D.normalized_smooth D.normalized_compact D.normalized_nonneg
    D.normalized_support D.point D.radius D.radius_pos (η/4) (by positivity) A N
  obtain ⟨P₂,hP₂,hslack⟩ := DyadicGradientScales.exists_threshold η hη
  refine ⟨C,max P₁ P₂,hC,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP R φ q θ hR hφ hq hqR hqP hθ v hv
  have hPbase : P₁ ≤ P := (le_max_left _ _).trans hP
  rw [D.weight_eq]
  apply hb P hPbase q hq hqP θ v
  exact (DyadicGradientScales.frequency_cutoff_le η P R φ q θ hη
    (hP₁.trans hPbase) (zero_le_one.trans hR) hφ.le hq.le hqR hθ
    (hslack P ((le_max_right _ _).trans hP))).trans hv

theorem exists_localization_bound 
    (D : Data F) (hF : F.IsHomogeneous 3) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ q θ : ℝ, 1 ≤ R → 0 < φ → 0 < q → q ≤ 2*R → |θ| ≤ 2*φ →
      ∀ v : Fin 10 → ℝ,
      ‖scaledIntegral F D.weight.weight P θ (q⁻¹ • v)‖ ≤
        C*(P^(-(A : ℝ))+
          (volume (GradientWindowScaling.window F D.box P (q*θ) v (P^η*Vzero P R φ))).toReal) := by
  obtain ⟨C,P₁,hC,hP₁,hb⟩ := exists_source_localization_exact (by decide)
    F hF D.normalizedWeight D.normalized_smooth D.normalized_compact D.normalized_nonneg
    D.normalized_support D.point D.radius D.radius_pos (η/4) (by positivity) A
  obtain ⟨P₂,hP₂,hslack⟩ := DyadicGradientScales.exists_threshold η hη
  refine ⟨C,max P₁ P₂,hC,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP R φ q θ hR hφ hq hqR hθ v
  have hPbase : P₁ ≤ P := (le_max_left _ _).trans hP
  have hPone : 1 ≤ P := hP₁.trans hPbase
  have hPpos : 0 < P := zero_lt_one.trans_le hPone
  have hsub : sourceWindow F D.point D.radius P θ q v 1 (η/4) ⊆
      GradientWindowScaling.window F D.box P (q*θ) v (P^η*Vzero P R φ) := by
    intro x hx
    have hy := GradientOscillatoryEstimate.sourceWindow_subset_window D P q θ (η/4) v hx
    exact ⟨hy.1,fun i => (hy.2 i).trans (DyadicGradientScales.gradient_width_le
      η P R φ q θ hη hPone (zero_le_one.trans hR) hφ.le hq.le hqR hθ
      (hslack P ((le_max_right _ _).trans hP)))⟩
  rw [D.weight_eq]
  apply (hb P hPbase q hq θ v).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply add_le_add le_rfl
  exact ENNReal.toReal_mono (PhysicalGradientWindow.volume_window_ne_top F hF D P hPpos _ _ _)
    (measure_mono hsub)

/-- The actual theta-integrated mass has rapid decay outside the common
finite frequency set, uniformly over every modulus in the dyadic block. -/
theorem exists_frequencyMass_bound 
    (G : MvPolynomial (Fin 10) ℤ) (hG : G.IsHomogeneous 3)
    (D : Data (map (Int.castRingHom ℝ) G)) (η : ℝ) (hη : 0 < η) (A N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R φ : ℝ, 1 ≤ R → 0 < φ → ∀ q : ℕ,
      q ∈ DyadicFrequencyError.moduli R → (q : ℝ) ≤ P^2 →
      ∀ v : Fin 10 → ℤ, v ≠ 0 → v ∉ LocalSupremumWindow.frequencies 10 (P^η*V P R φ) →
      DyadicFrequencyError.frequencyMass G D.weight.weight P φ q v ≤
        (4*φ*C)*P^(-(A : ℝ))*‖(fun i => (v i : ℝ))‖^(-(N : ℝ)) := by
  obtain ⟨C,P₀,hC,hP₀,hb⟩ := exists_rapid_bound D (hG.map _) η hη A N
  refine ⟨C,P₀,hC,hP₀,?_⟩
  intro P hP R φ hR hφ q hq hqP v hv hnot
  obtain ⟨hqR,hq2R⟩ := (DyadicFrequencyError.mem_moduli R q).mp hq
  have hPpos : 0 < P := zero_lt_one.trans_le (hP₀.trans hP)
  have hqpos : (0:ℝ) < q := (zero_lt_one.trans_le hR).trans hqR
  have hcut : P^η*V P R φ ≤ ‖(fun i => (v i : ℝ))‖ := by
    by_contra! h
    apply hnot
    apply (LocalSupremumWindow.mem_frequencies _ v).mpr
    refine ⟨hv,?_⟩
    intro i
    have hi : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (v i : ℝ)) i
    exact hi.trans h.le
  have hmass := DyadicFrequencyError.frequencyMass_le G D.weight.weight D.weight.smooth.continuous
    D.weight.compact P φ hPpos.ne' hφ.le q v
    (C*P^(-(A : ℝ))*‖(fun i => (v i : ℝ))‖^(-(N : ℝ))) (by positivity)
    (fun θ hθ => hb P hP R φ q θ hR hφ hqpos hq2R hqP hθ.2 _ hcut)
  convert hmass using 1
  ring

end CubicTenVariables.DyadicOscillatoryControl
