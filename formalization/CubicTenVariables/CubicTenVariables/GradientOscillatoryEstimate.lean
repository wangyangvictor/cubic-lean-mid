import CubicTenVariables.GradientPhysicalWindow
import CubicTenVariables.OscillatoryLocalizationSource

/-! A literal integral bound obtained from the proved rank-seven volume
estimate and internally proved cubic oscillatory localization. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GradientOscillatoryEstimate
open MvPolynomial MeasureTheory HessianTheorem11 RealRegularGradientChart OscillatoryLocalization
open GradientWindowScaling GradientVolumeNumerics
open scoped BigOperators
variable {F : MvPolynomial (Fin 10) ℝ}

theorem sourceWindow_subset_window (D : Data F) (P q θ η : ℝ) (v : Fin 10 → ℝ) :
    sourceWindow F D.point D.radius P θ q v 1 η ⊆
      window F D.box P (q*θ) v (P^η*Vzero P q |θ|) := by
  intro x hx
  refine ⟨hx.1,?_⟩
  intro i
  have hi := (norm_le_pi_norm (fun j => q*θ*eval x (pderiv j F)-v j) i).trans hx.2
  simpa only [Real.norm_eq_abs,one_mul,mul_assoc,Vzero] using hi

/-- The same actual chart weight is used in the volume estimate and the
oscillatory integral. Every constant precedes P,q,theta,v. -/
theorem exists_bound 
    (D : Data F) (hF : F.IsHomogeneous 3) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C P₀ : ℝ, 1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ q : ℝ, 1 ≤ q → ∀ (θ : ℝ) (v : Fin 10 → ℝ), θ ≠ 0 →
      ‖scaledIntegral F D.weight.weight P θ (q⁻¹ • v)‖ ≤
        C*(P^(-(N : ℝ))+P^((10 : ℝ)+ε)*(q/(P*Vzero P q |θ|))^7) := by
  obtain ⟨A,hA,hvolume⟩ := GradientPhysicalWindow.exists_epsilon_bound D hF
  obtain ⟨C,P₀,hC,hP₀,hlocal⟩ := exists_source_localization_exact (by decide) F hF
    D.normalizedWeight D.normalized_smooth D.normalized_compact D.normalized_nonneg
    D.normalized_support D.point D.radius D.radius_pos (ε/7) (by positivity) N
  refine ⟨C*A,P₀,one_le_mul_of_one_le_of_one_le hC hA,hP₀,?_⟩
  intro P hP q hq θ v hθ
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hφ : 0 < |θ| := abs_pos.mpr hθ
  have hvol := hvolume ε P q |θ| q θ hε hP1 hq hφ le_rfl le_rfl v
  have hmono : (volume (sourceWindow F D.point D.radius P θ q v 1 (ε/7))).toReal ≤
      (volume (window F D.box P (q*θ) v (P^(ε/7)*Vzero P q |θ|))).toReal := by
    apply ENNReal.toReal_mono
      (GradientPhysicalWindow.window_measure_ne_top D hF P (q*θ) hP0
        (mul_ne_zero hq0.ne' hθ) v _)
    exact measure_mono (sourceWindow_subset_window D P q θ (ε/7) v)
  rw [D.weight_eq]
  calc
    _ ≤ C*(P^(-(N : ℝ))+
      (volume (sourceWindow F D.point D.radius P θ q v 1 (ε/7))).toReal) :=
        hlocal P hP q hq0 θ v
    _ ≤ C*(A*P^(-(N : ℝ))+A*P^((10 : ℝ)+ε)*(q/(P*Vzero P q |θ|))^7) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
      exact add_le_add (le_mul_of_one_le_left (Real.rpow_nonneg hP0.le _) hA)
        (hmono.trans hvol)
    _ = _ := by ring

/-- End-to-end existence of the fixed counting weight and integral bound
from rational anisotropy and the single generic oscillatory input. -/
theorem exists_data_and_bound 
    (G : AnisotropicCubic 10) :
    ∃ D : Data (map (algebraMap ℚ ℝ) G.polynomial),
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ C P₀ : ℝ,
        1 ≤ C ∧ 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 1 ≤ q →
        ∀ (θ : ℝ) (v : Fin 10 → ℝ), θ ≠ 0 →
        ‖scaledIntegral (map (algebraMap ℚ ℝ) G.polynomial) D.weight.weight P θ (q⁻¹ • v)‖ ≤
          C*(P^(-(N : ℝ))+P^((10 : ℝ)+ε)*(q/(P*Vzero P q |θ|))^7) := by
  obtain ⟨D⟩ := RealRegularGradientChart.exists_data G
  exact ⟨D,fun ε hε N => exists_bound D (G.homogeneous.map _) ε hε N⟩

end CubicTenVariables.GradientOscillatoryEstimate
