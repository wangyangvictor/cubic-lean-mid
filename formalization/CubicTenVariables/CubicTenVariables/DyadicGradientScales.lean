import CubicTenVariables.LocalSupremumNumerics

/-! Uniform comparison of the actual q,theta cutoffs with dyadic R,phi
cutoffs, retaining positive exponent slack for the fixed factors. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DyadicGradientScales
open LocalSupremumNumerics GradientVolumeNumerics

theorem V_le (P R φ q θ : ℝ) (hP : 0 < P) (hR : 0 ≤ R) (_hφ : 0 ≤ φ)
    (_hq : 0 ≤ q) (hqR : q ≤ 2*R) (hθ : |θ| ≤ 2*φ) :
    V P q |θ| ≤ 4*V P R φ := by
  have hm : max 1 (|θ| * P^3) ≤ 2*max 1 (φ*P^3) := by
    apply max_le
    · have h := le_max_left (1:ℝ) (φ*P^3); linarith
    · calc
        _ ≤ 2*φ*P^3 := mul_le_mul_of_nonneg_right hθ (pow_nonneg hP.le 3)
        _ ≤ 2*max 1 (φ*P^3) := by nlinarith [le_max_right (1:ℝ) (φ*P^3)]
  calc
    V P q |θ| ≤ ((2*R)/P)*(2*max 1 (φ*P^3)) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hqR hP.le) hm
        (by positivity) (by positivity)
    _ = 4*V P R φ := by unfold V; ring

theorem Vzero_le (P R φ q θ : ℝ) (hP : 0 < P) (hR : 0 ≤ R) (hφ : 0 ≤ φ)
    (_hq : 0 ≤ q) (hqR : q ≤ 2*R) (hθ : |θ| ≤ 2*φ) :
    Vzero P q |θ| ≤ 4*Vzero P R φ := by
  have hs : Real.sqrt (|θ| * P^3) ≤ 2*Real.sqrt (φ*P^3) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [Real.sq_sqrt (by positivity : 0 ≤ |θ| * P^3),mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ φ*P^3)]
    have h := mul_le_mul_of_nonneg_right hθ (pow_nonneg hP.le 3)
    nlinarith [mul_nonneg hφ (pow_nonneg hP.le 3)]
  have hm : max 1 (Real.sqrt (|θ| * P^3)) ≤ 2*max 1 (Real.sqrt (φ*P^3)) := by
    apply max_le
    · have h := le_max_left (1:ℝ) (Real.sqrt (φ*P^3)); linarith
    · exact hs.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
  calc
    Vzero P q |θ| ≤ ((2*R)/P)*(2*max 1 (Real.sqrt (φ*P^3))) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hqR hP.le) hm
        (by positivity) (by positivity)
    _ = 4*Vzero P R φ := by unfold Vzero; ring

/-- A single threshold absorbs all fixed dyadic comparison factors. -/
theorem exists_threshold (η : ℝ) (hη : 0 < η) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → 4 ≤ P^(η/2) := by
  refine ⟨max 1 ((4:ℝ)^((η/2)⁻¹)),le_max_left _ _,?_⟩
  intro P hP
  exact (Real.rpow_inv_le_iff_of_pos (by norm_num : (0:ℝ) ≤ 4)
    (zero_le_one.trans ((le_max_left _ _).trans hP)) (half_pos hη)).mp
      ((le_max_right _ _).trans hP)

theorem frequency_cutoff_le (η P R φ q θ : ℝ) (_hη : 0 < η)
    (hP : 1 ≤ P) (hR : 0 ≤ R) (hφ : 0 ≤ φ) (hq : 0 ≤ q)
    (hqR : q ≤ 2*R) (hθ : |θ| ≤ 2*φ) (hslack : 4 ≤ P^(η/2)) :
    P^(2*(η/4))*(q/P)*max 1 (|θ| * P^3) ≤ P^η*V P R φ := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hv : 0 ≤ V P R φ := by unfold V; positivity
  have he : P^(η/2)*P^(η/2)=P^η := by rw [← Real.rpow_add hP0]; congr 1; ring
  calc
    _ = P^(η/2)*V P q |θ| := by unfold V; rw [show 2*(η/4)=η/2 by ring]; ring
    _ ≤ P^(η/2)*(4*V P R φ) :=
      mul_le_mul_of_nonneg_left (V_le P R φ q θ hP0 hR hφ hq hqR hθ) (by positivity)
    _ ≤ P^(η/2)*(P^(η/2)*V P R φ) := by gcongr
    _ = _ := by rw [← mul_assoc,he]

theorem gradient_width_le (η P R φ q θ : ℝ) (hη : 0 < η)
    (hP : 1 ≤ P) (hR : 0 ≤ R) (hφ : 0 ≤ φ) (hq : 0 ≤ q)
    (hqR : q ≤ 2*R) (hθ : |θ| ≤ 2*φ) (hslack : 4 ≤ P^(η/2)) :
    P^(η/4)*Vzero P q |θ| ≤ P^η*Vzero P R φ := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hv : 0 ≤ Vzero P R φ := by unfold Vzero; positivity
  have hp : P^(η/4) ≤ P^(η/2) := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have he : P^(η/2)*P^(η/2)=P^η := by rw [← Real.rpow_add hP0]; congr 1; ring
  calc
    _ ≤ P^(η/2)*(4*Vzero P R φ) := mul_le_mul hp
      (Vzero_le P R φ q θ hP0 hR hφ hq hqR hθ)
      (by unfold Vzero; positivity) (by positivity)
    _ ≤ P^(η/2)*(P^(η/2)*Vzero P R φ) := by gcongr
    _ = _ := by rw [← mul_assoc,he]

end CubicTenVariables.DyadicGradientScales
