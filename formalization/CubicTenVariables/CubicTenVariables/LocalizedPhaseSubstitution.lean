import CubicTenVariables.DyadicPhaseSubstitution

/-! The actual change of phase for a denominator within a fixed multiple
of the dyadic modulus. This retains the original R in the final phase. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedPhaseSubstitution
open MeasureTheory Set DyadicPhaseSubstitution

theorem transformed_annulus_subset (R ℓ φ κ : ℝ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ) (hℓR : ℓ ≤ 2*(κ*R)) (hφ : 0 ≤ φ) :
    annulus ((ℓ/R)*φ) ((ℓ/R)*(2*φ)) ⊆ annulus φ (4*κ*φ) := by
  have hlo : 1 ≤ ℓ/R := (one_le_div hR).mpr hRℓ
  have hhi : ℓ/R ≤ 2*κ := (div_le_iff₀ hR).mpr (by nlinarith only [hℓR])
  intro τ hτ
  refine ⟨?_,?_⟩
  · exact (by nlinarith only [mul_le_mul_of_nonneg_right hlo hφ] : φ ≤ (ℓ/R)*φ).trans_lt hτ.1
  · apply hτ.2.trans
    nlinarith only [mul_le_mul_of_nonneg_right hhi (by positivity : 0 ≤ 2*φ)]

/-- Exact substitution and monotonicity for the true denominator ℓ.
The Jacobian and normalization both decrease because ℓ≥R. -/
theorem weighted_integral_le (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (R ℓ φ κ : ℝ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ) (hℓR : ℓ ≤ 2*(κ*R)) (hφ : 0 ≤ φ)
    (hI : IntegrableOn f (annulus φ (4*κ*φ))) :
    (ℓ^10)⁻¹*(∫ θ in annulus φ (2*φ), f (ℓ*θ/R)) ≤
      (R^10)⁻¹*(∫ τ in annulus φ (4*κ*φ), f τ) := by
  have hℓ : 0 < ℓ := hR.trans_le hRℓ
  rw [DyadicPhaseSubstitution.integral_substitution f hf hfn R ℓ φ hR hℓ]
  have hint : (∫ τ in annulus ((ℓ/R)*φ) ((ℓ/R)*(2*φ)), f τ) ≤
      ∫ τ in annulus φ (4*κ*φ), f τ :=
    setIntegral_mono_set hI (Filter.Eventually.of_forall hfn)
      (Filter.Eventually.of_forall (transformed_annulus_subset R ℓ φ κ hR hRℓ hℓR hφ))
  have hinv : (ℓ^10)⁻¹ ≤ (R^10)⁻¹ :=
    inv_anti₀ (pow_pos hR 10) (pow_le_pow_left₀ hR.le hRℓ 10)
  have hnonneg : 0 ≤ ∫ τ in annulus ((ℓ/R)*φ) ((ℓ/R)*(2*φ)), f τ :=
    integral_nonneg hfn
  calc
    _ ≤ (R^10)⁻¹*((R/ℓ)*(∫ τ in annulus ((ℓ/R)*φ) ((ℓ/R)*(2*φ)), f τ)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg (div_nonneg hR.le hℓ.le) hnonneg)
    _ ≤ (R^10)⁻¹*(∫ τ in annulus ((ℓ/R)*φ) ((ℓ/R)*(2*φ)), f τ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left hnonneg ((div_le_one hℓ).mpr hRℓ)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)

theorem volume_expanded_le (φ κ : ℝ) :
    volume (annulus φ (4*κ*φ)) ≤ ENNReal.ofReal (8*κ*φ) := by
  have hsub : annulus φ (4*κ*φ) ⊆ Icc (-4*κ*φ) (4*κ*φ) := by
    intro τ hτ
    have h := abs_le.mp hτ.2
    exact ⟨by linarith only [h.1],h.2⟩
  have h := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at h
  simpa only [show (4*κ*φ)-(-4*κ*φ)=8*κ*φ by ring] using h

theorem volume_expanded_ne_top (φ κ : ℝ) : volume (annulus φ (4*κ*φ)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_expanded_le φ κ)

end CubicTenVariables.LocalizedPhaseSubstitution
