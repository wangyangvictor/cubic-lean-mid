import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact dyadic phase substitution and enlargement of the resulting real
annulus. Real-valued inequalities retain an explicit integrability hypothesis
on the expanded annulus; the nonnegative-integral version permits infinity. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.DyadicPhaseSubstitution
open MeasureTheory Set
open scoped ENNReal

/-- The lower endpoint is excluded and the upper endpoint included. -/
def annulus (lo hi : ℝ) : Set ℝ := {θ | lo < |θ| ∧ |θ| ≤ hi}

theorem measurableSet_annulus (lo hi : ℝ) : MeasurableSet (annulus lo hi) :=
  ((isOpen_lt continuous_const continuous_abs).measurableSet).inter
    (isClosed_le continuous_abs continuous_const).measurableSet

theorem preimage_annulus_mul (s lo hi : ℝ) (hs : 0 < s) :
    (fun θ : ℝ => s*θ) ⁻¹' annulus (s*lo) (s*hi) = annulus lo hi := by
  ext θ
  simp only [annulus,mem_preimage,mem_setOf_eq,abs_mul,abs_of_pos hs,
    mul_lt_mul_iff_right₀ hs,mul_le_mul_iff_right₀ hs]

/-- Exact Jacobian before any enlargement, for a nonnegative measurable function. -/
theorem lintegral_substitution (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (R q φ : ℝ) (hR : 0 < R) (hq : 0 < q) :
    (∫⁻ θ in annulus φ (2*φ), f (q*θ/R)) = ENNReal.ofReal (R/q)*
      ∫⁻ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ := by
  have hs : 0 < q/R := div_pos hq hR
  have h := setLIntegral_map (μ := (volume : Measure ℝ))
    (g := fun θ : ℝ => (q/R)*θ)
    (s := annulus ((q/R)*φ) ((q/R)*(2*φ)))
    (measurableSet_annulus _ _) hf (measurable_const.mul measurable_id)
  rw [preimage_annulus_mul _ _ _ hs,Real.map_volume_mul_left hs.ne',
    setLIntegral_smul_measure] at h
  have hinv : |(q/R)⁻¹|=R/q := by rw [inv_div,abs_of_pos (div_pos hR hq)]
  simpa only [hinv,smul_eq_mul,mul_div_assoc,div_mul_eq_mul_div] using h.symm

/-- The same exact factor in the real integral; the inequality below also
requires actual finite integrability, so no infinite-integral convention is used. -/
theorem integral_substitution (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (R q φ : ℝ) (hR : 0 < R) (hq : 0 < q) :
    (∫ θ in annulus φ (2*φ), f (q*θ/R)) = (R/q)*
      ∫ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ := by
  have h := congrArg ENNReal.toReal
    (lintegral_substitution (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal R q φ hR hq)
  have hcomp : Measurable (fun θ : ℝ => f (q*θ/R)) :=
    hf.comp ((measurable_const.mul measurable_id).div_const R)
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun θ : ℝ => f (q*θ/R))
    (Filter.Eventually.of_forall (fun x => hfn _)) hcomp.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (f := f) (Filter.Eventually.of_forall hfn)
      hf.aestronglyMeasurable]
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_nonneg hR.le hq.le)] using h

/-- The transformed shell lies in the fixed expanded shell for R ≤ q ≤ 2R. -/
theorem transformed_annulus_subset (R q φ : ℝ) (hR : 0 < R)
    (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ) :
    annulus ((q/R)*φ) ((q/R)*(2*φ)) ⊆ annulus φ (4*φ) := by
  have hs1 : 1 ≤ q/R := (one_le_div hR).mpr hRq
  have hs2 : q/R ≤ 2 := (div_le_iff₀ hR).mpr hqR
  intro τ hτ
  refine ⟨lt_of_le_of_lt ?_ hτ.1,hτ.2.trans ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hφ
  · calc
      _ ≤ 2*(2*φ) := mul_le_mul_of_nonneg_right hs2 (by positivity)
      _ = _ := by ring

/-- Nonnegative integrals can be enlarged without any finiteness hypothesis. -/
theorem lintegral_le (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (R q φ : ℝ) (hR : 0 < R) (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ) :
    (∫⁻ θ in annulus φ (2*φ), f (q*θ/R)) ≤ ∫⁻ τ in annulus φ (4*φ), f τ := by
  have hq : 0 < q := hR.trans_le hRq
  rw [lintegral_substitution f hf R q φ hR hq]
  have hr : ENNReal.ofReal (R/q) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal ((div_le_one hq).mpr hRq)
  calc
    _ ≤ 1*(∫⁻ τ in annulus φ (4*φ), f τ) :=
      mul_le_mul' hr (lintegral_mono_set (transformed_annulus_subset R q φ hR hRq hqR hφ))
    _ = _ := one_mul _

/-- The ten-dimensional q weight is also monotone throughout the dyadic range. -/
theorem weighted_lintegral_le (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (R q φ : ℝ) (hR : 0 < R) (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ) :
    ENNReal.ofReal ((q^10)⁻¹)*(∫⁻ θ in annulus φ (2*φ), f (q*θ/R)) ≤
      ENNReal.ofReal ((R^10)⁻¹)*(∫⁻ τ in annulus φ (4*φ), f τ) := by
  apply mul_le_mul' _ (lintegral_le f hf R q φ hR hRq hqR hφ)
  apply ENNReal.ofReal_le_ofReal
  exact inv_anti₀ (pow_pos hR 10) (pow_le_pow_left₀ hR.le hRq 10)

/-- Finite integrability of the pulled-back function follows from the single
expanded-shell integrability hypothesis. -/
theorem integrableOn_substitution (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (R q φ : ℝ) (hR : 0 < R)
    (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ)
    (hI : IntegrableOn f (annulus φ (4*φ))) :
    IntegrableOn (fun θ => f (q*θ/R)) (annulus φ (2*φ)) := by
  have hcomp : Measurable (fun θ : ℝ => f (q*θ/R)) :=
    hf.comp ((measurable_const.mul measurable_id).div_const R)
  apply (lintegral_ofReal_ne_top_iff_integrable hcomp.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => hfn _))).mp
  have hfinite := (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfn)).mpr hI
  exact ne_top_of_le_ne_top hfinite
    (lintegral_le (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal R q φ hR hRq hqR hφ)

/-- The literal real dyadic estimate, with one explicit integrability
hypothesis on the expanded shell and no unproved change-of-variable input. -/
theorem weighted_integral_le (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (R q φ : ℝ) (hR : 0 < R)
    (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ)
    (hI : IntegrableOn f (annulus φ (4*φ))) :
    (q^10)⁻¹*(∫ θ in annulus φ (2*φ), f (q*θ/R)) ≤
      (R^10)⁻¹*(∫ τ in annulus φ (4*φ), f τ) := by
  have hq : 0 < q := hR.trans_le hRq
  rw [integral_substitution f hf hfn R q φ hR hq]
  have hint : (∫ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ) ≤
      ∫ τ in annulus φ (4*φ), f τ :=
    setIntegral_mono_set hI (Filter.Eventually.of_forall hfn)
      (Filter.Eventually.of_forall (transformed_annulus_subset R q φ hR hRq hqR hφ))
  have hinv : (q^10)⁻¹ ≤ (R^10)⁻¹ :=
    inv_anti₀ (pow_pos hR 10) (pow_le_pow_left₀ hR.le hRq 10)
  have hnonneg : 0 ≤ ∫ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ :=
    integral_nonneg hfn
  calc
    _ ≤ (R^10)⁻¹*((R/q)*(∫ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg (div_nonneg hR.le hq.le) hnonneg)
    _ ≤ (R^10)⁻¹*(∫ τ in annulus ((q/R)*φ) ((q/R)*(2*φ)), f τ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left hnonneg ((div_le_one hq).mpr hRq)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (by positivity)

/-- A simple finite-volume enclosure, sufficient for integrating uniform errors. -/
theorem volume_expanded_le (φ : ℝ) (_hφ : 0 ≤ φ) :
    volume (annulus φ (4*φ)) ≤ ENNReal.ofReal (8*φ) := by
  have hsub : annulus φ (4*φ) ⊆ Icc (-4*φ) (4*φ) := by
    intro τ hτ
    have h := abs_le.mp hτ.2
    exact ⟨by linarith [h.1],h.2⟩
  have h := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at h
  simpa only [show (4*φ)-(-4*φ)=8*φ by ring] using h

theorem volume_expanded_ne_top (φ : ℝ) (hφ : 0 ≤ φ) :
    volume (annulus φ (4*φ)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (volume_expanded_le φ hφ)

/-- A measurable function bounded on the fixed expanded shell has the
integrability needed by the real-valued substitution inequality. -/
theorem integrableOn_expanded_of_bound (f : ℝ → ℝ) (hf : Measurable f)
    (φ : ℝ) (hφ : 0 ≤ φ) (M : ℝ)
    (hb : ∀ x ∈ annulus φ (4*φ), |f x| ≤ M) :
    IntegrableOn f (annulus φ (4*φ)) := by
  have hconst : IntegrableOn (fun _ : ℝ => M) (annulus φ (4*φ)) :=
    integrableOn_const (volume_expanded_ne_top φ hφ)
  apply hconst.mono' hf.aestronglyMeasurable
  apply (ae_restrict_iff' (measurableSet_annulus _ _)).mpr
  exact Filter.Eventually.of_forall (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx)

/-- The real dyadic inequality with integrability discharged from boundedness. -/
theorem weighted_integral_le_of_bound (f : ℝ → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (R q φ : ℝ) (hR : 0 < R)
    (hRq : R ≤ q) (hqR : q ≤ 2*R) (hφ : 0 ≤ φ)
    (M : ℝ) (hb : ∀ x ∈ annulus φ (4*φ), |f x| ≤ M) :
    (q^10)⁻¹*(∫ θ in annulus φ (2*φ), f (q*θ/R)) ≤
      (R^10)⁻¹*(∫ τ in annulus φ (4*φ), f τ) :=
  weighted_integral_le f hf hfn R q φ hR hRq hqR hφ
    (integrableOn_expanded_of_bound f hf φ hφ M hb)

end CubicTenVariables.DyadicPhaseSubstitution
