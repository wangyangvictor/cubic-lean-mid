import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

/-! Absolute summability of integral masses justifies integration of a
countable series, including restriction to a smaller set and multiplication
by a bounded measurable kernel. All convergence is proved from the stated
individual integrability and summable masses. No literature input is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SummableIntegralMajorant
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
variable {ι α E : Type*} [Countable ι] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem finite_enorm_mass (μ : Measure α) (f : ι → α → E)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    (∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ) < ⊤ := by
  rw [lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)]
  have he (i : ι) : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf i).norm, ENNReal.coe_nnreal_eq,
      coe_nnnorm, Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f i x)))]
    simp only [coe_nnnorm]
  simp_rw [he]
  exact lt_top_iff_ne_top.mpr
    (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs))

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Summable integral masses force genuine absolute convergence almost
everywhere; the totalized `tsum` convention is not used to bypass convergence. -/
theorem summable_norm_ae (μ : Measure α) (f : ι → α → E)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖) := by
  have hfinite := finite_enorm_mass μ f hf hs
  have hm := AEMeasurable.ennreal_tsum (fun i => (hf i).aestronglyMeasurable.enorm)
  filter_upwards [ae_lt_top' hm hfinite.ne] with x hx
  exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hx.ne

omit [NormedSpace ℝ E] in
/-- Integrability of the actual pointwise sum follows from the masses. -/
theorem integrable_tsum (μ : Measure α) (f : ι → α → E)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  classical
  have hae := summable_norm_ae μ f hf hs
  refine ⟨aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (fun s => s.aestronglyMeasurable_fun_sum (fun i _ => (hf i).aestronglyMeasurable))
    (hae.mono (fun x hx => hx.of_norm.hasSum)), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)).trans_lt
    (finite_enorm_mass μ f hf hs)

omit [NormedSpace ℝ E] in
/-- The integral of the norm of the sum is bounded by the sum of masses. -/
theorem integral_norm_tsum_le (μ : Measure α) (f : ι → α → E)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    (∫ x, ‖∑' i, f i x‖ ∂μ) ≤ ∑' i, ∫ x, ‖f i x‖ ∂μ := by
  have hsn : Summable (fun i => ∫ x, ‖‖f i x‖‖ ∂μ) := by
    simpa only [norm_norm] using hs
  have hn := integrable_tsum μ (fun i x => ‖f i x‖) (fun i => (hf i).norm) hsn
  rw [integral_tsum_of_summable_integral_norm (fun i => (hf i).norm) hsn]
  exact integral_mono_ae (integrable_tsum μ f hf hs).norm hn
    ((summable_norm_ae μ f hf hs).mono (fun _ hx => norm_tsum_le_tsum_norm hx))

/-- In particular, integrating a countable complex series costs at most its
summable individual integral masses. -/
theorem norm_integral_tsum_le (μ : Measure α) (f : ι → α → E)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ‖∫ x, ∑' i, f i x ∂μ‖ ≤ ∑' i, ∫ x, ‖f i x‖ ∂μ :=
  (norm_integral_le_integral_norm _).trans (integral_norm_tsum_le μ f hf hs)

/-- A bounded measurable kernel and clipping to a smaller set preserve the
same majorant, with the explicit kernel bound as the only new factor. -/
theorem clipped_kernel {S T : Set ℝ} (hST : S ⊆ T)
    (f : ι → ℝ → ℂ) (hf : ∀ i, IntegrableOn (f i) T)
    (hs : Summable (fun i => ∫ x in T, ‖f i x‖))
    (k : ℝ → ℂ) (hk : AEStronglyMeasurable k (volume.restrict S))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ᵐ x ∂volume.restrict S, ‖k x‖ ≤ K) :
    IntegrableOn (fun x => k x * ∑' i, f i x) S ∧
      ‖∫ x in S, k x * ∑' i, f i x‖ ≤ K * ∑' i, ∫ x in T, ‖f i x‖ := by
  have hsum : IntegrableOn (fun x => ∑' i, f i x) T :=
    integrable_tsum (volume.restrict T) f hf hs
  have hsumS : IntegrableOn (fun x => ∑' i, f i x) S := hsum.mono_set hST
  have hprod := hsumS.bdd_mul hk hbound
  refine ⟨hprod, ?_⟩
  calc
    ‖∫ x in S, k x * ∑' i, f i x‖ ≤ ∫ x in S, ‖k x * ∑' i, f i x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in S, K * ‖∑' i, f i x‖ := by
      apply integral_mono_ae hprod.norm (hsumS.norm.const_mul K)
      filter_upwards [hbound] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = K * ∫ x in S, ‖∑' i, f i x‖ := integral_const_mul K _
    _ ≤ K * ∫ x in T, ‖∑' i, f i x‖ := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact setIntegral_mono_set hsum.norm (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (Filter.Eventually.of_forall hST)
    _ ≤ K * ∑' i, ∫ x in T, ‖f i x‖ :=
      mul_le_mul_of_nonneg_left (integral_norm_tsum_le (volume.restrict T) f hf hs) hK

/-- Pointwise bounded-kernel version for applying the estimate directly to
an arc clipped out of a larger shell. No measurability of the sets is needed. -/
theorem clipped_kernel_bound {S T : Set ℝ} (hST : S ⊆ T)
    (f : ι → ℝ → ℂ) (hf : ∀ i, IntegrableOn (f i) T)
    (hs : Summable (fun i => ∫ x in T, ‖f i x‖))
    (k : ℝ → ℂ) (hk : Measurable k)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x ∈ S, ‖k x‖ ≤ K) :
    IntegrableOn (fun x => k x * ∑' i, f i x) S ∧
      ‖∫ x in S, k x * ∑' i, f i x‖ ≤ K * ∑' i, ∫ x in T, ‖f i x‖ := by
  apply clipped_kernel hST f hf hs k hk.aestronglyMeasurable K hK
  exact (ae_restrict_iff (measurableSet_le hk.norm measurable_const)).mpr
    (Filter.Eventually.of_forall hbound)

end CubicTenVariables.SummableIntegralMajorant
