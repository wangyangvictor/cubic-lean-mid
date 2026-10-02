import Mathlib.MeasureTheory.Measure.Prod

/-! A finite family of measurable product-space sets is controlled by the
measure of the outer parameter region, a bound for each fiber, and the number
of nonempty fibers at each outer parameter. All bounds are actual measures;
there is no geometric or analytic estimate assumed implicitly. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteFiberVolumeSum
open MeasureTheory
open scoped ENNReal BigOperators
open Classical
variable {ι E W : Type*} [MeasurableSpace E]

/-- The literal slice obtained by fixing the second coordinate. -/
def fiber (S : Set (E × W)) (w : W) : Set E := {x | (x,w) ∈ S}

/-- A pointwise finite-sum bound. The active-cardinality bound may be a real
number embedded into ENNReal, so no integer ceiling is necessary. -/
theorem sum_fiber_le (μ : Measure E) (T : Finset ι) (S : ι → Set (E × W))
    (w : W) (N M : ℝ≥0∞)
    (hM : ∀ i ∈ T, μ (fiber (S i) w) ≤ M)
    (hN : ((T.filter fun i => (fiber (S i) w).Nonempty).card : ℝ≥0∞) ≤ N) :
    (∑ i ∈ T, μ (fiber (S i) w)) ≤ N*M := by
  classical
  calc
    (∑ i ∈ T, μ (fiber (S i) w)) ≤
        ∑ i ∈ T, if (fiber (S i) w).Nonempty then M else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : (fiber (S i) w).Nonempty
      · simpa only [if_pos h] using hM i hi
      · rw [if_neg h, Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    _ = ((T.filter fun i => (fiber (S i) w).Nonempty).card : ℝ≥0∞)*M := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul]
    _ ≤ N*M := mul_le_mul_left hN M

variable [MeasurableSpace W]

/-- Exact finite Tonelli rearrangement; only measurability and s-finiteness
are required. In particular this identity also allows infinite measures. -/
theorem sum_prod_eq_lintegral (μ : Measure E) (ν : Measure W)
    [SFinite μ] [SFinite ν] (T : Finset ι) (S : ι → Set (E × W))
    (hS : ∀ i ∈ T, MeasurableSet (S i)) :
    (∑ i ∈ T, (μ.prod ν) (S i)) =
      ∫⁻ w, ∑ i ∈ T, μ (fiber (S i) w) ∂ν := by
  have hm : ∀ i ∈ T, Measurable (fun w => μ (fiber (S i) w)) :=
    fun i hi => measurable_measure_prodMk_right (hS i hi)
  rw [lintegral_finset_sum T hm]
  exact Finset.sum_congr rfl fun i hi => Measure.prod_apply_symm (hS i hi)

/-- Uniform fiber size times uniform overlap, integrated over the actual
outer region. The region itself need not be measurable. -/
theorem sum_prod_le (μ : Measure E) (ν : Measure W)
    [SFinite μ] [SFinite ν] (T : Finset ι) (S : ι → Set (E × W))
    (hS : ∀ i ∈ T, MeasurableSet (S i)) (K : Set W)
    (hK : ∀ i ∈ T, S i ⊆ Set.univ ×ˢ K) (N M : ℝ≥0∞)
    (hM : ∀ w ∈ K, ∀ i ∈ T, μ (fiber (S i) w) ≤ M)
    (hN : ∀ w ∈ K,
      ((T.filter fun i => (fiber (S i) w).Nonempty).card : ℝ≥0∞) ≤ N) :
    (∑ i ∈ T, (μ.prod ν) (S i)) ≤ ν K*N*M := by
  classical
  rw [sum_prod_eq_lintegral μ ν T S hS]
  calc
    (∫⁻ w, ∑ i ∈ T, μ (fiber (S i) w) ∂ν) ≤
        ∫⁻ w, K.indicator (fun _ => N*M) w ∂ν := by
      apply lintegral_mono
      intro w
      by_cases hw : w ∈ K
      · rw [Set.indicator_of_mem hw]
        exact sum_fiber_le μ T S w N M (hM w hw) (hN w hw)
      · rw [Set.indicator_of_notMem hw]
        have hf : ∀ i ∈ T, fiber (S i) w = ∅ := by
          intro i hi
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hw (hK i hi hx).2
        have hz : (∑ i ∈ T, μ (fiber (S i) w))=0 :=
          Finset.sum_eq_zero (fun i hi => by rw [hf i hi, measure_empty])
        exact hz.le
    _ ≤ (N*M)*ν K := lintegral_indicator_const_le K (N*M)
    _ = ν K*N*M := by ac_rfl

/-- Real-valued form, with finiteness of every product-set measure derived
from the hypotheses instead of being assumed. The overlap bound uses a real
cardinality, directly accommodating nonintegral bounds. -/
theorem sum_prod_toReal_le (μ : Measure E) (ν : Measure W)
    [SFinite μ] [SFinite ν] (T : Finset ι) (S : ι → Set (E × W))
    (hS : ∀ i ∈ T, MeasurableSet (S i)) (K : Set W)
    (hK : ∀ i ∈ T, S i ⊆ Set.univ ×ˢ K) (hKfinite : ν K ≠ ⊤)
    (N M : ℝ) (hNnonneg : 0 ≤ N) (hMnonneg : 0 ≤ M)
    (hM : ∀ w ∈ K, ∀ i ∈ T, μ (fiber (S i) w) ≤ ENNReal.ofReal M)
    (hN : ∀ w ∈ K,
      ((T.filter fun i => (fiber (S i) w).Nonempty).card : ℝ) ≤ N) :
    (∑ i ∈ T, ((μ.prod ν) (S i)).toReal) ≤ (ν K).toReal*N*M := by
  have hn : ∀ w ∈ K,
      ((T.filter fun i => (fiber (S i) w).Nonempty).card : ℝ≥0∞) ≤
        ENNReal.ofReal N := by
    intro w hw
    exact_mod_cast ENNReal.ofReal_le_ofReal (hN w hw)
  have hb := sum_prod_le μ ν T S hS K hK (ENNReal.ofReal N) (ENNReal.ofReal M) hM hn
  have hr : ν K*ENNReal.ofReal N*ENNReal.ofReal M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hKfinite ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hf : ∀ i ∈ T, (μ.prod ν) (S i) ≠ ⊤ :=
    ENNReal.sum_ne_top.mp (ne_top_of_le_ne_top hr hb)
  rw [← ENNReal.toReal_sum hf]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hNnonneg,
    ENNReal.toReal_ofReal hMnonneg] using ENNReal.toReal_mono hr hb

end CubicTenVariables.FiniteFiberVolumeSum
