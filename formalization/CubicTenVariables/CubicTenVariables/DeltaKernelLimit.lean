import CubicTenVariables.RescaledDeltaArc
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The rescaled delta kernel tends to one against every integrable function.
The cutoff is the actual rescaled open arc. All estimates are derived from
the explicit kernel estimates; there is no additional literature premise. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DeltaKernelLimit
open Filter MeasureTheory
open scoped Topology

/-- Extend the actual clipped integrand by zero to the whole real line. -/
def cutKernel (p : ℕ → ℕ → ℝ → ℂ) (P : ℝ) (Q q : ℕ) (η : ℝ)
    (J : ℝ → ℂ) : ℝ → ℂ :=
  (RescaledDeltaArc.domain P Q q η).indicator (fun β => p Q q (β/P^3)*J β)

theorem integral_cutKernel (p : ℕ → ℕ → ℝ → ℂ) (P : ℝ)
    (Q q : ℕ) (η : ℝ) (J : ℝ → ℂ) :
    (∫ β, cutKernel p P Q q η J β) = RescaledDeltaArc.integral p P Q q η J :=
  integral_indicator (RescaledDeltaArc.measurableSet_domain P Q q η)

/-- The small coordinate needed for the near-one estimate follows from the
single scale ratio used in the main-term limit. -/
theorem coordinate_lt (P Q β : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (h : |β| *(Q^2/P^3) < 1) : |β/P^3| < Q^(-(2:ℝ)) := by
  have hh : (|β| * Q^2)/P^3 < 1 := by simpa only [mul_div_assoc] using h
  have hn : |β| *Q^2 < P^3 := by
    simpa using (div_lt_iff₀ (pow_pos hP 3)).mp hh
  rw [abs_div, abs_of_pos (pow_pos hP 3), Real.rpow_neg hQ.le,
    show (2:ℝ) = (2:ℕ) by norm_num, Real.rpow_natCast, inv_eq_one_div]
  exact (div_lt_div_iff₀ (pow_pos hP 3) (pow_pos hQ 2)).mpr (by simpa using hn)

/-- Once Q is at least the fixed modulus, the near-one neighborhood lies in
the actual major arc, for every nonnegative arc parameter. -/
theorem near_one_subset_arc (Q q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (η : ℝ) (hη : 0 ≤ η) :
    (Q : ℝ)^(-(2:ℝ)) ≤ ((q:ℝ)*(Q:ℝ))^(-1+η) := by
  have hqr : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast le_trans hq hqQ
  have hqQr : (q:ℝ) ≤ Q := by exact_mod_cast hqQ
  have hbase : 1 ≤ (q:ℝ)*(Q:ℝ) := one_le_mul_of_one_le_of_one_le hqr hQr
  calc
    (Q:ℝ)^(-(2:ℝ)) = 1/(Q:ℝ)^2 := by
      rw [Real.rpow_neg (by positivity), show (2:ℝ) = (2:ℕ) by norm_num, Real.rpow_natCast, inv_eq_one_div]
    _ ≤ 1/((q:ℝ)*(Q:ℝ)) := one_div_le_one_div_of_le (by positivity)
      (by nlinarith only [hQr, hqQr])
    _ = ((q:ℝ)*(Q:ℝ))^(-1:ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ ((q:ℝ)*(Q:ℝ))^(-1+η) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)

theorem eventually_coordinate_lt (P Q : ℕ → ℕ)
    (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (β : ℝ) : ∀ᶠ k in atTop, |β/(P k:ℝ)^3| < (Q k:ℝ)^(-(2:ℝ)) := by
  have ht : Tendsto (fun k => |β| *((Q k:ℝ)^2/(P k:ℝ)^3)) atTop (𝓝 0) := by
    simpa using hratio.const_mul |β|
  filter_upwards [hP.eventually (eventually_ge_atTop 1),
    hQ.eventually (eventually_ge_atTop 1), ht.eventually_lt_const (by norm_num : (0:ℝ)<1)]
    with k hkP hkQ hk
  exact coordinate_lt _ _ _ (by exact_mod_cast (by omega : 0<P k))
    (by exact_mod_cast (by omega : 0<Q k)) hk

/-- Every fixed real frequency eventually belongs to the literal rescaled arc. -/
theorem eventually_mem_domain (P Q : ℕ → ℕ)
    (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (q : ℕ) (hq : 1 ≤ q) (η : ℝ) (hη : 0 ≤ η) (β : ℝ) :
    ∀ᶠ k in atTop, β ∈ RescaledDeltaArc.domain (P k:ℝ) (Q k) q η := by
  filter_upwards [eventually_coordinate_lt P Q hP hQ hratio β,
    hP.eventually (eventually_ge_atTop 1), hQ.eventually (eventually_ge_atTop q)]
    with k hk hkP hkQ
  have hPk : (0:ℝ)<P k := by exact_mod_cast (by omega : 0<P k)
  have hh := hk.trans_le (near_one_subset_arc (Q k) q hq hkQ η hη)
  rw [abs_div, abs_of_pos (pow_pos hPk 3)] at hh
  change |β| < _
  simpa [mul_comm] using (div_lt_iff₀ (pow_pos hPk 3)).mp hh

/-- Pointwise convergence of the actual kernel, with the fixed-modulus
condition derived eventually from Q tending to infinity. -/
theorem tendsto_kernel (p : ℕ → ℕ → ℝ → ℂ) (hp : DeltaMethod.KernelEstimates 1 p)
    (P Q : ℕ → ℕ) (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) :
    Tendsto (fun k => p (Q k) q (β/(P k:ℝ)^3)) atTop (𝓝 1) := by
  obtain ⟨C, hC, hb⟩ := hp.near_one 1 le_rfl
  have hQc : Tendsto (fun k => (Q k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hQ
  have ht : Tendsto (fun k => C*((q:ℝ)/(Q k:ℝ))) atTop (𝓝 0) := by
    simpa using (hQc.const_div_atTop (q:ℝ)).const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [eventually_coordinate_lt P Q hP hQ hratio β,
    hQ.eventually (eventually_ge_atTop q)] with k hk hkQ
  simpa using hb (Q k) (le_trans hq hkQ) q hq hkQ (β/(P k:ℝ)^3) hk.le

/-- Pointwise convergence includes the actual moving-domain indicator. -/
theorem tendsto_cutKernel (p : ℕ → ℕ → ℝ → ℂ) (hp : DeltaMethod.KernelEstimates 1 p)
    (P Q : ℕ → ℕ) (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (q : ℕ) (hq : 1 ≤ q) (η : ℝ) (hη : 0 ≤ η) (J : ℝ → ℂ) (β : ℝ) :
    Tendsto (fun k => cutKernel p (P k:ℝ) (Q k) q η J β) atTop (𝓝 (J β)) := by
  have ht := (tendsto_kernel p hp P Q hP hQ hratio q hq β).mul_const (J β)
  apply (show Tendsto (fun k => p (Q k) q (β/(P k:ℝ)^3)*J β)
    atTop (𝓝 (J β)) by simpa using ht).congr'
  filter_upwards [eventually_mem_domain P Q hP hQ hratio q hq η hη β] with k hk
  simp [cutKernel, hk]

theorem norm_cutKernel_le (p : ℕ → ℕ → ℝ → ℂ) (P : ℝ) (Q q : ℕ)
    (η : ℝ) (J : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ θ, ‖p Q q θ‖ ≤ C) (β : ℝ) :
    ‖cutKernel p P Q q η J β‖ ≤ C*‖J β‖ := by
  by_cases hm : β ∈ RescaledDeltaArc.domain P Q q η
  · simp only [cutKernel, Set.indicator_of_mem hm, norm_mul]
    exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)
  · simp only [cutKernel, Set.indicator_of_notMem hm, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

/-- The clipped integrals used below are genuine integrals of integrable
functions, for every admissible fixed modulus and every physical scale. -/
theorem integrable_cutKernel (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (P : ℝ) (Q q : ℕ)
    (hQ : 1 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (η : ℝ)
    (J : ℝ → ℂ) (hJ : Integrable J) : Integrable (cutKernel p P Q q η J) := by
  obtain ⟨C, hC, hb⟩ := hp.bounded
  have hc : Continuous (fun β : ℝ => p Q q (β/P^3)) :=
    (hp.smooth Q hQ q hq hqQ).continuous.comp (by fun_prop)
  apply (hJ.norm.const_mul C).mono'
  · exact (hc.aestronglyMeasurable.mul hJ.aestronglyMeasurable).indicator
      (RescaledDeltaArc.measurableSet_domain _ _ _ _)
  · exact Eventually.of_forall (norm_cutKernel_le p P Q q η J C
      (by linarith) (hb Q hQ q hq hqQ))

/-- A single bound works before all varying physical scales, moduli and
arc parameters. This also supplies domination for a subsequent modulus sum. -/
theorem exists_uniform_integral_bound (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (J : ℝ → ℂ) (hJ : Integrable J) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℝ) (Q q : ℕ),
      1 ≤ Q → 1 ≤ q → q ≤ Q → ∀ η : ℝ,
      ‖RescaledDeltaArc.integral p P Q q η J‖ ≤ C*(∫ β, ‖J β‖) := by
  obtain ⟨C, hC, hb⟩ := hp.bounded
  refine ⟨C, hC, ?_⟩
  intro P Q q hQ hq hqQ η
  rw [← integral_cutKernel]
  calc
    ‖∫ β, cutKernel p P Q q η J β‖ ≤ ∫ β, C*‖J β‖ :=
      norm_integral_le_of_norm_le (hJ.norm.const_mul C)
        (Eventually.of_forall (norm_cutKernel_le p P Q q η J C
          (by linarith) (hb Q hQ q hq hqQ)))
    _ = C*(∫ β, ‖J β‖) := integral_const_mul _ _

/-- Dominated convergence for the literal rescaled clipped kernel. Constants
and smoothness come from hp; integrability of J is the only analytic premise
on the limiting function. In particular, no continuity of J is required. -/
theorem tendsto_integral (p : ℕ → ℕ → ℝ → ℂ) (hp : DeltaMethod.KernelEstimates 1 p)
    (q : ℕ) (hq : 1 ≤ q) (η : ℝ) (hη : 0 ≤ η)
    (P Q : ℕ → ℕ) (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (J : ℝ → ℂ) (hJ : Integrable J) :
    Tendsto (fun k => RescaledDeltaArc.integral p (P k:ℝ) (Q k) q η J)
      atTop (𝓝 (∫ β, J β)) := by
  obtain ⟨C, hC, hb⟩ := hp.bounded
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable (cutKernel p (P k:ℝ) (Q k) q η J) := by
    filter_upwards [hQ.eventually (eventually_ge_atTop q)] with k hk
    have hc : Continuous (fun β : ℝ => p (Q k) q (β/(P k:ℝ)^3)) :=
      (hp.smooth (Q k) (le_trans hq hk) q hq hk).continuous.comp (by fun_prop)
    exact (hc.aestronglyMeasurable.mul hJ.aestronglyMeasurable).indicator
      (RescaledDeltaArc.measurableSet_domain _ _ _ _)
  have hbound : ∀ᶠ k in atTop, ∀ᵐ β, ‖cutKernel p (P k:ℝ) (Q k) q η J β‖ ≤ C*‖J β‖ := by
    filter_upwards [hQ.eventually (eventually_ge_atTop q)] with k hk
    apply Eventually.of_forall
    intro β
    by_cases hm : β ∈ RescaledDeltaArc.domain (P k:ℝ) (Q k) q η
    · simp only [cutKernel, Set.indicator_of_mem hm, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb (Q k) (le_trans hq hk) q hq hk _) (norm_nonneg _)
    · simp only [cutKernel, Set.indicator_of_notMem hm, norm_zero]
      exact mul_nonneg (by linarith) (norm_nonneg _)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun β => C*‖J β‖)
    hmeas hbound (hJ.norm.const_mul C)
    (Eventually.of_forall (tendsto_cutKernel p hp P Q hP hQ hratio q hq η hη J))
  simpa only [integral_cutKernel] using ht

end CubicTenVariables.DeltaKernelLimit
