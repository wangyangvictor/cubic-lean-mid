import CubicTenVariables.DeltaKernelLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-! Sum the actual rescaled delta-kernel limits over the moduli. Absolute
convergence of the coefficient series remains an explicit hypothesis.
The finite cutoff is exactly 1 <= q <= Q; no arithmetic estimate is assumed
or concealed in this generic analytic assembly. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.DeltaKernelSeriesLimit
open Filter MeasureTheory
open scoped Topology BigOperators

def cutoffTerm (p : ℕ → ℕ → ℝ → ℂ) (a : ℕ → ℂ) (P : ℝ)
    (Q : ℕ) (η : ℝ) (J : ℝ → ℂ) (q : ℕ) : ℂ :=
  if q ∈ Finset.Icc 1 Q then a q * RescaledDeltaArc.integral p P Q q η J else 0

theorem tsum_cutoffTerm (p : ℕ → ℕ → ℝ → ℂ) (a : ℕ → ℂ) (P : ℝ)
    (Q : ℕ) (η : ℝ) (J : ℝ → ℂ) :
    (∑' q, cutoffTerm p a P Q η J q) =
      ∑ q ∈ Finset.Icc 1 Q, a q * RescaledDeltaArc.integral p P Q q η J := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, cutoffTerm p a P Q η J q :=
      tsum_eq_sum (fun q hq => if_neg hq)
    _ = _ := Finset.sum_congr rfl fun q hq => if_pos hq

/-- A fixed modulus eventually enters the genuine finite cutoff. The q=0
case uses the explicit zero-coefficient hypothesis. -/
theorem tendsto_cutoffTerm (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (η : ℝ) (hη : 0 ≤ η) (P Q : ℕ → ℕ)
    (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (J : ℝ → ℂ) (hJ : Integrable J) (q : ℕ) :
    Tendsto (fun k => cutoffTerm p a (P k:ℝ) (Q k) η J q)
      atTop (𝓝 (a q * ∫ β, J β)) := by
  by_cases hq : q = 0
  · subst q
    simpa only [cutoffTerm,Finset.mem_Icc,show ¬ 1 ≤ (0:ℕ) by omega,
      false_and,ite_false,ha0,zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
  · have hq1 : 1 ≤ q := by omega
    apply ((DeltaKernelLimit.tendsto_integral p hp q hq1 η hη
      P Q hP hQ hratio J hJ).const_mul (a q)).congr'
    filter_upwards [hQ.eventually (eventually_ge_atTop q)] with k hk
    simp only [cutoffTerm,Finset.mem_Icc,hq1,hk,and_self,ite_true]

/-- The cutoff series has a summable majorant uniform in every scale.
Terms outside 1 <= q <= Q vanish, so no kernel bound at q=0 is needed. -/
theorem exists_summable_bound (p : ℕ → ℕ → ℝ → ℂ)
    (hp : DeltaMethod.KernelEstimates 1 p) (a : ℕ → ℂ)
    (ha : Summable (fun q => ‖a q‖)) (J : ℝ → ℂ) (hJ : Integrable J) :
    ∃ bound : ℕ → ℝ, Summable bound ∧
      ∀ (P : ℝ) (Q : ℕ) (η : ℝ) (q : ℕ),
        ‖cutoffTerm p a P Q η J q‖ ≤ bound q := by
  obtain ⟨C,hC,hb⟩ := DeltaKernelLimit.exists_uniform_integral_bound p hp J hJ
  refine ⟨fun q => ‖a q‖*(C*(∫ β, ‖J β‖)),ha.mul_right _,?_⟩
  intro P Q η q
  by_cases hq : q ∈ Finset.Icc 1 Q
  · have hh := Finset.mem_Icc.mp hq
    simp only [cutoffTerm,if_pos hq,norm_mul]
    exact mul_le_mul_of_nonneg_left (hb P Q q (hh.1.trans hh.2) hh.1 hh.2 η)
      (norm_nonneg _)
  · simp only [cutoffTerm,if_neg hq,norm_zero]
    exact mul_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans hC)
      (integral_nonneg fun _ => norm_nonneg _))

/-- Absolute coefficient summability permits the literal finite modulus
sum to converge to the product of the full series and limiting integral. -/
theorem tendsto_sum (p : ℕ → ℕ → ℝ → ℂ) (hp : DeltaMethod.KernelEstimates 1 p)
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (ha : Summable (fun q => ‖a q‖))
    (η : ℝ) (hη : 0 ≤ η) (P Q : ℕ → ℕ)
    (hP : Tendsto P atTop atTop) (hQ : Tendsto Q atTop atTop)
    (hratio : Tendsto (fun k => (Q k:ℝ)^2/(P k:ℝ)^3) atTop (𝓝 0))
    (J : ℝ → ℂ) (hJ : Integrable J) :
    Tendsto (fun k => ∑ q ∈ Finset.Icc 1 (Q k),
      a q * RescaledDeltaArc.integral p (P k:ℝ) (Q k) q η J)
      atTop (𝓝 ((∑' q, a q)*(∫ β, J β))) := by
  obtain ⟨bound,hbound,hb⟩ := exists_summable_bound p hp a ha J hJ
  have ht := tendsto_tsum_of_dominated_convergence hbound
    (tendsto_cutoffTerm p hp a ha0 η hη P Q hP hQ hratio J hJ)
    (Eventually.of_forall fun k q => hb (P k:ℝ) (Q k) η q)
  simpa only [tsum_apply,tsum_cutoffTerm,ha.of_norm.tsum_mul_right] using ht

end CubicTenVariables.DeltaKernelSeriesLimit
