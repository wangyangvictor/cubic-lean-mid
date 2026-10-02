import HessianTheorem11.UnconditionalWeightOptimization

/-! The minimum-norm support optimizer is orthogonal to every direction
preserving its tight constraints. This is the concrete active-face linear
algebra bridge needed to prove rationality of its coordinates. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial Filter
open scoped Topology
variable {n : ℕ}

theorem minimumNorm_inner {S : Finset (Fin n →₀ ℕ)} {w : WeightSpace n}
    (hw : MinimumNorm S w) (v : WeightSpace n) (hv : v ∈ feasible S) :
    0 ≤ inner ℝ w (v-w) := by
  letI : Nonempty (feasible S) := ⟨⟨w,hw.1⟩⟩
  have he : ‖(0 : WeightSpace n)-w‖ = ⨅ z : feasible S, ‖(0 : WeightSpace n)-z‖ := by
    simp only [zero_sub,norm_neg]
    apply le_antisymm
    · exact le_ciInf (fun z => hw.2 z z.property)
    · exact ciInf_le (f := fun z : feasible S => ‖(z : WeightSpace n)‖)
        ⟨0,by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩ (⟨w,hw.1⟩ : feasible S)
  have h := (norm_eq_iInf_iff_real_inner_le_zero (feasible_convex S) hw.1).mp he v hv
  simp only [zero_sub,inner_neg_left] at h
  linarith

/-- A direction annihilating every tight monomial constraint is feasible
in both signs near the optimizer. Finiteness of the actual support provides
one neighborhood valid for all its inequalities. -/
theorem feasible_near_tight_direction {S : Finset (Fin n →₀ ℕ)}
    {w : WeightSpace n} (hw : w ∈ feasible S) (v : WeightSpace n)
    (hsum : weightSum v = 0)
    (htight : ∀ e ∈ S, realMonomialWeight e w = 1 → realMonomialWeight e v = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, w + t • v ∈ feasible S := by
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ e ∈ S, 1 ≤ realMonomialWeight e (w+t • v) := by
    rw [eventually_all_finset]
    intro e he
    by_cases ht : realMonomialWeight e w = 1
    · exact Filter.Eventually.of_forall (fun t => by simp [ht,htight e he ht])
    · have hstrict : 1 < realMonomialWeight e w := lt_of_le_of_ne (hw.2 e he) (Ne.symm ht)
      have hc : Continuous (fun t : ℝ => realMonomialWeight e (w+t • v)) :=
        (realMonomialWeight e).continuous_of_finiteDimensional.comp
          (continuous_const.add (continuous_id.smul continuous_const))
      have hh := (hc.tendsto 0).eventually_const_lt (by simpa using hstrict)
      exact hh.mono (fun t ht => ht.le)
  exact hall.mono (fun t ht => ⟨by simp [hw.1,hsum],ht⟩)

/-- The actual optimizer satisfies the linear normal-space equations of
its active face. No KKT or rational-polyhedron input is assumed. -/
theorem minimumNorm_orthogonal_tight_direction {S : Finset (Fin n →₀ ℕ)}
    {w : WeightSpace n} (hw : MinimumNorm S w) (v : WeightSpace n)
    (hsum : weightSum v = 0)
    (htight : ∀ e ∈ S, realMonomialWeight e w = 1 → realMonomialWeight e v = 0) :
    inner ℝ w v = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp
    (feasible_near_tight_direction hw.1 v hsum htight)
  have hplus : w + (ε/2) • v ∈ feasible S := hball (by
    rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0 < ε/2)]
    linarith)
  have hminus : w + (-(ε/2)) • v ∈ feasible S := hball (by
    rw [Real.dist_eq,sub_zero,abs_neg,abs_of_pos (by linarith : 0 < ε/2)]
    linarith)
  have h1 := minimumNorm_inner hw _ hplus
  have h2 := minimumNorm_inner hw _ hminus
  simp only [add_sub_cancel_left,real_inner_smul_right] at h1 h2
  nlinarith

end HessianTheorem11.UnconditionalWeightOptimization
