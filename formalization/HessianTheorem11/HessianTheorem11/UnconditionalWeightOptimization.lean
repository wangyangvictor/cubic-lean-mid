import HessianTheorem11.RationalDescent
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The fixed-coordinate optimization step in optimal-weight theory.
The feasible region is the actual finite monomial halfspace intersection,
with sum-zero variable weights and every occurring monomial of weight at
least one. Its unique minimum-norm point and sharp normalized bound are
proved by real finite-dimensional convexity. No GIT input is used. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial RationalDescent
open scoped BigOperators
variable {n : ℕ}
abbrev WeightSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

def weightSum : WeightSpace n →ₗ[ℝ] ℝ where
  toFun w := ∑ i, w i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' a w := by simp [Finset.mul_sum]

def realMonomialWeight (e : Fin n →₀ ℕ) : WeightSpace n →ₗ[ℝ] ℝ where
  toFun w := ∑ i, (e i : ℝ) * w i
  map_add' u v := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' a w := by simp [Finset.mul_sum]; congr 1; funext i; ring

def feasible (S : Finset (Fin n →₀ ℕ)) : Set (WeightSpace n) :=
  {w | weightSum w = 0 ∧ ∀ e ∈ S, 1 ≤ realMonomialWeight e w}

theorem feasible_closed (S : Finset (Fin n →₀ ℕ)) : IsClosed (feasible S) := by
  have he : feasible S = {w | weightSum w = 0} ∩
      ⋂ e ∈ S, {w | 1 ≤ realMonomialWeight e w} := by ext w; simp [feasible]
  rw [he]
  exact (isClosed_eq weightSum.continuous_of_finiteDimensional continuous_const).inter
    (isClosed_biInter (fun e _ => isClosed_le continuous_const
      (realMonomialWeight e).continuous_of_finiteDimensional))

theorem feasible_convex (S : Finset (Fin n →₀ ℕ)) : Convex ℝ (feasible S) := by
  intro u hu v hv a b ha hb hab
  refine ⟨?_,?_⟩
  · simp [hu.1,hv.1]
  · intro e he
    change 1 ≤ realMonomialWeight e (a • u + b • v)
    rw [map_add,map_smul,map_smul]
    change 1 ≤ a * realMonomialWeight e u + b * realMonomialWeight e v
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hu.2 e he)),
      mul_nonneg hb (sub_nonneg.mpr (hv.2 e he))]

/-- The optimizer is an actual weight vector, normalized by minimum
monomial weight at least one rather than by its length. -/
def MinimumNorm (S : Finset (Fin n →₀ ℕ)) (w : WeightSpace n) : Prop :=
  w ∈ feasible S ∧ ∀ v ∈ feasible S, ‖w‖ ≤ ‖v‖

theorem minimumNorm_unique (S : Finset (Fin n →₀ ℕ))
    {u v : WeightSpace n} (hu : MinimumNorm S u) (hv : MinimumNorm S v) : u = v := by
  have hinf (w : WeightSpace n) (hw : MinimumNorm S w) :
      ‖(0 : WeightSpace n) - w‖ = ⨅ z : feasible S, ‖(0 : WeightSpace n) - z‖ := by
    letI : Nonempty (feasible S) := ⟨⟨w,hw.1⟩⟩
    simp only [zero_sub,norm_neg]
    apply le_antisymm
    · exact le_ciInf (fun z => hw.2 z z.property)
    · exact ciInf_le (f := fun z : feasible S => ‖(z : WeightSpace n)‖)
        ⟨0,by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩ (⟨w,hw.1⟩ : feasible S)
  have h1 := (norm_eq_iInf_iff_real_inner_le_zero (feasible_convex S) hu.1).mp
    (hinf u hu) v hv.1
  have h2 := (norm_eq_iInf_iff_real_inner_le_zero (feasible_convex S) hv.1).mp
    (hinf v hv) u hu.1
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at h1 h2
  rw [real_inner_comm u v] at h2
  have hnorm : ‖u-v‖ = 0 := by
    have he := norm_sub_sq_real u v
    nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Unconditional finite-support optimization: every nonempty feasible
region has a unique least-length representative. -/
theorem exists_unique_minimumNorm (S : Finset (Fin n →₀ ℕ))
    (hne : (feasible S).Nonempty) : ∃! w, MinimumNorm S w := by
  obtain ⟨w,hw,he⟩ := exists_norm_eq_iInf_of_complete_convex hne
    (feasible_closed S).isComplete (feasible_convex S) (0 : WeightSpace n)
  have hmin : MinimumNorm S w := by
    refine ⟨hw,?_⟩
    intro v hv
    have h := ciInf_le (f := fun z : feasible S => ‖(0 : WeightSpace n)-z‖)
      ⟨0,by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩ ⟨v,hv⟩
    rw [← he] at h
    simpa only [zero_sub,norm_neg] using h
  exact ⟨w,hmin,fun v hv => minimumNorm_unique S hv hmin⟩

theorem feasible_ne_zero {S : Finset (Fin n →₀ ℕ)} (hne : S.Nonempty)
    {w : WeightSpace n} (hw : w ∈ feasible S) : w ≠ 0 := by
  obtain ⟨e,he⟩ := hne
  intro hz
  have h := hw.2 e he
  rw [hz,map_zero] at h
  norm_num at h

/-- Any competing positive monomial lower bound is controlled by the
least-length feasible weight. This is the actual normalized optimality
inequality, with no compactness or optimum input left. -/
theorem normalized_bound {S : Finset (Fin n →₀ ℕ)} (hne : S.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S w)
    (v : WeightSpace n) (hv : weightSum v = 0) (a : ℝ) (ha : 0 < a)
    (hlevel : ∀ e ∈ S, a ≤ realMonomialWeight e v) :
    a / ‖v‖ ≤ 1 / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hne hw.1)
  have hfeas : a⁻¹ • v ∈ feasible S := by
    refine ⟨by simp [hv],?_⟩
    intro e he
    rw [map_smul]
    change 1 ≤ a⁻¹ * realMonomialWeight e v
    calc
      1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
      _ ≤ a⁻¹ * realMonomialWeight e v :=
        mul_le_mul_of_nonneg_left (hlevel e he) (inv_nonneg.mpr ha.le)
  have hmin := hw.2 _ hfeas
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)] at hmin
  have hvpos : 0 < ‖v‖ := by nlinarith [inv_pos.mpr ha]
  apply (div_le_div_iff₀ hvpos hwpos).mpr
  have hh := mul_le_mul_of_nonneg_left hmin ha.le
  simpa only [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul] using hh

/-- At least one actual supported monomial is tight at the minimum-norm
weight. Consequently its reciprocal norm is the attained optimal speed. -/
theorem minimumNorm_active {S : Finset (Fin n →₀ ℕ)} (hne : S.Nonempty)
    {w : WeightSpace n} (hw : MinimumNorm S w) :
    ∃ e ∈ S, realMonomialWeight e w = 1 := by
  obtain ⟨e,he,hmin⟩ := Finset.exists_mem_eq_inf' hne
    (fun e => realMonomialWeight e w)
  have hlevel : ∀ j ∈ S, realMonomialWeight e w ≤ realMonomialWeight j w := by
    intro j hj
    rw [← hmin]
    exact Finset.inf'_le _ hj
  have hpos : 0 < realMonomialWeight e w := lt_of_lt_of_le zero_lt_one (hw.1.2 e he)
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr (feasible_ne_zero hne hw.1)
  have h := normalized_bound hne hw w hw.1.1 _ hpos hlevel
  have hh := (div_le_div_iff₀ hn hn).mp h
  refine ⟨e,he,le_antisymm ?_ (hw.1.2 e he)⟩
  nlinarith

/-- The optimal real weight ray for an actual finite support is attained
on the unit sphere and controls every other sum-zero unit weight. -/
theorem exists_normalized_optimum (S : Finset (Fin n →₀ ℕ))
    (hS : S.Nonempty) (hne : (feasible S).Nonempty) :
    ∃ (w : WeightSpace n) (a : ℝ), weightSum w = 0 ∧ ‖w‖ = 1 ∧ 0 < a ∧
      (∀ e ∈ S, a ≤ realMonomialWeight e w) ∧
      (∃ e ∈ S, realMonomialWeight e w = a) ∧
      ∀ v : WeightSpace n, weightSum v = 0 → ‖v‖ = 1 →
        ∀ b : ℝ, (∀ e ∈ S, b ≤ realMonomialWeight e v) → b ≤ a := by
  obtain ⟨p,hp,_⟩ := exists_unique_minimumNorm S hne
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr (feasible_ne_zero hS hp.1)
  refine ⟨‖p‖⁻¹ • p,1 / ‖p‖,by simp [hp.1.1],?_,one_div_pos.mpr hn,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · intro e he
    rw [map_smul]
    change 1 / ‖p‖ ≤ ‖p‖⁻¹ * realMonomialWeight e p
    simpa only [one_div,mul_one] using
      mul_le_mul_of_nonneg_left (hp.1.2 e he) (inv_nonneg.mpr hn.le)
  · obtain ⟨e,he,heq⟩ := minimumNorm_active hS hp
    exact ⟨e,he,by simp [heq,one_div]⟩
  · intro v hv hvn b hb
    by_cases hbpos : 0 < b
    · have h := normalized_bound hS hp v hv b hbpos hb
      simpa only [hvn,div_one] using h
    · exact (le_of_not_gt hbpos).trans (one_div_pos.mpr hn).le

/-- An actual strictly positive integral polynomial weighting supplies the
feasible point needed by the unconditional optimizer theorem. -/
theorem feasible_of_positive {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hsum : ∑ i, w i = 0) (hpositive : HasPositiveWeights F w) :
    WithLp.toLp 2 (fun i => (w i : ℝ)) ∈ feasible F.support := by
  constructor
  · change (∑ i, (w i : ℝ)) = 0
    exact_mod_cast hsum
  · intro e he
    have h : (1 : ℤ) ≤ monomialWeight w e := by have := hpositive e he; omega
    change (1 : ℝ) ≤ ∑ i, (e i : ℝ) * (w i : ℝ)
    exact_mod_cast h

/-- Every actual positive integral frame has a unique real optimal weight
in its fixed coordinates. Rationality and comparison of different flags
are separate remaining steps, not assumptions of this theorem. -/
theorem positive_frame_has_unique_fixed_optimizer {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (f : WeightFrame K n) (hf : f.Positive F) :
    ∃! w, MinimumNorm (PolynomialRestriction.restrict f.matrix F).support w :=
  exists_unique_minimumNorm _ ⟨_,feasible_of_positive _ f.weight f.sum_zero hf⟩

end HessianTheorem11.UnconditionalWeightOptimization
