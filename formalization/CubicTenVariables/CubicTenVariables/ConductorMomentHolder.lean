import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! Finite weighted Hölder interpolation between a positive half-moment
and an inverse moment. The hypotheses concern only the finite summation
set; no arithmetic or literature premise is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ConductorMomentHolder
open scoped BigOperators Classical

/-- Interpolate the positive half-moment and inverse moment with powers
two thirds and one third. Both zero summands and an empty set are allowed. -/
theorem sum_le_moments {ι : Type*} (E : Finset ι) (a k : ι → ℝ)
    (ha : ∀ i ∈ E, 0 ≤ a i) (hk : ∀ i ∈ E, 1 ≤ k i) :
    (∑ i ∈ E, a i) ≤
      (∑ i ∈ E, a i * (k i)^((1 : ℝ)/2))^((2 : ℝ)/3) *
      (∑ i ∈ E, a i / k i)^((1 : ℝ)/3) := by
  let w : ι → ℝ := fun i => if i ∈ E then a i / k i else 0
  let f : ι → ℝ := fun i => if i ∈ E then k i else 1
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    by_cases hi : i ∈ E
    · simpa only [w, if_pos hi] using
        div_nonneg (ha i hi) (le_trans zero_le_one (hk i hi))
    · simp only [w, if_neg hi, le_refl]
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    by_cases hi : i ∈ E
    · simpa only [f, if_pos hi] using le_trans zero_le_one (hk i hi)
    · simp only [f, if_neg hi, zero_le_one]
  have hleft : (∑ i ∈ E, w i * f i) = ∑ i ∈ E, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, f, if_pos hi]
    exact div_mul_cancel₀ (a i) (ne_of_gt (lt_of_lt_of_le zero_lt_one (hk i hi)))
  have hinverse : (∑ i ∈ E, w i) = ∑ i ∈ E, a i / k i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, if_pos hi]
  have hhalf : (∑ i ∈ E, w i * (f i)^((3 : ℝ)/2)) =
      ∑ i ∈ E, a i * (k i)^((1 : ℝ)/2) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hki : 0 < k i := lt_of_lt_of_le zero_lt_one (hk i hi)
    simp only [w, f, if_pos hi]
    rw [show (3 : ℝ)/2 = 1 + 1/2 by norm_num,
      Real.rpow_add hki, Real.rpow_one, ← mul_assoc, div_mul_cancel₀ _ hki.ne']
  have h := Real.inner_le_weight_mul_Lp_of_nonneg E
    (p := (3 : ℝ)/2) (by norm_num) w f hw hf
  rw [hleft, hinverse, hhalf] at h
  norm_num at h
  simpa only [mul_comm] using h

end CubicTenVariables.ConductorMomentHolder
