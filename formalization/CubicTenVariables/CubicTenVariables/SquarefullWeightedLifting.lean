import CubicTenVariables.SquarefullWeightedSums

/-! Finite stationary-support averaging for the selected j=1 squarefull bound.
All kernels and residue classes are literal; no literature or counting input
is used. The finite averaging itself works for arbitrary integral polynomials. -/

noncomputable section
namespace CubicTenVariables.SquarefullWeightedLifting
open MvPolynomial FirstLiftSum SecondLiftSum
open SquarefullWeightedSums WeightedHessianRootCRT WeightedResidueMaximum
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual root mass written with the manuscript's integer representatives. -/
theorem rootMass_eq_fin_sum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] (hdc : d ∣ c) :
    SquarefullWeightedSums.rootMass F c d hdc =
      ∑ x : Fin n → Fin c,
        if (c : ℤ) ∣ eval (integerVector x) F then
          kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0 := by
  classical
  symm
  unfold SquarefullWeightedSums.rootMass
  apply Fintype.sum_equiv (PrimeSumAdapter.vectorResidueEquiv c n)
  intro x
  have hz : ((c : ℤ) ∣ eval (integerVector x) F) ↔
      eval₂ (Int.castRingHom (ZMod c)) (PrimeSumAdapter.vectorResidueEquiv c n x) F = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((eval (fun i => ((x i).val : ℤ)) F : ℤ) : ZMod c) = 0 ↔ _
    rw [PrimeSumAdapter.cast_eval_fin, eval₂_eq_eval_map]
    rfl
  simp only [hz, PrimeSumAdapter.vectorResidueEquiv_apply, map_natCast]

/-- The proved pointwise starT estimate with the common literal L1 definition. -/
theorem norm_completeCubicSum_le_pointwiseL1
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c) (v : Fin 10 → ℤ) :
    ‖completeCubicSum F (c^2*d) v‖ ≤ pointwiseL1 F c d v := by
  exact SquarefullStarT.norm_completeCubicSum_starT_ten_le F hF c d hdc v

/-- Nonnegative finite weights preserve the pointwise complete-sum bound. -/
theorem weighted_norm_sum_le_weightedL1
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖completeCubicSum F (c^2*d) v‖) ≤ weightedL1 F c d V w := by
  apply Finset.sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_left (norm_completeCubicSum_le_pointwiseL1 F hF c d hdc v)
    (hw v hv)

/-- A fixed scalar and root contribute at most their Hessian weight times
one actual weighted residue-class maximum. -/
theorem weighted_support_sum_le
    (F : MvPolynomial (Fin 10) ℤ) (c d : ℕ) [NeZero c]
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (a : ℤ) (x : Fin 10 → Fin c) :
    (∑ v ∈ V, w v *
      (if supportCondition F c a (integerVector x) v then
        kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0)) ≤
      maximum c V w *
        (if (c : ℤ) ∣ eval (integerVector x) F then
          kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0) := by
  by_cases hx : (c : ℤ) ∣ eval (integerVector x) F
  · simp only [supportCondition, hx, true_and, if_true]
    have h := sum_if_stationary_support_le c V w
      (fun i => a * eval (integerVector x) (pderiv i F))
    have he : (∑ v ∈ V, w v *
        (if ∀ i, (c : ℤ) ∣ a * eval (integerVector x) (pderiv i F) + v i then
          kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0)) =
        (∑ v ∈ V, if ∀ i, (c : ℤ) ∣ a * eval (integerVector x) (pderiv i F) + v i
          then w v else 0) * kernelWeight F d (fun i => ((x i).val : ZMod d)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right h (kernelWeight_nonneg F d _)
  · simp [supportCondition, hx]

/-- Exact finite regrouping before applying the residue maximum. -/
theorem weightedL1_eq_regrouped
    (F : MvPolynomial (Fin 10) ℤ) (c d : ℕ)
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ) :
    weightedL1 F c d V w =
      (c : ℝ)^11 * (d : ℝ)^6 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑ x : Fin 10 → Fin c, ∑ v ∈ V,
            w v * (if supportCondition F c (a.val : ℤ) (integerVector x) v then
              kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0)
        else 0 := by
  unfold weightedL1 pointwiseL1
  calc
    _ = (c : ℝ)^11 * (d : ℝ)^6 *
        ∑ v ∈ V, w v *
          ∑ a : Fin c, if Nat.Coprime a.val c then
            ∑ x : Fin 10 → Fin c,
              if supportCondition F c (a.val : ℤ) (integerVector x) v then
                kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = _ := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Nat.Coprime a.val c
      · simp only [if_pos ha]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      · simp [ha]

/-- The manuscript's stationary finite-sum bound in ten variables, including
modulus one and every nonnegative finite weighting. -/
theorem weightedL1_le_residue_maximum
    (F : MvPolynomial (Fin 10) ℤ) (c d : ℕ) [NeZero c]
    (hdc : d ∣ c) (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    weightedL1 F c d V w ≤
      (c : ℝ)^12 * (d : ℝ)^6 * maximum c V w *
        SquarefullWeightedSums.rootMass F c d hdc := by
  have hE := maximum_nonneg c V w hw
  have hM := SquarefullWeightedSums.rootMass_nonneg F c d hdc
  rw [weightedL1_eq_regrouped]
  have hscalar (a : Fin c) :
      (if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c, ∑ v ∈ V,
          w v * (if supportCondition F c (a.val : ℤ) (integerVector x) v then
            kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0)
      else 0) ≤ maximum c V w * SquarefullWeightedSums.rootMass F c d hdc := by
    by_cases ha : Nat.Coprime a.val c
    · rw [if_pos ha, rootMass_eq_fin_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => weighted_support_sum_le F c d V w a.val x
    · simpa only [if_neg ha] using mul_nonneg hE hM
  calc
    _ ≤ (c : ℝ)^11 * (d : ℝ)^6 *
        ∑ _a : Fin c, maximum c V w * SquarefullWeightedSums.rootMass F c d hdc :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hscalar a) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The actual complete sums obey the same finite root-mass majorant. -/
theorem weighted_norm_sum_le_residue_maximum
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖completeCubicSum F (c^2*d) v‖) ≤
      (c : ℝ)^12 * (d : ℝ)^6 * maximum c V w *
        SquarefullWeightedSums.rootMass F c d hdc :=
  (weighted_norm_sum_le_weightedL1 F hF c d hdc V w hw).trans
    (weightedL1_le_residue_maximum F c d hdc V w hw)

end CubicTenVariables.SquarefullWeightedLifting
