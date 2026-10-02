import CubicTenVariables.GaussianCongruenceMajorant
import CubicTenVariables.SquarefullWeightedLifting
import CubicTenVariables.OnionGaussianCharacter
import CubicTenVariables.WeightedGaussianPoisson

/-! The finite L1 sum is majorized by a full Gaussian Fourier sum. The
cubic congruence is weakened before Poisson summation. No degree, geometric,
literature, or point-count assumption is used in this analytic adapter. -/

noncomputable section
namespace CubicTenVariables.OnionGaussianMajorant
open MvPolynomial FirstLiftSum SecondLiftSum SquarefullWeightedSums
open WeightedHessianRootCRT WeightedGaussianPoisson OnionGaussianCharacter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private theorem residueGaussian_nonneg {n : ℕ} (c W : ℝ) (b u : Fin n → ℝ) :
    0 ≤ residueGaussian c W b u := tsum_nonneg (fun _ => Real.exp_nonneg _)

/-- Weaken the polynomial constraint before replacing the stationary class
by its entire Gaussian progression. -/
theorem support_sum_le_gaussian
    (F : MvPolynomial (Fin 10) ℤ) (c d r : ℕ) [NeZero c] (hrc : r ∣ c)
    (W R : ℝ) (hW : 0 < W) (hR : 0 ≤ R) (hRW : R ≤ W)
    (u : Fin 10 → ℝ) (V : Finset (Fin 10 → ℤ))
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R)
    (a : ℤ) (x : Fin 10 → Fin c) :
    (∑ v ∈ V, if supportCondition F c a (integerVector x) v then
      kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0) ≤
      Real.exp 10 * partialWeight F c d r x *
        residueGaussian (c : ℝ) W (fun i => (stationaryShift F a x i : ℝ)) u := by
  by_cases hx : (c : ℤ) ∣ eval (integerVector x) F
  · have hr : (r : ℤ) ∣ eval (integerVector x) F :=
      dvd_trans (by exact_mod_cast hrc) hx
    have hpred (v : Fin 10 → ℤ) : supportCondition F c a (integerVector x) v ↔
        ∀ i, (c : ℤ) ∣ v i-stationaryShift F a x i := by
      simp only [supportCondition, hx, true_and]
      apply forall_congr'
      intro i
      have he : a * eval (integerVector x) (pderiv i F) + v i =
          v i-stationaryShift F a x i := by
        unfold stationaryShift
        ring
      rw [he]
    have hcard := GaussianCongruenceMajorant.card_congruence_le c (NeZero.pos c)
      W R hW hR hRW u (stationaryShift F a x) V hbox
    rw [partialWeight, if_pos hr]
    calc
      _ = ((V.filter fun v => ∀ i, (c : ℤ) ∣ v i-stationaryShift F a x i).card : ℝ) *
          kernelWeight F d (fun i => ((x i).val : ZMod d)) := by
        simp_rw [hpred]
        rw [← Finset.sum_filter]
        simp
      _ ≤ (Real.exp 10 *
          residueGaussian (c : ℝ) W (fun i => (stationaryShift F a x i : ℝ)) u) *
            kernelWeight F d (fun i => ((x i).val : ZMod d)) :=
        mul_le_mul_of_nonneg_right hcard (kernelWeight_nonneg F d _)
      _ = _ := by ring
  · have hn (v : Fin 10 → ℤ) : ¬supportCondition F c a (integerVector x) v :=
      fun h => hx h.1
    simp only [hn, if_false, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (partialWeight_nonneg F c d r x))
      (residueGaussian_nonneg _ _ _ _)

/-- The exact finite Gaussian intermediary, prior to taking a Fourier norm. -/
theorem weightedL1_le_gaussian
    (F : MvPolynomial (Fin 10) ℤ) (c d r : ℕ) [NeZero c] (hrc : r ∣ c)
    (W R : ℝ) (hW : 0 < W) (hR : 0 ≤ R) (hRW : R ≤ W)
    (u : Fin 10 → ℝ) (V : Finset (Fin 10 → ℤ))
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) :
    weightedL1 F c d V (fun _ => 1) ≤
      (c : ℝ)^11*(d : ℝ)^6*Real.exp 10 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑ x : Fin 10 → Fin c, partialWeight F c d r x *
            residueGaussian (c : ℝ) W
              (fun i => (stationaryShift F (a.val : ℤ) x i : ℝ)) u
        else 0 := by
  rw [SquarefullWeightedLifting.weightedL1_eq_regrouped]
  simp only [one_mul]
  have hs :
      (∑ a : Fin c, if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c, ∑ v ∈ V,
          if supportCondition F c (a.val : ℤ) (integerVector x) v then
            kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0
      else 0) ≤
      Real.exp 10 * ∑ a : Fin c, if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c, partialWeight F c d r x *
          residueGaussian (c : ℝ) W
            (fun i => (stationaryShift F (a.val : ℤ) x i : ℝ)) u
      else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : Nat.Coprime a.val c
    · simp only [if_pos ha]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      simpa only [mul_assoc] using
        support_sum_le_gaussian F c d r hrc W R hW hR hRW u V hbox a.val x
    · simp [ha]
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (c : ℝ)^11*(d : ℝ)^6)
  exact hp.trans_eq (by ring)

/-- The complete finite-to-Fourier L1 majorant, with the partial root
condition and actual Hessian weights inside the character sum. -/
theorem weightedL1_le_fourier
    (F : MvPolynomial (Fin 10) ℤ) (c d r : ℕ) [NeZero c]
    (hdc : d ∣ c) (hrc : r ∣ c)
    (W R : ℝ) (hW : 0 < W) (hR : 0 ≤ R) (hRW : R ≤ W)
    (u : Fin 10 → ℝ) (V : Finset (Fin 10 → ℤ))
    (hbox : ∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) :
    weightedL1 F c d V (fun _ => 1) ≤
      (c : ℝ)^11*(d : ℝ)^6*Real.exp 10*(Real.sqrt Real.pi*W/(c : ℝ))^10 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
            ‖partialRootCharacterMass F c d r hdc hrc (-(a.val : ℤ) : ZMod c) h‖
        else 0 := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hp (a : Fin c) := WeightedGaussianPoisson.weighted_le (c : ℝ) W hcR hW
    (fun x i => (stationaryShift F (a.val : ℤ) x i : ℝ)) u (partialWeight F c d r)
  simp_rw [OnionGaussianCharacter.character_eq F c d r hdc hrc] at hp
  have hs :
      (∑ a : Fin c, if Nat.Coprime a.val c then
        ∑ x : Fin 10 → Fin c, partialWeight F c d r x *
          residueGaussian (c : ℝ) W
            (fun i => (stationaryShift F (a.val : ℤ) x i : ℝ)) u
      else 0) ≤
      (Real.sqrt Real.pi*W/(c : ℝ))^10 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑' h : Fin 10 → ℤ, dualGaussian (c : ℝ) W h *
            ‖partialRootCharacterMass F c d r hdc hrc (-(a.val : ℤ) : ZMod c) h‖
        else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : Nat.Coprime a.val c
    · simpa only [if_pos ha] using hp a
    · simp [ha]
  calc
    _ ≤ (c : ℝ)^11*(d : ℝ)^6*Real.exp 10 *
        ∑ a : Fin c, if Nat.Coprime a.val c then
          ∑ x : Fin 10 → Fin c, partialWeight F c d r x *
            residueGaussian (c : ℝ) W
              (fun i => (stationaryShift F (a.val : ℤ) x i : ℝ)) u
        else 0 := weightedL1_le_gaussian F c d r hrc W R hW hR hRW u V hbox
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hs
          (by positivity : 0 ≤ (c : ℝ)^11*(d : ℝ)^6*Real.exp 10)

end CubicTenVariables.OnionGaussianMajorant
