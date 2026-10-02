import CubicTenVariables.SecondLiftSum
import CubicTenVariables.WeightedResidueMaximum
import CubicTenVariables.LiftingTotient

/-! The manuscript's weighted flexible-lifting inequality for literal
complete cubic sums. The residue maximum, zero-fiber terminal sum and
totient factor are actual finite quantities. The proof applies to all
positive A,T; no square-full, radical, anisotropy or literature premise
is needed for this elementary inequality. -/

noncomputable section
namespace CubicTenVariables.FlexibleLifting
open MvPolynomial HessianTheorem11 FirstLiftSum SecondLiftSum
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def zeroFiberTerminalTotal {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] : ℝ :=
  ∑ y : Fin n → Fin A,
    if (A : ℤ) ∣ eval (integerVector y) F then residueTerminalMax F A T y else 0

def pointwiseResidueBound {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] (v : Fin n → ℤ) : ℝ :=
  ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
    ∑ y : Fin n → Fin A,
      if supportCondition F A (a.val:ℤ) (integerVector y) v then
        residueTerminalMax F A T y else 0
  else 0

theorem weighted_support_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero A] [NeZero T] (a : ℤ) (y : Fin n → Fin A)
    (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) :
    (∑ v ∈ V, w v * (if supportCondition F A a (integerVector y) v then
      residueTerminalMax F A T y else 0)) ≤
    if (A : ℤ) ∣ eval (integerVector y) F then
      WeightedResidueMaximum.maximum A V w * residueTerminalMax F A T y else 0 := by
  classical
  by_cases hy : (A : ℤ) ∣ eval (integerVector y) F
  · simp only [supportCondition, hy, true_and, if_true]
    have he : (∑ v ∈ V, w v *
        (if ∀ i, (A : ℤ) ∣ a*eval (integerVector y) (pderiv i F)+v i then
          residueTerminalMax F A T y else 0)) =
        (∑ v ∈ V, if ∀ i, (A : ℤ) ∣ a*eval (integerVector y) (pderiv i F)+v i then
          w v else 0) * residueTerminalMax F A T y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (WeightedResidueMaximum.sum_if_stationary_support_le A V w
        (fun i => a*eval (integerVector y) (pderiv i F)))
      (residueTerminalMax_nonneg F A T y)
  · simp [supportCondition, hy]

theorem weighted_pointwise_rearrange {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) :
    (∑ v ∈ V, w v * pointwiseResidueBound F A T v) =
      ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        ∑ y : Fin n → Fin A, ∑ v ∈ V,
          w v * (if supportCondition F A (a.val:ℤ) (integerVector y) v then
            residueTerminalMax F A T y else 0)
      else 0 := by
  classical
  unfold pointwiseResidueBound
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Nat.Coprime a.val (A*T)
  · simp_rw [if_pos ha, Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp [ha]

theorem weighted_pointwiseResidueBound_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero A] [NeZero T]
    (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ) :
    (∑ v ∈ V, w v * pointwiseResidueBound F A T v) ≤
      (Nat.totient (A*T) : ℝ) * WeightedResidueMaximum.maximum A V w *
        zeroFiberTerminalTotal F A T := by
  classical
  rw [weighted_pointwise_rearrange]
  calc
    _ ≤ ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        WeightedResidueMaximum.maximum A V w * zeroFiberTerminalTotal F A T else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : Nat.Coprime a.val (A*T)
      · simp only [if_pos ha]
        rw [zeroFiberTerminalTotal, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro y _
        simpa only [mul_ite, mul_zero] using
          weighted_support_le F A T (a.val:ℤ) y V w
      · simp [ha]
    _ = _ := by rw [LiftingTotient.sum_coprime_const]; ring

/-- Exact source inequality with the literal weighted residue maximum.
Nonnegativity is required only for frequencies in the given finite set. -/
theorem weighted_completeCubicSum_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T]
    (V : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    (∑ v ∈ V, w v * ‖completeCubicSum F (A^2*T) v‖) ≤
      (A : ℝ)^n * (Nat.totient (A^2*T) : ℝ) *
        WeightedResidueMaximum.maximum A V w * zeroFiberTerminalTotal F A T := by
  have hfactor : (A : ℝ)^(n+1)*(Nat.totient (A*T) : ℝ) =
      (A : ℝ)^n*(Nat.totient (A^2*T) : ℝ) := by
    simpa only [pow_two, mul_assoc] using
      LiftingTotient.real_lifting_factor A (A*T) n (dvd_mul_right A T)
  calc
    _ ≤ ∑ v ∈ V, w v * ((A : ℝ)^(n+1) * pointwiseResidueBound F A T v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (norm_completeCubicSum_le F hF A T v) (hw v hv)
    _ = (A : ℝ)^(n+1) * (∑ v ∈ V, w v * pointwiseResidueBound F A T v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ (A : ℝ)^(n+1) * ((Nat.totient (A*T) : ℝ) *
        WeightedResidueMaximum.maximum A V w * zeroFiberTerminalTotal F A T) :=
      mul_le_mul_of_nonneg_left (weighted_pointwiseResidueBound_le F A T V w) (by positivity)
    _ = _ := by
      calc
        _ = ((A : ℝ)^(n+1)*(Nat.totient (A*T) : ℝ)) *
            WeightedResidueMaximum.maximum A V w * zeroFiberTerminalTotal F A T := by ring
        _ = _ := by rw [hfactor]

end CubicTenVariables.FlexibleLifting
