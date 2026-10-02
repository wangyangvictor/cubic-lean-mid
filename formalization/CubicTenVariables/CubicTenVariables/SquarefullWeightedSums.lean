import CubicTenVariables.SquarefullStarT
import CubicTenVariables.WeightedHessianRootCRT
import CubicTenVariables.PrimeFrogZeroMass
import CubicTenVariables.WeightedResidueMaximum

/-! Literal weighted sums for the selected j=1 squarefull route. -/

noncomputable section
namespace CubicTenVariables.SquarefullWeightedSums
open MvPolynomial WeightedHessianRootCRT
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Roots at modulus c, with the actual Hessian kernel measured modulo d. -/
def rootMass {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] (hdc : d ∣ c) : ℝ :=
  ∑ x : Fin n → ZMod c,
    if eval₂ (Int.castRingHom (ZMod c)) x F = 0 then
      kernelWeight F d (fun i => ZMod.castHom hdc (ZMod d) (x i)) else 0

/-- The two gcd factors are evaluated on canonical integral representatives. -/
def gcdRootMass {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (d : ℕ) [NeZero d] : ℝ :=
  ∑ x : Fin n → ZMod d,
    if eval₂ (Int.castRingHom (ZMod d)) x F = 0 then
      kernelWeight F d x * (PrimeFrogZeroMass.rootWeight F d x : ℝ) else 0

/-- The literal source L1 summand in ten variables. -/
def pointwiseL1 (F : MvPolynomial (Fin 10) ℤ) (c d : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  (c : ℝ)^11 * (d : ℝ)^6 *
    ∑ a : Fin c, if Nat.Coprime a.val c then
      ∑ x : Fin 10 → Fin c,
        if FirstLiftSum.supportCondition F c (a.val : ℤ) (SecondLiftSum.integerVector x) v then
          kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0
    else 0

def weightedL1 (F : MvPolynomial (Fin 10) ℤ) (c d : ℕ)
    (V : Finset (Fin 10 → ℤ)) (w : (Fin 10 → ℤ) → ℝ) : ℝ :=
  ∑ v ∈ V, w v * pointwiseL1 F c d v

theorem rootMass_nonneg {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d : ℕ) [NeZero c] (hdc : d ∣ c) : 0 ≤ rootMass F c d hdc := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact kernelWeight_nonneg F d _
  · rfl

theorem gcdRootMass_nonneg {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (d : ℕ) [NeZero d] : 0 ≤ gcdRootMass F d := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact mul_nonneg (kernelWeight_nonneg F d _) (Nat.cast_nonneg _)
  · rfl

end CubicTenVariables.SquarefullWeightedSums
