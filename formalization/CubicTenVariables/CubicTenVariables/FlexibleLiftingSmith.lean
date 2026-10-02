import CubicTenVariables.FlexibleLifting
import CubicTenVariables.TerminalSmithBound

/-!
# Weighted flexible lifting with the actual terminal Smith profile

The terminal maximum is replaced by its proved profile bound inside the
literal zero-fiber sum. One integral Hessian diagonalization is chosen for
each canonical base point before all primes, exponents, frequency sets and
weights. The final theorem takes no diagonalization or profile estimate as
input. Weights need be nonnegative only on the given finite frequency set.
-/

noncomputable section
namespace CubicTenVariables.FlexibleLiftingSmith
open MvPolynomial HessianTheorem11 SecondLiftSum FlexibleLifting
open PrimePowerKernelProfile SmithProfileMultiplicity SmithProfileNumerics
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The canonical base point is lifted to integers before taking its
Hessian. Its actual terminal maximum uses the same integer representatives. -/
theorem residueTerminalMax_le_profile_of_diagonalization {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A : ℕ) (y : Fin n → Fin A)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F (integerVector y) * V =
      Matrix.diagonal d)
    (p : ℕ) [NeZero p] (hp : p.Prime) (a t : ℕ)
    (hA : p^a ∣ A) (hcase : t ≤ a ∨ p ≠ 2) :
    residueTerminalMax F A (p^t) y ≤
      Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
        (penaltyWeight a t i : ℝ) *
          (profile (fun ν => truncatedValuation p a (d ν)) i : ℝ)) := by
  have hA' : ((p^a : ℕ) : ℤ) ∣ (A : ℤ) := by exact_mod_cast hA
  simpa only [residueTerminalMax, integerVector, Int.cast_natCast] using
    TerminalSmithBound.terminalMax_le_profile_of_diagonalization F hF
      (integerVector y) U V d hD p hp a t hcase (A : ℤ) hA'

/-- Weighted lifting with displayed actual integral diagonalizations.
The source's congruence filter, totient, residue maximum and real exponent
all remain literal finite quantities. -/
theorem weighted_completeCubicSum_le_profile_of_diagonalizations {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A : ℕ) [NeZero A]
    (U V : (Fin n → Fin A) → (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (d : (Fin n → Fin A) → Fin n → ℤ)
    (hD : ∀ y, (U y : Matrix (Fin n) (Fin n) ℤ) * hessian F (integerVector y) * V y =
      Matrix.diagonal (d y))
    (p : ℕ) (hp : p.Prime) (a t : ℕ)
    (hA : p^a ∣ A) (hcase : t ≤ a ∨ p ≠ 2)
    (S : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ)
    (hw : ∀ v ∈ S, 0 ≤ w v) :
    (∑ v ∈ S, w v * ‖completeCubicSum F (A^2*p^t) v‖) ≤
      (A : ℝ)^n * (Nat.totient (A^2*p^t) : ℝ) * WeightedResidueMaximum.maximum A S w *
        ∑ y : Fin n → Fin A, if (A : ℤ) ∣ eval (integerVector y) F then
          Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
            (penaltyWeight a t i : ℝ) *
              (profile (fun ν => truncatedValuation p a (d y ν)) i : ℝ))
        else 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply (weighted_completeCubicSum_le F hF A (p^t) S w hw).trans
  apply mul_le_mul_of_nonneg_left
  · unfold zeroFiberTerminalTotal
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact residueTerminalMax_le_profile_of_diagonalization F hF A y
        (U y) (V y) (d y) (hD y) p hp a t hA hcase
    · rfl
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (WeightedResidueMaximum.maximum_nonneg A S w hw)

/-- Actual Hessian diagonals are constructed once, before every prime,
exponent, finite frequency set and weight. No Smith data is an input to
this weighted estimate; the zero-fiber profile sum remains to be estimated. -/
theorem exists_diagonalizations_and_weighted_completeCubicSum_le_profile {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A : ℕ) [NeZero A] :
    ∃ (U V : (Fin n → Fin A) → (Matrix (Fin n) (Fin n) ℤ)ˣ)
      (d : (Fin n → Fin A) → Fin n → ℤ),
      (∀ y, (U y : Matrix (Fin n) (Fin n) ℤ) * hessian F (integerVector y) * V y =
        Matrix.diagonal (d y)) ∧
      ∀ (p : ℕ), p.Prime → ∀ (a t : ℕ), p^a ∣ A → (t ≤ a ∨ p ≠ 2) →
      ∀ (S : Finset (Fin n → ℤ)) (w : (Fin n → ℤ) → ℝ),
        (∀ v ∈ S, 0 ≤ w v) →
        (∑ v ∈ S, w v * ‖completeCubicSum F (A^2*p^t) v‖) ≤
          (A : ℝ)^n * (Nat.totient (A^2*p^t) : ℝ) *
            WeightedResidueMaximum.maximum A S w *
            ∑ y : Fin n → Fin A, if (A : ℤ) ∣ eval (integerVector y) F then
              Real.rpow (p : ℝ) (((n*t : ℕ) : ℝ) - ∑ i ∈ Finset.range a,
                (penaltyWeight a t i : ℝ) *
                  (profile (fun ν => truncatedValuation p a (d y ν)) i : ℝ))
            else 0 := by
  have hdiag : ∀ y : Fin n → Fin A,
      ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
        (U : Matrix (Fin n) (Fin n) ℤ) * hessian F (integerVector y) * V =
          Matrix.diagonal d :=
    fun y => MatrixSmithExistence.exists_integer_diagonalization (hessian F (integerVector y))
  choose U V d hD using hdiag
  refine ⟨U, V, d, hD, ?_⟩
  intro p hp a t hA hcase S w hw
  exact weighted_completeCubicSum_le_profile_of_diagonalizations F hF A U V d hD
    p hp a t hA hcase S w hw

end CubicTenVariables.FlexibleLiftingSmith
