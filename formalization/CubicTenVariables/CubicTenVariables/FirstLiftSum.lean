import CubicTenVariables.FirstLiftPhase
import CubicTenVariables.MixedRadixLifting

/-! The complete square-full first-lift identity, with the project's
literal integer-representative exponential sum. The two high-digit sums
enforce F=0 and a grad F+v=0 modulo A. No radical hypothesis is needed
beyond A∣M, which is automatic for the manuscript's M=A*T. -/

noncomputable section
namespace CubicTenVariables.FirstLiftSum
open MvPolynomial HessianTheorem11 FirstLiftPhase LiftingCharacters MixedRadixLifting
open scoped BigOperators

def supportCondition {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (a : ℤ) (y v : Fin n → ℤ) : Prop :=
  (A : ℤ) ∣ eval y F ∧ ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i

instance {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (a : ℤ) (y v : Fin n → ℤ) : Decidable (supportCondition F A a y v) :=
  inferInstanceAs (Decidable ((A : ℤ) ∣ eval y F ∧
    ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i))

theorem sum_lifted_phase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A M : ℕ) [NeZero A] [NeZero M]
    (hAM : A ∣ M) (y v : Fin n → ℤ) (a : ℤ) :
    (∑ e : Fin A, ∑ h : Fin n → Fin A,
      residueExponential (A*M)
        (integerPhase F (a+(M:ℤ)*e.val)
          (y+(M:ℤ)•(fun i => ((h i).val : ℤ))) v)) =
      if supportCondition F A a y v then
        (A : ℂ)^(n+1) * residueExponential (A*M) (integerPhase F a y v) else 0 := by
  classical
  simp_rw [residueExponential_firstLift F hF A M hAM]
  have hdot (h : Fin n → Fin A) :
      dotProduct (a•gradient F y+v) (fun i => ((h i).val : ℤ)) =
        ∑ i, (h i).val * (a*eval y (pderiv i F)+v i) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, gradient]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hdot, ← Finset.mul_sum]
  rw [sum_scalar_vector_phase]
  split_ifs <;> simp_all [supportCondition, mul_comm]

theorem completeSumPhase_mixedRadix {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A M : ℕ) (a : Fin M) (e : Fin A)
    (y : Fin n → Fin M) (h : Fin n → Fin A) (v : Fin n → ℤ) :
    completeSumPhase F (mixedRadixEquiv A M (a,e))
      (mixedRadixVectorEquiv n A M (y,h)) v =
      integerPhase F ((a.val:ℤ)+(M:ℤ)*e.val)
        ((fun i => ((y i).val:ℤ))+(M:ℤ)•(fun i => ((h i).val:ℤ))) v := by
  unfold completeSumPhase integerPhase
  rw [mixedRadixEquiv_intCast, mixedRadixVectorEquiv_intCast]
  rfl

/-- The exact low-digit sum. Its displayed support contains both the
cubic equation and every stationary-gradient congruence. -/
def lowDigitSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A M : ℕ) (v : Fin n → ℤ) : ℂ := by
  classical
  exact ∑ a : Fin M, if Nat.Coprime a.val M then
    ∑ y : Fin n → Fin M,
      if supportCondition F A (a.val:ℤ) (fun i => ((y i).val:ℤ)) v then
        residueExponential (A*M) (completeSumPhase F a y v)
      else 0
  else 0

/-- Full finite-sum identity, including the unit condition and both
orthogonality constraints, for every positive A,M with A∣M. -/
theorem completeCubicSum_firstLift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A M : ℕ) [NeZero A] [NeZero M] (hAM : A ∣ M)
    (v : Fin n → ℤ) :
    completeCubicSum F (A*M) v = (A:ℂ)^(n+1) * lowDigitSum F A M v := by
  classical
  unfold completeCubicSum lowDigitSum
  rw [sum_mixedRadix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [coprime_mixedRadix_iff A M hAM]
  by_cases ha : Nat.Coprime a.val M
  · simp_rw [if_pos ha]
    simp_rw [sum_mixedRadixVector n A M]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [completeSumPhase_mixedRadix]
    rw [sum_lifted_phase F hF A M hAM]
    split_ifs <;> simp [integerPhase, completeSumPhase, dotProduct]
  · simp [ha]

/-- The manuscript's q=A²T first lift. No square-full or radical premise
is needed for this identity; those hypotheses enter later estimates. -/
theorem completeCubicSum_firstLift_AT {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T] (v : Fin n → ℤ) :
    completeCubicSum F (A^2*T) v = (A:ℂ)^(n+1) * lowDigitSum F A (A*T) v := by
  simpa only [pow_two, mul_assoc] using
    completeCubicSum_firstLift F hF A (A*T) (dvd_mul_right A T) v

end CubicTenVariables.FirstLiftSum
