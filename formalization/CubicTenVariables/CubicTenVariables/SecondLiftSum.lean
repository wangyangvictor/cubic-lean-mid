import CubicTenVariables.FirstLiftSum
import CubicTenVariables.SecondLiftPhase

/-! Actual second-lift finite sums and their terminal-maximum bound.
The congruence support is retained when the low-digit vectors are split.
All representatives and coefficient reductions are explicit. -/

noncomputable section
namespace CubicTenVariables.SecondLiftSum
open MvPolynomial HessianTheorem11 FirstLiftPhase FirstLiftSum SecondLiftPhase
open MixedRadixLifting TerminalCubicSum PrimeSumAdapter
open scoped BigOperators

def integerVector {n d : ℕ} (y : Fin n → Fin d) : Fin n → ℤ :=
  fun i => (y i).val

/-- The low digit is modulo A and the high digit modulo T. -/
def secondLiftVectorEquiv (n A T : ℕ) :
    ((Fin n → Fin A) × (Fin n → Fin T)) ≃ (Fin n → Fin (A*T)) :=
  (mixedRadixVectorEquiv n T A).trans
    (Equiv.piCongrRight fun _ => finCongr (Nat.mul_comm T A))

theorem secondLiftVectorEquiv_intCast (n A T : ℕ)
    (y : Fin n → Fin A) (z : Fin n → Fin T) :
    integerVector (secondLiftVectorEquiv n A T (y,z)) =
      integerVector y + (A : ℤ) • integerVector z := by
  ext i
  exact mixedRadixEquiv_intCast T A (y i) (z i)

theorem sum_secondLiftVector {S : Type*} [AddCommMonoid S] (n A T : ℕ)
    (f : (Fin n → Fin (A*T)) → S) :
    (∑ x, f x) = ∑ y : Fin n → Fin A, ∑ z : Fin n → Fin T,
      f (secondLiftVectorEquiv n A T (y,z)) := by
  rw [← (secondLiftVectorEquiv n A T).sum_comp f, Fintype.sum_prod_type]

def residueTerminalMax {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] (y : Fin n → Fin A) : ℝ :=
  terminalMax T (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
    (fun i => ((y i).val : ZMod T))

theorem residueTerminalMax_nonneg {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) [NeZero T] (y : Fin n → Fin A) :
    0 ≤ residueTerminalMax F A T y := terminalMax_nonneg _ _ _ _

theorem norm_residueExponential (q : ℕ) [NeZero q] (b : ℤ) :
    ‖residueExponential q b‖ = 1 := by
  rw [residueExponential_eq_stdAddChar]
  exact QuadraticGaussBound.norm_stdAddChar q (b : ZMod q)

/-- The entire high-digit vector sum equals the actual terminal sum times
its constant phase, with the integer quotient supplying the linear term. -/
theorem sum_secondLift_phase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T]
    (a : ℤ) (y v : Fin n → ℤ)
    (hs : ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) :
    (∑ z : Fin n → Fin T,
      residueExponential (A^2*T) (integerPhase F a (y+(A:ℤ)•integerVector z) v)) =
      residueExponential (A^2*T) (integerPhase F a y v) *
        terminalSum T (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
          (fun i => (linearQuotient F A a y v i : ZMod T)) (a : ZMod T)
          (fun i => (y i : ZMod T)) := by
  simp_rw [residueExponential_secondLift_stdAddChar F hF A T a y _ v hs,
    ← Finset.mul_sum]
  congr 1
  apply Fintype.sum_equiv (vectorResidueEquiv T n)
  intro z
  simp only [vectorResidueEquiv_apply, integerVector, Int.cast_natCast]

def firstLiftInner {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) (a : ℤ) (v : Fin n → ℤ) : ℂ :=
  ∑ x : Fin n → Fin (A*T),
    if supportCondition F A a (integerVector x) v then
      residueExponential (A^2*T) (integerPhase F a (integerVector x) v) else 0

/-- The support is constant on every second-lift block. -/
theorem firstLiftInner_eq_secondLift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T]
    (a : ℤ) (v : Fin n → ℤ) :
    firstLiftInner F A T a v =
      ∑ y : Fin n → Fin A,
        if supportCondition F A a (integerVector y) v then
          residueExponential (A^2*T) (integerPhase F a (integerVector y) v) *
            terminalSum T (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
              (fun i => (linearQuotient F A a (integerVector y) v i : ZMod T))
              (a : ZMod T) (fun i => ((y i).val : ZMod T))
        else 0 := by
  classical
  unfold firstLiftInner
  rw [sum_secondLiftVector]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [secondLiftVectorEquiv_intCast]
  have hsup (z : Fin n → Fin T) :
      supportCondition F A a (integerVector y+(A:ℤ)•integerVector z) v ↔
        supportCondition F A a (integerVector y) v :=
    support_add_smul_iff F A a (integerVector y) (integerVector z) v
  simp_rw [hsup]
  by_cases hy : supportCondition F A a (integerVector y) v
  · simp_rw [if_pos hy]
    simpa only [integerVector, Int.cast_natCast] using
      sum_secondLift_phase F hF A T a (integerVector y) v hy.2
  · simp [hy]

/-- Taking norms now loses only the terminal maximum, and keeps both
the cubic and gradient congruence conditions. -/
theorem norm_firstLiftInner_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T]
    (a : ℕ) (ha : Nat.Coprime a (A*T)) (v : Fin n → ℤ) :
    ‖firstLiftInner F A T (a:ℤ) v‖ ≤
      ∑ y : Fin n → Fin A,
        if supportCondition F A (a:ℤ) (integerVector y) v then
          residueTerminalMax F A T y else 0 := by
  classical
  rw [firstLiftInner_eq_secondLift F hF A T]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : supportCondition F A (a:ℤ) (integerVector y) v
  · simp only [if_pos hy, norm_mul, norm_residueExponential, one_mul]
    have hu := norm_terminalSum_le_terminalMax T
      (map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
      (fun i => (linearQuotient F A (a:ℤ) (integerVector y) v i : ZMod T))
      (ZMod.unitOfCoprime a (ha.of_dvd_right (dvd_mul_left T A)))
      (fun i => ((y i).val : ZMod T))
    simpa only [ZMod.coe_unitOfCoprime, Int.cast_natCast, residueTerminalMax] using hu
  · simp [hy]

theorem lowDigitSum_eq_sum_inner {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (A T : ℕ) (v : Fin n → ℤ) :
    lowDigitSum F A (A*T) v =
      ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        firstLiftInner F A T (a.val:ℤ) v else 0 := by
  simp only [lowDigitSum, firstLiftInner, completeSumPhase, integerPhase,
    dotProduct, integerVector, pow_two, mul_assoc]
  rfl

/-- The source's pointwise flexible-lifting bound, before weighting and
summing frequencies. -/
theorem norm_completeCubicSum_le {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A] [NeZero T]
    (v : Fin n → ℤ) :
    ‖completeCubicSum F (A^2*T) v‖ ≤ (A:ℝ)^(n+1) *
      ∑ a : Fin (A*T), if Nat.Coprime a.val (A*T) then
        ∑ y : Fin n → Fin A,
          if supportCondition F A (a.val:ℤ) (integerVector y) v then
            residueTerminalMax F A T y else 0
      else 0 := by
  classical
  rw [completeCubicSum_firstLift_AT F hF A T v, norm_mul, norm_pow,
    Complex.norm_natCast, lowDigitSum_eq_sum_inner]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Nat.Coprime a.val (A*T)
  · simp only [if_pos ha]
    exact norm_firstLiftInner_le F hF A T a.val ha v
  · simp [ha]

end CubicTenVariables.SecondLiftSum
