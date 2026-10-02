import CubicTenVariables.FirstLiftPhase
import CubicTenVariables.TerminalCubicSum

/-!
# Exact second-lift phase factorization

On the literal support `A ∣ a∂ᵢF(y)+vᵢ`, the integer quotient defines the
linear term of the terminal cubic sum. The phase difference is exactly
`A²` times the integral terminal phase, before reduction. Character
scaling then gives the source factorization modulo `A²T`. Only actual
integer coefficient/coordinate casts into `ZMod T` are used.
-/

noncomputable section
namespace CubicTenVariables.SecondLiftPhase

open MvPolynomial HessianTheorem11 CubicTaylorExpansion FirstLiftPhase
open LiftingCharacters TerminalCubicSum
open scoped BigOperators

/-- The literal coordinatewise integer quotient on stationary support. -/
def linearQuotient {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (a : ℤ) (y v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => (a * eval y (pderiv i F) + v i) / (A : ℤ)

theorem mul_linearQuotient {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (a : ℤ) (y v : Fin n → ℤ)
    (hs : ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) (i : Fin n) :
    (A : ℤ) * linearQuotient F A a y v i = a * eval y (pderiv i F) + v i := by
  rw [linearQuotient, mul_comm]
  exact Int.ediv_mul_cancel (hs i)

/-- Exact integral factorization; divisibility of `F(y)` itself is not needed. -/
theorem integerPhase_secondLift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A : ℕ) (a : ℤ) (y z v : Fin n → ℤ)
    (hs : ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) :
    integerPhase F a (y + (A : ℤ) • z) v = integerPhase F a y v +
      (A : ℤ) ^ 2 * terminalPhase F (A : ℤ) (linearQuotient F A a y v) a y z := by
  have hb : a • gradient F y + v = (A : ℤ) • linearQuotient F A a y v := by
    funext i
    exact (mul_linearQuotient F A a y v hs i).symm
  have hz := congrArg (fun b : Fin _ → ℤ => dotProduct b z) hb
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hz
  rw [dotProduct_comm (gradient F y) z] at hz
  change a * directional F y z + dotProduct v z =
    (A : ℤ) * dotProduct (linearQuotient F A a y v) z at hz
  calc
    _ = integerPhase F a y v +
        (A : ℤ) * (a * directional F y z + dotProduct v z) +
        (A : ℤ) ^ 2 * (a * quadraticAt F y z + a * (A : ℤ) * eval z F) := by
      unfold integerPhase
      rw [eval_cubic_add_smul F hF]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    _ = _ := by
      rw [hz]
      unfold terminalPhase
      ring

/-- The source's second-lift character factorization with integer representatives. -/
theorem residueExponential_secondLift {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (A T : ℕ) [NeZero A]
    (a : ℤ) (y z v : Fin n → ℤ)
    (hs : ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) :
    residueExponential (A ^ 2 * T) (integerPhase F a (y + (A : ℤ) • z) v) =
      residueExponential (A ^ 2 * T) (integerPhase F a y v) *
        residueExponential T (terminalPhase F (A : ℤ) (linearQuotient F A a y v) a y z) := by
  rw [integerPhase_secondLift F hF A a y z v hs, residueExponential_add]
  congr 1
  simpa only [Nat.cast_pow, Nat.mul_comm] using
    residueExponential_mul_modulus T (A ^ 2)
      (terminalPhase F (A : ℤ) (linearQuotient F A a y v) a y z)

/-- Arbitrary integral evaluation followed by its actual coefficient and coordinate cast. -/
theorem cast_eval_int {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (T : ℕ)
    (x : Fin n → ℤ) :
    (eval x P : ZMod T) =
      eval (fun i => (x i : ZMod T)) (MvPolynomial.map (Int.castRingHom (ZMod T)) P) := by
  simpa only [Function.comp_def, Int.coe_castRingHom] using
    MvPolynomial.map_eval (Int.castRingHom (ZMod T)) x P

/-- The terminal phase reduces by actual integer casts, including its formal derivatives. -/
theorem terminalPhase_intCast {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (T : ℕ)
    (A alpha : ℤ) (ell y z : Fin n → ℤ) :
    ((terminalPhase F A ell alpha y z : ℤ) : ZMod T) =
      terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
        (fun i => (ell i : ZMod T)) (alpha : ZMod T)
        (fun i => (y i : ZMod T)) (fun i => (z i : ZMod T)) := by
  simp only [terminalPhase, quadraticAt, directional, dotProduct, gradient, pderiv_map,
    Int.cast_add, Int.cast_mul, Int.cast_sum, cast_eval_int]

/-- The literal standard-character version used by `terminalSum`.
No homomorphism between different residue rings is postulated. -/
theorem residueExponential_secondLift_stdAddChar {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (A T : ℕ) [NeZero A] [NeZero T] (a : ℤ) (y z v : Fin n → ℤ)
    (hs : ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) :
    residueExponential (A ^ 2 * T) (integerPhase F a (y + (A : ℤ) • z) v) =
      residueExponential (A ^ 2 * T) (integerPhase F a y v) *
        ZMod.stdAddChar
          (terminalPhase (MvPolynomial.map (Int.castRingHom (ZMod T)) F) (A : ZMod T)
            (fun i => (linearQuotient F A a y v i : ZMod T)) (a : ZMod T)
            (fun i => (y i : ZMod T)) (fun i => (z i : ZMod T))) := by
  rw [residueExponential_secondLift F hF A T a y z v hs,
    PrimeSumAdapter.residueExponential_eq_stdAddChar T, terminalPhase_intCast]
  simp only [Int.cast_natCast]

/-- Every integral polynomial has the same residue after a step divisible by the modulus. -/
theorem cast_eval_add_smul {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (y z : Fin n → ℤ) :
    (eval (y + (A : ℤ) • z) P : ZMod A) = (eval y P : ZMod A) := by
  have hc : (fun i => (((y + (A : ℤ) • z) i : ℤ) : ZMod A)) =
      (fun i => (y i : ZMod A)) := by
    funext i
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [cast_eval_int, cast_eval_int, hc]

/-- The two literal support conditions in the first lift depend only on `y mod A`.
This holds for every integral polynomial, without a homogeneity hypothesis. -/
theorem support_add_smul_iff {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (A : ℕ)
    (a : ℤ) (y z v : Fin n → ℤ) :
    ((A : ℤ) ∣ eval (y + (A : ℤ) • z) F ∧
      ∀ i, (A : ℤ) ∣ a * eval (y + (A : ℤ) • z) (pderiv i F) + v i) ↔
    ((A : ℤ) ∣ eval y F ∧ ∀ i, (A : ℤ) ∣ a * eval y (pderiv i F) + v i) := by
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul,
    cast_eval_add_smul]

end CubicTenVariables.SecondLiftPhase
