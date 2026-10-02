import HessianTheorem11.Geometry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The analytic derivative of an actual multivariate real polynomial.

The continuous linear map below is defined from the formal partial
derivatives, then proved to be the Fréchet derivative by polynomial
induction. Smoothness is proved by the same induction. No differentiability
or formal-to-analytic comparison is assumed as input. -/

noncomputable section
namespace CubicTenVariables.PolynomialCalculus
open scoped ContDiff
open MvPolynomial HessianTheorem11

/-- The continuous linear functional obtained by pairing the actual formal
gradient at `x` with a direction. -/
def evalDerivative {n : ℕ} (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval x (pderiv i F) • ContinuousLinearMap.proj i

@[simp]
theorem evalDerivative_apply {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    evalDerivative F x v = ∑ i, eval x (pderiv i F) * v i := by
  simp [evalDerivative, ContinuousLinearMap.sum_apply]

theorem evalDerivative_apply_eq_gradient {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    evalDerivative F x v = ∑ i, gradient F x i * v i :=
  evalDerivative_apply F x v

@[simp]
theorem evalDerivative_C {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    evalDerivative (C c) x = 0 := by
  simp [evalDerivative]

@[simp]
theorem evalDerivative_X {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    evalDerivative (X i) x = ContinuousLinearMap.proj i := by
  classical
  ext v
  simp [evalDerivative_apply, pderiv_X, Pi.single_apply]

theorem evalDerivative_add {n : ℕ} (F G : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    evalDerivative (F + G) x = evalDerivative F x + evalDerivative G x := by
  simp [evalDerivative, add_smul, Finset.sum_add_distrib]

theorem evalDerivative_mul {n : ℕ} (F G : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    evalDerivative (F * G) x =
      eval x F • evalDerivative G x + eval x G • evalDerivative F x := by
  ext v
  simp only [evalDerivative_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pderiv_mul, eval_add, eval_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Polynomial evaluation is a smooth function on the actual real Pi space. -/
theorem contDiff_eval {n : ℕ} (F : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => eval x F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin n → ℝ => c))
  | add F G hF hG => simpa only [eval_add] using hF.add hG
  | mul_X F i hF =>
      simpa only [eval_mul, eval_X] using hF.mul (contDiff_apply ℝ ℝ i)

/-- The gradient pairing is the actual Fréchet derivative of evaluation. -/
theorem hasFDerivAt_eval {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => eval y F) (evalDerivative F x) x := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using (hasFDerivAt_const c x)
  | add F G hF hG =>
      simpa only [eval_add, evalDerivative_add] using hF.add hG
  | mul_X F i hF =>
      simpa only [eval_mul, eval_X, evalDerivative_mul, evalDerivative_X] using
        hF.mul (hasFDerivAt_apply i x)

theorem fderiv_eval {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => eval y F) x = evalDerivative F x :=
  (hasFDerivAt_eval F x).fderiv

@[simp]
theorem evalDerivative_apply_single {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    evalDerivative F x (Pi.single i 1) = eval x (pderiv i F) := by
  classical
  simp [evalDerivative_apply, Pi.single_apply]

/-- Formal gradient nonsingularity is exactly nonvanishing of the actual
Fréchet derivative. -/
theorem evalDerivative_eq_zero_iff {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    evalDerivative F x = 0 ↔ gradient F x = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) h
    change evalDerivative F x (Pi.single i 1) = 0 at hi
    rw [evalDerivative_apply_single] at hi
    simpa [gradient] using hi
  · intro h
    ext v
    rw [evalDerivative_apply_eq_gradient, h]
    simp

theorem fderiv_eval_eq_zero_iff {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => eval y F) x = 0 ↔ gradient F x = 0 := by
  rw [fderiv_eval, evalDerivative_eq_zero_iff]

end CubicTenVariables.PolynomialCalculus
