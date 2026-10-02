import HessianTheorem11.Geometry
import CubicTenVariables.CoordinateReplacement
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual polynomial coordinate charts over complete nontrivially normed fields.

The formal gradient is proved to give the strict derivative of actual
polynomial evaluation. The inverse function theorem therefore applies also
to p-adic fields, with no analytic chart or differentiability input.
-/

noncomputable section
namespace CubicTenVariables.NormedPolynomialChart
open scoped ContDiff
open MvPolynomial HessianTheorem11
open scoped Topology

variable {K : Type*} [NontriviallyNormedField K]

/-- The continuous linear functional obtained by pairing the actual formal
gradient at `x` with a direction. -/
def evalDerivative {n : ℕ} (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    (Fin n → K) →L[K] K :=
  ∑ i, eval x (pderiv i F) • ContinuousLinearMap.proj i

@[simp]
theorem evalDerivative_apply {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x v : Fin n → K) :
    evalDerivative F x v = ∑ i, eval x (pderiv i F) * v i := by
  simp [evalDerivative, ContinuousLinearMap.sum_apply]

theorem evalDerivative_apply_eq_gradient {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x v : Fin n → K) :
    evalDerivative F x v = ∑ i, gradient F x i * v i :=
  evalDerivative_apply F x v

@[simp]
theorem evalDerivative_C {n : ℕ} (c : K) (x : Fin n → K) :
    evalDerivative (C c) x = 0 := by
  ext v
  simp [evalDerivative_apply]

@[simp]
theorem evalDerivative_X {n : ℕ} (i : Fin n) (x : Fin n → K) :
    evalDerivative (X i) x = ContinuousLinearMap.proj i := by
  classical
  ext v
  simp [evalDerivative_apply, pderiv_X, Pi.single_apply]

theorem evalDerivative_add {n : ℕ} (F G : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    evalDerivative (F + G) x = evalDerivative F x + evalDerivative G x := by
  ext v
  simp [evalDerivative_apply, add_mul, Finset.sum_add_distrib]

theorem evalDerivative_mul {n : ℕ} (F G : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    evalDerivative (F * G) x =
      eval x F • evalDerivative G x + eval x G • evalDerivative F x := by
  ext v
  simp only [evalDerivative_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pderiv_mul, eval_add, eval_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Polynomial evaluation is a smooth function on the actual normed Pi space. -/
theorem contDiff_eval {n : ℕ} (F : MvPolynomial (Fin n) K) :
    ContDiff K ∞ (fun x : Fin n → K => eval x F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff K ∞ (fun _ : Fin n → K => c))
  | add F G hF hG => simpa only [eval_add] using hF.add hG
  | mul_X F i hF =>
      simpa only [eval_mul, eval_X] using hF.mul (contDiff_apply K K i)

/-- The gradient pairing is the actual Fréchet derivative of evaluation. -/
theorem hasFDerivAt_eval {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    HasFDerivAt (fun y : Fin n → K => eval y F) (evalDerivative F x) x := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using (hasFDerivAt_const c x)
  | add F G hF hG =>
      simpa only [eval_add, evalDerivative_add] using hF.add hG
  | mul_X F i hF =>
      simpa only [eval_mul, eval_X, evalDerivative_mul, evalDerivative_X] using
        hF.mul (hasFDerivAt_apply i x)

theorem fderiv_eval {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    fderiv K (fun y : Fin n → K => eval y F) x = evalDerivative F x :=
  (hasFDerivAt_eval F x).fderiv

@[simp]
theorem evalDerivative_apply_single {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) (i : Fin n) :
    evalDerivative F x (Pi.single i 1) = eval x (pderiv i F) := by
  classical
  simp [evalDerivative_apply, Pi.single_apply]

/-- Formal gradient nonsingularity is exactly nonvanishing of the actual
Fréchet derivative. -/
theorem evalDerivative_eq_zero_iff {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    evalDerivative F x = 0 ↔ gradient F x = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := congrArg (fun L : (Fin n → K) →L[K] K => L (Pi.single i 1)) h
    change evalDerivative F x (Pi.single i 1) = 0 at hi
    rw [evalDerivative_apply_single] at hi
    simpa [gradient] using hi
  · intro h
    ext v
    rw [evalDerivative_apply_eq_gradient, h]
    simp

theorem fderiv_eval_eq_zero_iff {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    fderiv K (fun y : Fin n → K => eval y F) x = 0 ↔ gradient F x = 0 := by
  rw [fderiv_eval, evalDerivative_eq_zero_iff]



/-- Strict differentiability over the coefficient field, including Q_p. -/
theorem hasStrictFDerivAt_eval {n : ℕ} (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) :
    HasStrictFDerivAt (fun y : Fin n → K => eval y F) (evalDerivative F x) x := by
  induction F using MvPolynomial.induction_on with
  | C c => simpa using (hasStrictFDerivAt_const c x)
  | add F G hF hG =>
      simpa only [eval_add, evalDerivative_add] using hF.add hG
  | mul_X F i hF =>
      simpa only [eval_mul, eval_X, evalDerivative_mul, evalDerivative_X] using
        hF.mul (hasStrictFDerivAt_apply i x)

variable [CompleteSpace K]

/-- The actual derivative of coordinate replacement, as a continuous map. -/
def coordinateReplacementCLM {n : ℕ} (i : Fin n) (g : Fin n → K) :
    (Fin n → K) →L[K] (Fin n → K) :=
  LinearMap.toContinuousLinearMap
    (CoordinateReplacement.rowReplacementMatrix i g).mulVecLin

@[simp] theorem coordinateReplacementCLM_apply {n : ℕ}
    (i : Fin n) (g v : Fin n → K) :
    coordinateReplacementCLM i g v = Function.update v i (∑ j, g j * v j) :=
  CoordinateReplacement.rowReplacementMatrix_mulVec i g v

@[simp] theorem coordinateReplacementCLM_det {n : ℕ}
    (i : Fin n) (g : Fin n → K) : (coordinateReplacementCLM i g).det = g i := by
  rw [coordinateReplacementCLM, LinearMap.det_toContinuousLinearMap]
  change LinearMap.det (Matrix.toLin' (CoordinateReplacement.rowReplacementMatrix i g)) = g i
  rw [LinearMap.det_toLin', CoordinateReplacement.rowReplacementMatrix_det]

def coordinateReplacementCLE {n : ℕ}
    (i : Fin n) (g : Fin n → K) (hg : g i ≠ 0) :
    (Fin n → K) ≃L[K] (Fin n → K) :=
  (coordinateReplacementCLM i g).toContinuousLinearEquivOfDetNeZero
    (by simpa using hg)

@[simp] theorem coordinateReplacementCLE_toContinuousLinearMap {n : ℕ}
    (i : Fin n) (g : Fin n → K) (hg : g i ≠ 0) :
    (coordinateReplacementCLE i g hg : (Fin n → K) →L[K] (Fin n → K)) =
      coordinateReplacementCLM i g := by
  simp only [coordinateReplacementCLE,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]

/-- Replace the selected coordinate by the actual polynomial value. -/
def coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) K) (i : Fin n)
    (x : Fin n → K) : Fin n → K :=
  Function.update x i (eval x F)

@[simp] theorem coordinateMap_apply_same {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) : coordinateMap F i x i = eval x F := by
  simp [coordinateMap]

theorem coordinateMap_apply_ne {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) (j : Fin n) (hji : j ≠ i) :
    coordinateMap F i x j = x j := by
  simp [coordinateMap, hji]

theorem coordinateReplacement_proj_same {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) :
    (ContinuousLinearMap.proj i).comp (coordinateReplacementCLM i (gradient F x)) =
      evalDerivative F x := by
  ext v
  simp [gradient]

theorem coordinateReplacement_proj_ne {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) (j : Fin n) (hji : j ≠ i) :
    (ContinuousLinearMap.proj j).comp (coordinateReplacementCLM i (gradient F x)) =
      ContinuousLinearMap.proj j := by
  ext v
  simp [hji]

/-- The polynomial coordinate map has the literal invertible strict derivative. -/
theorem hasStrictFDerivAt_coordinateMap {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) :
    HasStrictFDerivAt (coordinateMap F i) (coordinateReplacementCLM i (gradient F x)) x := by
  apply hasStrictFDerivAt_pi'.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [coordinateMap_apply_same, coordinateReplacement_proj_same] using
      hasStrictFDerivAt_eval F x
  · simpa only [coordinateMap_apply_ne F i _ j hji,
      coordinateReplacement_proj_ne F i x j hji] using hasStrictFDerivAt_apply j x

/-- A genuine inverse-function chart over the complete coefficient field. -/
def coordinateChart {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) (hi : eval x (pderiv i F) ≠ 0) :
    OpenPartialHomeomorph (Fin n → K) (Fin n → K) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (coordinateMap F i)
    (f' := coordinateReplacementCLE i (gradient F x) hi)
    (by simpa using hasStrictFDerivAt_coordinateMap F i x)

@[simp] theorem coordinateChart_coe {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) (hi : eval x (pderiv i F) ≠ 0) :
    (coordinateChart F i x hi : (Fin n → K) → (Fin n → K)) = coordinateMap F i := rfl

theorem mem_coordinateChart_source {n : ℕ} (F : MvPolynomial (Fin n) K)
    (i : Fin n) (x : Fin n → K) (hi : eval x (pderiv i F) ≠ 0) :
    x ∈ (coordinateChart F i x hi).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

end CubicTenVariables.NormedPolynomialChart
