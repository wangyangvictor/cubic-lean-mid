import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Elementary coordinate replacement for local real charts.

Replacing row i of the identity matrix by g gives determinant g i.
Consequently replacing the i-th coordinate of v by the actual linear
functional ∑ j, g j * v j is a continuous linear equivalence whenever
that coefficient is nonzero. No differentiability or inverse-function
hypothesis is assumed in this module.
-/
noncomputable section
namespace CubicTenVariables.CoordinateReplacement
open Matrix

/-- Identity matrix with one actual row replaced. -/
def rowReplacementMatrix {R : Type*} [Zero R] [One R] {n : ℕ}
    (i : Fin n) (g : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  (1 : Matrix (Fin n) (Fin n) R).updateRow i g

/-- The determinant is the coefficient in the replaced coordinate. -/
theorem rowReplacementMatrix_det {R : Type*} [CommRing R] {n : ℕ}
    (i : Fin n) (g : Fin n → R) : (rowReplacementMatrix i g).det = g i := by
  have hsum : (∑ k, g k • (1 : Matrix (Fin n) (Fin n) R) k) = g := by
    ext j
    simp [Matrix.one_apply, smul_eq_mul, mul_ite]
  have h := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) R) i g
  simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using h

/-- Matrix multiplication performs the literal coordinate update. -/
theorem rowReplacementMatrix_mulVec {R : Type*} [Semiring R] {n : ℕ}
    (i : Fin n) (g v : Fin n → R) :
    (rowReplacementMatrix i g).mulVec v =
      Function.update v i (∑ j, g j * v j) := by
  simp only [rowReplacementMatrix, Matrix.updateRow_mulVec, Matrix.one_mulVec, dotProduct]

/-- The real continuous linear map replacing coordinate i by g's pairing. -/
def coordinateReplacementCLM {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (rowReplacementMatrix i g).mulVecLin

@[simp] theorem coordinateReplacementCLM_apply {n : ℕ}
    (i : Fin n) (g v : Fin n → ℝ) :
    coordinateReplacementCLM i g v = Function.update v i (∑ j, g j * v j) :=
  rowReplacementMatrix_mulVec i g v

/-- The continuous map's actual linear determinant has the same value. -/
@[simp] theorem coordinateReplacementCLM_det {n : ℕ}
    (i : Fin n) (g : Fin n → ℝ) : (coordinateReplacementCLM i g).det = g i := by
  rw [coordinateReplacementCLM, LinearMap.det_toContinuousLinearMap]
  change LinearMap.det (Matrix.toLin' (rowReplacementMatrix i g)) = g i
  rw [LinearMap.det_toLin', rowReplacementMatrix_det]

/-- A nonzero coefficient makes the actual coordinate replacement a
continuous linear equivalence. The inverse is the inverse of this same map. -/
def coordinateReplacementCLE {n : ℕ}
    (i : Fin n) (g : Fin n → ℝ) (hg : g i ≠ 0) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (coordinateReplacementCLM i g).toContinuousLinearEquivOfDetNeZero
    (by simpa using hg)

@[simp] theorem coordinateReplacementCLE_toContinuousLinearMap {n : ℕ}
    (i : Fin n) (g : Fin n → ℝ) (hg : g i ≠ 0) :
    (coordinateReplacementCLE i g hg : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
      coordinateReplacementCLM i g := by
  simp only [coordinateReplacementCLE,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]

@[simp] theorem coordinateReplacementCLE_apply {n : ℕ}
    (i : Fin n) (g v : Fin n → ℝ) (hg : g i ≠ 0) :
    coordinateReplacementCLE i g hg v =
      Function.update v i (∑ j, g j * v j) := by
  simp only [coordinateReplacementCLE,
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply,
    coordinateReplacementCLM_apply]

/-- The selected output coordinate is exactly the specified linear pairing. -/
@[simp] theorem coordinateReplacementCLE_apply_same {n : ℕ}
    (i : Fin n) (g v : Fin n → ℝ) (hg : g i ≠ 0) :
    coordinateReplacementCLE i g hg v i = ∑ j, g j * v j := by
  simp [coordinateReplacementCLE_apply]

/-- Every other output coordinate is unchanged. -/
theorem coordinateReplacementCLE_apply_ne {n : ℕ}
    (i : Fin n) (g v : Fin n → ℝ) (hg : g i ≠ 0)
    (j : Fin n) (hji : j ≠ i) :
    coordinateReplacementCLE i g hg v j = v j := by
  simp only [coordinateReplacementCLE_apply, Function.update_of_ne hji]

end CubicTenVariables.CoordinateReplacement
