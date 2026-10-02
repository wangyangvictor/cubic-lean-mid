import CubicTenVariables.TranslatedIntegerBoxes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Literal integral coordinate changes preserve progression data and enlarge
real-centered boxes by one fixed coefficient constant. Rational invertibility
suffices; no invertibility modulo a sieve modulus is assumed. -/
noncomputable section
namespace CubicTenVariables.IntegralCoordinateBoxes
open scoped BigOperators

variable {n : ℕ}

def coefficientBound (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  max 1 (integerProjectionCoefficientBound A)

def realMatrix (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  A.map (Int.castRingHom ℝ)

theorem one_le_coefficientBound (A : Matrix (Fin n) (Fin n) ℤ) :
    1 ≤ coefficientBound A := le_max_left _ _

theorem cast_mulVec (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    (fun i => (A.mulVec x i : ℝ)) = (realMatrix A).mulVec (fun i => (x i : ℝ)) := by
  ext i
  simp [Matrix.mulVec,dotProduct,realMatrix]

theorem row_bound (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (∑ j, |(A i j : ℝ)|) ≤ (coefficientBound A : ℝ) := by
  have h := integerProjection_row_sum_le A i
  have h' : (∑ j, |(A i j : ℝ)|) ≤ (integerProjectionCoefficientBound A : ℝ) := by
    exact_mod_cast h
  exact h'.trans (by exact_mod_cast le_max_right 1 (integerProjectionCoefficientBound A))

theorem mulVec_coordinate_le (A : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L) (hz : ∀ i, |z i| ≤ L) (i : Fin n) :
    |(realMatrix A).mulVec z i| ≤ (coefficientBound A : ℝ)*L := by
  calc
    |(realMatrix A).mulVec z i| ≤ ∑ j, |(A i j : ℝ)*z j| :=
      by simpa only [realMatrix,Matrix.mulVec,dotProduct,Matrix.map_apply] using
        Finset.abs_sum_le_sum_abs (fun j => (A i j : ℝ)*z j) Finset.univ
    _ = ∑ j, |(A i j : ℝ)| * |z j| := by simp only [abs_mul]
    _ ≤ ∑ j, |(A i j : ℝ)| * L :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
    _ = (∑ j, |(A i j : ℝ)|)*L := (Finset.sum_mul ..).symm
    _ ≤ (coefficientBound A : ℝ)*L := mul_le_mul_of_nonneg_right (row_bound A i) hL

theorem transformed_box (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hx : ∀ i, |(x i : ℝ)-u i| ≤ L) :
    ∀ i, |(A.mulVec x i : ℝ)-(realMatrix A).mulVec u i| ≤
      (coefficientBound A : ℝ)*L := by
  intro i
  have h := mulVec_coordinate_le A ((fun j => (x j : ℝ))-u) L hL hx i
  rw [Matrix.mulVec_sub,←cast_mulVec] at h
  exact h

theorem transformed_center_norm (A : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℝ) :
    ‖(realMatrix A).mulVec u‖ ≤ (coefficientBound A : ℝ)*‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  apply mulVec_coordinate_le A u ‖u‖ (norm_nonneg _) _ i
  intro j
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm u j

theorem transformed_progression (A : Matrix (Fin n) (Fin n) ℤ)
    (x b : Fin n → ℤ) (m : ℕ) (hx : ∀ j, (m : ℤ) ∣ x j-b j) :
    ∀ i, (m : ℤ) ∣ A.mulVec x i-A.mulVec b i := by
  intro i
  rw [←Pi.sub_apply,←Matrix.mulVec_sub]
  change (m : ℤ) ∣ ∑ j, A i j*(x j-b j)
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (hx j) (A i j)

/-- A rationally invertible integral matrix is injective on integral points,
including at every prime dividing its determinant. -/
theorem mulVec_injective (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (A.map (Int.castRingHom ℚ)).det ≠ 0) : Function.Injective A.mulVec := by
  have hinj := Matrix.mulVec_injective_iff.mpr (Matrix.linearIndependent_cols_of_det_ne_zero hA)
  intro x y hxy
  have he : (A.map (Int.castRingHom ℚ)).mulVec (fun i => (x i : ℚ)) =
      (A.map (Int.castRingHom ℚ)).mulVec (fun i => (y i : ℚ)) := by
    ext i
    have h := congrArg (fun z : Fin n → ℤ => (z i : ℚ)) hxy
    simpa [Matrix.mulVec,dotProduct] using h
  have h := hinj he
  funext i
  exact_mod_cast congrFun h i

end CubicTenVariables.IntegralCoordinateBoxes
