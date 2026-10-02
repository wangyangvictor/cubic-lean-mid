import CubicTenVariables.FixedLeadingSurfaceNormalizedPrimeCount
import CubicTenVariables.AffineFourCountByParallelSlices

/-! The fixed determinant normalization changes the integer box by one
explicit factor, independent of the varying equation and its coefficients. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceCoordinateBoxCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceNormalizedPrimeCount
open AffineFourCountByParallelSlices

def boxFactor (a b : ℤ) : ℝ := 1 + |(a : ℝ)| + |(b : ℝ)|

theorem one_le_boxFactor (a b : ℤ) : 1 ≤ boxFactor a b := by
  dsimp [boxFactor]
  linarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ)]

/-- The actual inverse integral point map has this uniform row-sum bound. -/
theorem inverse_coordinate_mem_box
    (a b : ℤ) (x : IntVector 3) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ i, |(x i : ℝ)| ≤ B) :
    ∀ i, |((coordinatePointEquiv a b).symm x i : ℝ)| ≤ boxFactor a b * B := by
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 2
  have habsA := abs_nonneg (a : ℝ)
  have habsB := abs_nonneg (b : ℝ)
  intro i
  fin_cases i
  · change |((x 1 - a * x 0 : ℤ) : ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(x 1 : ℝ)| + |(a : ℝ) * (x 0 : ℝ)| := abs_sub _ _
      _ = |(x 1 : ℝ)| + |(a : ℝ)| * |(x 0 : ℝ)| := by rw [abs_mul]
      _ ≤ B + |(a : ℝ)| * B := add_le_add hx1 (mul_le_mul_of_nonneg_left hx0 habsA)
      _ ≤ boxFactor a b * B := by dsimp [boxFactor]; nlinarith
  · change |((x 2 - b * x 0 : ℤ) : ℝ)| ≤ _
    push_cast
    calc
      _ ≤ |(x 2 : ℝ)| + |(b : ℝ) * (x 0 : ℝ)| := abs_sub _ _
      _ = |(x 2 : ℝ)| + |(b : ℝ)| * |(x 0 : ℝ)| := by rw [abs_mul]
      _ ≤ B + |(b : ℝ)| * B := add_le_add hx2 (mul_le_mul_of_nonneg_left hx0 habsB)
      _ ≤ boxFactor a b * B := by dsimp [boxFactor]; nlinarith
  · change |(x 0 : ℝ)| ≤ _
    exact hx0.trans (by nlinarith [one_le_boxFactor a b])

theorem affineHypersurface_card_le_coordinateEquiv
    (a b : ℤ) (g : MvPolynomial (Fin 3) ℤ)
    (B : ℝ) (hB : 0 ≤ B) :
    (affineHypersurfaceIntegerPoints g B).card ≤
      (affineHypersurfaceIntegerPoints (coordinateEquiv a b g)
        (boxFactor a b * B)).card := by
  classical
  apply Finset.card_le_card_of_injOn (coordinatePointEquiv a b).symm
  · intro x hx
    obtain ⟨hbox, hzero⟩ := (mem_affineHypersurfaceIntegerPoints_iff g B x).mp hx
    apply (mem_affineHypersurfaceIntegerPoints_iff _ _ _).mpr
    refine ⟨inverse_coordinate_mem_box a b x B hB hbox, ?_⟩
    rw [eval_coordinateEquiv, ← coordinatePointEquiv_eq_mulVec,
      Equiv.apply_symm_apply]
    exact hzero
  · exact fun _ _ _ _ h => (coordinatePointEquiv a b).symm.injective h

/-- A normalized surface bound transfers with the same exponent. -/
theorem affineHypersurface_bound_of_coordinateEquiv
    (a b : ℤ) (g : MvPolynomial (Fin 3) ℤ)
    (B C α : ℝ) (hB : 0 ≤ B)
    (hcount : ((affineHypersurfaceIntegerPoints (coordinateEquiv a b g)
      (boxFactor a b * B)).card : ℝ) ≤ C * (boxFactor a b * B) ^ α) :
    ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
      (C * boxFactor a b ^ α) * B ^ α := by
  have hcard : ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
      ((affineHypersurfaceIntegerPoints (coordinateEquiv a b g)
        (boxFactor a b * B)).card : ℝ) := by
    exact_mod_cast affineHypersurface_card_le_coordinateEquiv a b g B hB
  calc
    _ ≤ C * (boxFactor a b * B) ^ α := hcard.trans hcount
    _ = _ := by
      rw [Real.mul_rpow (le_trans (by norm_num) (one_le_boxFactor a b)) hB]
      ring

end CubicTenVariables.FixedLeadingSurfaceCoordinateBoxCount
