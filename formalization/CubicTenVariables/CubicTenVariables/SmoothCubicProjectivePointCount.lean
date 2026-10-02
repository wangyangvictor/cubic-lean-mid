import CubicTenVariables.Literature.SmoothCubicWeil
import CubicTenVariables.ProjectiveFourierIdentity
import CubicTenVariables.ProjectiveLinearSectionPolynomialSelection
import CubicTenVariables.CubicSlicingNumerics

/-! Exact conversion of the concrete smooth-cubic Weil premise to actual
projective point counts, and an unconditional crude bound for arbitrary
nonzero ten-variable cubics. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.SmoothCubicProjectivePointCount
open MvPolynomial Literature ProjectiveFourierIdentity CubicSlicingNumerics

variable {K : Type} [Field K] [Fintype K] {n d : ℕ}

theorem real_affine_cone_card (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hd : 0 < d) :
    (affineZeroCount F : ℝ) = 1 + ((Fintype.card K : ℝ) - 1) *
      (Nat.card (zeroPoints F) : ℝ) := by
  have hc := affine_zero_card F hF hd
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hc' := congrArg (fun a : ℕ => (a : ℝ)) hc
  push_cast [Nat.cast_sub hq] at hc'
  change (affineZeroCount F : ℝ) = _ at hc'
  nlinarith

/-- The only unproved input here is the stated numerical smooth-cubic Weil bound. -/
theorem projective_error_sq (weil : SmoothCubicWeil) (r : ℕ)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (F : MvPolynomial (Fin (r + 2)) K)
    (hFne : F ≠ 0) (hF : F.IsHomogeneous 3) (hsmooth : ProjectivelySmooth F) :
    ((Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) r) ^ 2 ≤
      100 * (Fintype.card K : ℝ) ^ r := by
  have hq : (1 : ℝ) < Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  apply projective_error_sq_of_cone hq r (real_affine_cone_card F hF (by decide))
  convert weil r hr1 hr3 K F hFne hF hsmooth using 1 <;> ring

/-- The rough size bound used before choosing a smooth section needs only
Schwartz--Zippel and the exact cone identity. -/
theorem ten_variable_crude_bound (F : MvPolynomial (Fin 10) K)
    (hFne : F ≠ 0) (hF : F.IsHomogeneous 3) :
    (Nat.card (zeroPoints F) : ℝ) ≤ 6 * (Fintype.card K : ℝ) ^ 8 := by
  classical
  have hSZ := ProjectiveLinearSectionVariance.card_affine_polynomial_zeros_le_degree_mul
    (m := 9) (D := 3) F hFne hF.totalDegree_le
  have hA : (affineZeroCount F : ℝ) ≤ 3 * (Fintype.card K : ℝ) ^ 9 := by
    rw [affineZeroCount_eq_filter_card]
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hSZ)
  have hcone := real_affine_cone_card F hF (by decide)
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    have h : 2 ≤ Fintype.card K := Fintype.one_lt_card
    exact_mod_cast h
  have hN : (0 : ℝ) ≤ Nat.card (zeroPoints F) := Nat.cast_nonneg _
  have hhalf : (Fintype.card K : ℝ) / 2 ≤ (Fintype.card K : ℝ) - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hhalf hN
  have h : (Fintype.card K : ℝ) * (Nat.card (zeroPoints F) : ℝ) ≤
      (Fintype.card K : ℝ) * (6 * (Fintype.card K : ℝ) ^ 8) := by
    nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

end CubicTenVariables.SmoothCubicProjectivePointCount
