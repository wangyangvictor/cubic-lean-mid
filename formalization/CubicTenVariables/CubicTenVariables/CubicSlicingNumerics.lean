import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Numerical part of the ten-variable cubic slicing argument.
The hypotheses are displayed scalar inequalities; no geometric or
cohomological realization is asserted by this file. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CubicTenVariables.CubicSlicingNumerics

/-- The point count of projective r-space over a field with q elements. -/
def projectiveMainTerm (q : ℝ) (r : ℕ) : ℝ := ∑ i ∈ Finset.range (r + 1), q ^ i

theorem cone_mainTerm (q : ℝ) (r : ℕ) :
    1 + (q - 1) * projectiveMainTerm q r = q ^ (r + 1) := by
  rw [projectiveMainTerm, mul_geom_sum]
  ring

theorem projectiveMainTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (r : ℕ) :
    0 ≤ projectiveMainTerm q r :=
  Finset.sum_nonneg (fun _ _ => pow_nonneg hq _)

theorem projectiveMainTerm_le_two {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    projectiveMainTerm q r ≤ 2 * q ^ r := by
  apply (mul_le_mul_iff_left₀ (show 0 < q - 1 by linarith)).mp
  have hm := cone_mainTerm q r
  rw [pow_succ] at hm
  have hp := mul_nonneg (show 0 ≤ q - 2 by linarith) (pow_nonneg (by linarith : 0 ≤ q) r)
  nlinarith

theorem cone_error {q N A : ℝ} (r : ℕ) (hA : A = 1 + (q - 1) * N) :
    A - q ^ (r + 1) = (q - 1) * (N - projectiveMainTerm q r) := by
  have h := cone_mainTerm q r
  rw [hA]
  nlinarith

theorem projective_error_sq_of_cone {q N A B : ℝ} (hq : 1 < q) (r : ℕ)
    (hA : A = 1 + (q - 1) * N)
    (hbound : (A - q ^ (r + 1)) ^ 2 ≤ (q - 1) ^ 2 * B) :
    (N - projectiveMainTerm q r) ^ 2 ≤ B := by
  rw [cone_error r hA, mul_pow] at hbound
  exact le_of_mul_le_mul_left hbound (sq_pos_of_pos (sub_pos.mpr hq))

theorem sqrt_form {q : ℝ} (hq : 0 < q) :
    q ^ 6 * Real.sqrt q = q ^ ((13 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast q 6, ← Real.rpow_add hq]
  norm_num

/-- The selected-section variance and the smooth threefold Weil bound imply
the desired projective exponent, with the inessential constant 15. -/
theorem projective_slicing_bound {q N M : ℝ} (hq : 2 ≤ q)
    (hN : 0 ≤ N) (hsize : N ≤ 6 * q ^ 8)
    (hvariance : (N - q ^ 5 * M) ^ 2 ≤ 2 * N * (q ^ 5 - 1))
    (hsmooth : (M - projectiveMainTerm q 3) ^ 2 ≤ 100 * q ^ 3) :
    |N - projectiveMainTerm q 8| ≤ 15 * q ^ ((13 : ℝ) / 2) := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hroot : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hroot1 : 1 ≤ Real.sqrt q := by
    rw [Real.le_sqrt (by norm_num) hq0]
    nlinarith
  have hroot2 := Real.sq_sqrt hq0
  have hfive : 0 ≤ q ^ 5 - 1 := sub_nonneg.mpr (one_le_pow₀ hq1)
  have hv12 : (N - q ^ 5 * M) ^ 2 ≤ 12 * q ^ 13 := by
    calc
      _ ≤ 2 * N * (q ^ 5 - 1) := hvariance
      _ ≤ 2 * (6 * q ^ 8) * (q ^ 5 - 1) := by gcongr
      _ ≤ 12 * q ^ 13 := by nlinarith [pow_nonneg hq0 8]
  have hsquare4 : (4 * (q ^ 6 * Real.sqrt q)) ^ 2 = 16 * q ^ 13 := by
    rw [mul_pow, mul_pow, hroot2]
    ring
  have hv : |N - q ^ 5 * M| ≤ 4 * (q ^ 6 * Real.sqrt q) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [hsquare4]
    nlinarith [pow_nonneg hq0 13]
  have hsquare10 : (10 * q * Real.sqrt q) ^ 2 = 100 * q ^ 3 := by
    rw [mul_pow, hroot2]
    ring
  have hs : |M - projectiveMainTerm q 3| ≤ 10 * q * Real.sqrt q :=
    abs_le_of_sq_le_sq (hsmooth.trans_eq hsquare10.symm) (by positivity)
  have hpi4 : projectiveMainTerm q 4 ≤ q ^ 6 * Real.sqrt q := by
    calc
      _ ≤ 2 * q ^ 4 := projectiveMainTerm_le_two hq 4
      _ ≤ q * q ^ 4 := by gcongr
      _ = q ^ 5 := by ring
      _ ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by decide : 5 ≤ 6)
      _ ≤ q ^ 6 * Real.sqrt q := by nlinarith [pow_nonneg hq0 6]
  have hsplit : projectiveMainTerm q 8 =
      q ^ 5 * projectiveMainTerm q 3 + projectiveMainTerm q 4 := by
    norm_num [projectiveMainTerm, Finset.sum_range_succ]
    ring
  have htriangle : |N - projectiveMainTerm q 8| ≤
      |N - q ^ 5 * M| + q ^ 5 * |M - projectiveMainTerm q 3| +
        projectiveMainTerm q 4 := by
    rw [show N - projectiveMainTerm q 8 =
        (N - q ^ 5 * M) + q ^ 5 * (M - projectiveMainTerm q 3) -
          projectiveMainTerm q 4 by rw [hsplit]; ring]
    have h := (abs_sub ((N - q ^ 5 * M) + q ^ 5 * (M - projectiveMainTerm q 3))
      (projectiveMainTerm q 4)).trans
        (add_le_add (abs_add_le (N - q ^ 5 * M)
          (q ^ 5 * (M - projectiveMainTerm q 3))) (le_refl _))
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg hq0 5),
      abs_of_nonneg (projectiveMainTerm_nonneg hq0 4)] using h
  calc
    _ ≤ |N - q ^ 5 * M| + q ^ 5 * |M - projectiveMainTerm q 3| +
        projectiveMainTerm q 4 := htriangle
    _ ≤ 4 * (q ^ 6 * Real.sqrt q) + q ^ 5 * (10 * q * Real.sqrt q) +
        q ^ 6 * Real.sqrt q := by gcongr
    _ = 15 * (q ^ 6 * Real.sqrt q) := by ring
    _ = _ := by rw [sqrt_form (by linarith)]

/-- Small finite fields can be covered by the elementary degree bound alone.
The constant is intentionally loose; it does not affect the analytic exponents. -/
theorem small_field_projective_bound {q N : ℝ} (hq : 2 ≤ q) (hsmall : q ≤ 1440)
    (hN : 0 ≤ N) (hsize : N ≤ 6 * q ^ 8) :
    |N - projectiveMainTerm q 8| ≤ 330000 * q ^ ((13 : ℝ) / 2) := by
  have hq0 : 0 ≤ q := by linarith
  have hroot : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hroot38 : Real.sqrt q ≤ 38 := by
    apply (sq_le_sq₀ hroot (by norm_num : (0 : ℝ) ≤ 38)).mp
    rw [Real.sq_sqrt hq0]
    norm_num
    linarith
  have hbase : |N - projectiveMainTerm q 8| ≤ 6 * q ^ 8 := by
    apply abs_le.mpr
    have hpi0 := projectiveMainTerm_nonneg hq0 8
    have hpi := projectiveMainTerm_le_two hq 8
    constructor <;> nlinarith [pow_nonneg hq0 8]
  have hcoef : 6 * q * Real.sqrt q ≤ 330000 := by
    have h := mul_le_mul hsmall hroot38 hroot (by norm_num : (0 : ℝ) ≤ 1440)
    nlinarith
  have hfactor : 6 * q ^ 8 = (6 * q * Real.sqrt q) * (q ^ 6 * Real.sqrt q) := by
    calc
      _ = 6 * q ^ 7 * (Real.sqrt q) ^ 2 := by rw [Real.sq_sqrt hq0]; ring
      _ = _ := by ring
  calc
    _ ≤ 6 * q ^ 8 := hbase
    _ = (6 * q * Real.sqrt q) * (q ^ 6 * Real.sqrt q) := hfactor
    _ ≤ 330000 * (q ^ 6 * Real.sqrt q) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by rw [sqrt_form (by linarith)]

end CubicTenVariables.CubicSlicingNumerics
