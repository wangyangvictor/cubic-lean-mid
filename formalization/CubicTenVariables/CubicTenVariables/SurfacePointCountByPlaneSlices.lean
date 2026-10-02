import CubicTenVariables.BinarySliceGeometry
import CubicTenVariables.FiniteFieldPolynomialZeros
import CubicTenVariables.Literature.AffinePlaneCurveWeil
import Mathlib.Data.Real.Sqrt

/-!
# Counting an affine surface by a pencil of plane curves

This file contains the finite-field counting part of the fixed-projection
argument.  Every surface point is put in its actual plane-curve fiber.  Away
from the zeros of one displayed parameter polynomial, the only literature
input is `Literature.AffinePlaneCurveWeil`.  Exceptional fibers are bounded
by Schwartz--Zippel.

The hypothesis that every fiber polynomial is nonzero is deliberately
literal.  It is the flatness/monicity condition needed to prevent an entire
affine plane from occurring as one exceptional fiber; such a fiber would
destroy the leading coefficient one in the surface estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace CubicTenVariables.SurfacePointCountByPlaneSlices

open MvPolynomial
open scoped BigOperators Classical
open BinarySliceCounting BinarySliceGeometry FiniteFieldPolynomialZeros

/-- The squared affine curve-Weil estimate implies its usual square-root
upper bound. -/
theorem curve_zero_count_le_sqrt
    {K : Type} [Field K] [Fintype K]
    (f : MvPolynomial (Fin 2) K) (B : ℝ)
    (hweil : (((Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
      (Fintype.card K : ℝ)) ^ 2 ≤ B * (Fintype.card K : ℝ))) :
    (Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) ≤
      (Fintype.card K : ℝ) + Real.sqrt (B * (Fintype.card K : ℝ)) := by
  let x : ℝ := (Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
    (Fintype.card K : ℝ)
  have hsqrt : |x| ≤ Real.sqrt (B * (Fintype.card K : ℝ)) := by
    calc
      |x| = Real.sqrt (x ^ 2) := by simpa using (Real.sqrt_sq_eq_abs x).symm
      _ ≤ Real.sqrt (B * (Fintype.card K : ℝ)) := Real.sqrt_le_sqrt hweil
  dsimp only [x] at hsqrt
  linarith [le_abs_self ((Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
    (Fintype.card K : ℝ))]

/-- Exact decomposition of the literal affine surface zero set into the
literal zero sets of its binary slices. -/
theorem surface_zero_count_eq_sum_slice_counts
    {K : Type} [Field K] [Fintype K]
    (e : Fin 2 ↪ Fin 3) (f : MvPolynomial (Fin 3) K) :
    Nat.card {x : Fin 3 → K // eval x f = 0} =
      ∑ w : Complement e → K,
        Nat.card {z : Fin 2 → K // eval z (slice e f w) = 0} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [card_filter_eq_sum_slices e (fun x : Fin 3 → K => eval x f = 0)]
  apply Finset.sum_congr rfl
  intro w _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eval_slice]

/-- A nonzero one-variable parameter polynomial has at most its total degree
many zeros.  Here the one parameter is the actual complement of a selected
pair of coordinates in `Fin 3`. -/
theorem card_exceptional_parameters_le
    {K : Type} [Field K] [Fintype K]
    (e : Fin 2 ↪ Fin 3) (g : MvPolynomial (Complement e) K) (hg : g ≠ 0) :
    (zeros g).card ≤ g.totalDegree := by
  have h := card_zeros_le_totalDegree_mul g hg
  simpa only [card_complement, Nat.reduceSub, pow_zero, mul_one] using h

/-- Finite-fiber assembly for a fixed plane-curve pencil.  The exceptional
polynomial and all fiber hypotheses are concrete; the only point-count input
is the displayed degree-uniform affine curve Weil proposition. -/
theorem surface_zero_count_le_of_plane_slices
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (g : MvPolynomial (Complement e) K)
    (hfdeg : f.totalDegree ≤ d) (hg : g ≠ 0)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, eval w g ≠ 0 →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, eval w g ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (slice e f w)})) :
    (Nat.card {x : Fin 3 → K // eval x f = 0} : ℝ) ≤
      (Fintype.card K : ℝ) ^ 2 +
      (Fintype.card K : ℝ) * Real.sqrt
        ((Classical.choose (curveWeil d hd)) * (Fintype.card K : ℝ)) +
      (g.totalDegree : ℝ) * (d : ℝ) * (Fintype.card K : ℝ) := by
  let B : ℝ := Classical.choose (curveWeil d hd)
  have hBdata := Classical.choose_spec (curveWeil d hd)
  have hB : 1 ≤ B := hBdata.1
  have hWeil := hBdata.2
  let q : ℝ := Fintype.card K
  let c : (Complement e → K) → ℕ := fun w =>
    Nat.card {z : Fin 2 → K // eval z (slice e f w) = 0}
  have hslice : ∀ w : Complement e → K,
      (c w : ℝ) ≤ q + Real.sqrt (B * q) +
        (if eval w g = 0 then (d : ℝ) * q else 0) := by
    intro w
    by_cases hw : eval w g = 0
    · have hzNat : c w ≤ d * Fintype.card K := by
        dsimp only [c]
        rw [natCard_zeros]
        have hs := card_zeros_le_degree_mul (slice e f w) (hall w) d
          ((totalDegree_slice_le e f w).trans hfdeg)
        simpa only [Fintype.card_fin, Nat.reduceSub, pow_one] using hs
      simp only [hw, if_pos]
      have hzReal : (c w : ℝ) ≤ (d : ℝ) * q := by
        dsimp only [q]
        exact_mod_cast hzNat
      have hq : 0 ≤ q := by positivity
      have hsqrt : 0 ≤ Real.sqrt (B * q) := Real.sqrt_nonneg _
      linarith
    · have hwWeil := hWeil K (slice e f w) (hgoodDegree w hw)
        ((totalDegree_slice_le e f w).trans hfdeg) (hgoodIntegral w hw)
      have hc := curve_zero_count_le_sqrt (slice e f w) B hwWeil
      rw [if_neg hw, add_zero]
      simpa only [c, q] using hc
  have hsum : (∑ w : Complement e → K, (c w : ℝ)) ≤
      ∑ w : Complement e → K,
        (q + Real.sqrt (B * q) +
          (if eval w g = 0 then (d : ℝ) * q else 0)) :=
    Finset.sum_le_sum fun w _ => hslice w
  have hparamCard : Fintype.card (Complement e → K) = Fintype.card K := by
    simp only [Fintype.card_fun, card_complement, Nat.reduceSub, pow_one]
  have hbad : ((zeros g).card : ℝ) ≤ (g.totalDegree : ℝ) := by
    exact_mod_cast card_exceptional_parameters_le e g hg
  have hindicator : (∑ w : Complement e → K,
      if eval w g = 0 then (d : ℝ) * (Fintype.card K : ℝ) else 0) =
      ((zeros g).card : ℝ) * ((d : ℝ) * (Fintype.card K : ℝ)) := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun w : Complement e → K => eval w g = 0) =
        zeros g := by
      ext w
      simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  rw [surface_zero_count_eq_sum_slice_counts e f]
  rw [Nat.cast_sum]
  calc
    (∑ w : Complement e → K, (c w : ℝ))
        ≤ ∑ w : Complement e → K,
          (q + Real.sqrt (B * q) +
            (if eval w g = 0 then (d : ℝ) * q else 0)) := hsum
    _ = q ^ 2 + q * Real.sqrt (B * q) +
          ((zeros g).card : ℝ) * ((d : ℝ) * q) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hparamCard, q]
      rw [hindicator]
      ring
    _ ≤ q ^ 2 + q * Real.sqrt (B * q) +
          (g.totalDegree : ℝ) * (d : ℝ) * q := by
      have hdq : 0 ≤ (d : ℝ) * q := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hbad hdq]

/-- The two explicit lower bounds on the field size absorb the curve-Weil
error and the finitely many exceptional fibers into any prescribed leading
constant `K₀ > 1`. -/
theorem surface_error_le_K_mul_sq
    (B C q K₀ : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hq : 0 < q) (hK : 1 < K₀)
    (hcurve : 4 * B ≤ (K₀ - 1) ^ 2 * q)
    (hexceptional : 2 * C ≤ (K₀ - 1) * q) :
    q ^ 2 + q * Real.sqrt (B * q) + C * q ≤ K₀ * q ^ 2 := by
  have hε : 0 < K₀ - 1 := sub_pos.mpr hK
  have hroot : 0 ≤ Real.sqrt (B * q) := Real.sqrt_nonneg _
  have hroot_sq : (Real.sqrt (B * q)) ^ 2 = B * q :=
    Real.sq_sqrt (mul_nonneg hB hq.le)
  have hcurve' : 4 * (B * q) ≤ ((K₀ - 1) * q) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hcurve hq.le
    nlinarith
  have hroot_bound : 2 * Real.sqrt (B * q) ≤ (K₀ - 1) * q := by
    nlinarith [sq_nonneg (2 * Real.sqrt (B * q) + (K₀ - 1) * q)]
  nlinarith

/-- Leading-one surface bound for one literal finite-field pencil.  Its
large-field conditions are explicit and uniform once the fixed exceptional
degree bound `Dg` is supplied. -/
theorem surface_zero_count_le_K_mul_sq_of_plane_slices
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (g : MvPolynomial (Complement e) K)
    (Dg : ℕ) (hgdeg : g.totalDegree ≤ Dg)
    (hfdeg : f.totalDegree ≤ d) (hg : g ≠ 0)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, eval w g ≠ 0 →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, eval w g ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (slice e f w)}))
    (K₀ : ℝ) (hK₀ : 1 < K₀)
    (hcurveLarge : 4 * Classical.choose (curveWeil d hd) ≤
      (K₀ - 1) ^ 2 * (Fintype.card K : ℝ))
    (hexceptionalLarge : 2 * ((Dg : ℝ) * (d : ℝ)) ≤
      (K₀ - 1) * (Fintype.card K : ℝ)) :
    (Nat.card {x : Fin 3 → K // eval x f = 0} : ℝ) ≤
      K₀ * (Fintype.card K : ℝ) ^ 2 := by
  let B : ℝ := Classical.choose (curveWeil d hd)
  let q : ℝ := Fintype.card K
  have hB : 0 ≤ B := le_trans (by norm_num) (Classical.choose_spec (curveWeil d hd)).1
  have hq : 0 < q := by positivity
  have hC : 0 ≤ (g.totalDegree : ℝ) * (d : ℝ) := by positivity
  have hcurve : 4 * B ≤ (K₀ - 1) ^ 2 * q := by
    simpa only [B, q] using hcurveLarge
  have hexceptional : 2 * ((g.totalDegree : ℝ) * (d : ℝ)) ≤
      (K₀ - 1) * q := by
    have hdegree : (g.totalDegree : ℝ) ≤ (Dg : ℝ) := by exact_mod_cast hgdeg
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hmul := mul_le_mul_of_nonneg_right hdegree hd0
    linarith
  have hcount := surface_zero_count_le_of_plane_slices curveWeil d hd e f g
    hfdeg hg hall hgoodDegree hgoodIntegral
  have herror := surface_error_le_K_mul_sq B
    ((g.totalDegree : ℝ) * (d : ℝ)) q K₀ hB hC hq hK₀ hcurve hexceptional
  exact hcount.trans (by simpa only [B, q, mul_assoc] using herror)

/-- An explicit field-cardinality threshold for the leading constant `K₀`.
It depends only on the degree, the fixed exceptional-polynomial degree bound,
and the degree-uniform affine curve-Weil constant. -/
def surfaceSliceThreshold
    (curveWeil : Literature.AffinePlaneCurveWeil)
    (d : ℕ) (hd : 1 ≤ d) (Dg : ℕ) (K₀ : ℝ) : ℝ :=
  max
    (4 * Classical.choose (curveWeil d hd) / (K₀ - 1) ^ 2)
    (2 * ((Dg : ℝ) * (d : ℝ)) / (K₀ - 1))

theorem surfaceSliceThreshold_nonneg
    (curveWeil : Literature.AffinePlaneCurveWeil)
    (d : ℕ) (hd : 1 ≤ d) (Dg : ℕ) (K₀ : ℝ) (_hK₀ : 1 < K₀) :
    0 ≤ surfaceSliceThreshold curveWeil d hd Dg K₀ := by
  unfold surfaceSliceThreshold
  exact (show 0 ≤ 4 * Classical.choose (curveWeil d hd) / (K₀ - 1) ^ 2 by
    have hB := (Classical.choose_spec (curveWeil d hd)).1
    positivity).trans (le_max_left _ _)

/-- The large-field version of
`surface_zero_count_le_K_mul_sq_of_plane_slices`, with the two numerical
hypotheses packaged into one explicit threshold. -/
theorem surface_zero_count_le_K_mul_sq_of_card_ge
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (g : MvPolynomial (Complement e) K)
    (Dg : ℕ) (hgdeg : g.totalDegree ≤ Dg)
    (hfdeg : f.totalDegree ≤ d) (hg : g ≠ 0)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, eval w g ≠ 0 →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, eval w g ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (slice e f w)}))
    (K₀ : ℝ) (hK₀ : 1 < K₀)
    (hcard : surfaceSliceThreshold curveWeil d hd Dg K₀ ≤
      (Fintype.card K : ℝ)) :
    (Nat.card {x : Fin 3 → K // eval x f = 0} : ℝ) ≤
      K₀ * (Fintype.card K : ℝ) ^ 2 := by
  have hε : 0 < K₀ - 1 := sub_pos.mpr hK₀
  have hεsq : 0 < (K₀ - 1) ^ 2 := sq_pos_of_pos hε
  have hfirst : 4 * Classical.choose (curveWeil d hd) / (K₀ - 1) ^ 2 ≤
      (Fintype.card K : ℝ) :=
    (le_max_left _ _).trans hcard
  have hsecond : 2 * ((Dg : ℝ) * (d : ℝ)) / (K₀ - 1) ≤
      (Fintype.card K : ℝ) :=
    (le_max_right _ _).trans hcard
  have hcurveLarge : 4 * Classical.choose (curveWeil d hd) ≤
      (K₀ - 1) ^ 2 * (Fintype.card K : ℝ) := by
    have h := (div_le_iff₀ hεsq).mp hfirst
    nlinarith
  have hexceptionalLarge : 2 * ((Dg : ℝ) * (d : ℝ)) ≤
      (K₀ - 1) * (Fintype.card K : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hsecond
  exact surface_zero_count_le_K_mul_sq_of_plane_slices curveWeil d hd e f g Dg
    hgdeg hfdeg hg hall hgoodDegree hgoodIntegral K₀ hK₀ hcurveLarge
    hexceptionalLarge

end CubicTenVariables.SurfacePointCountByPlaneSlices
