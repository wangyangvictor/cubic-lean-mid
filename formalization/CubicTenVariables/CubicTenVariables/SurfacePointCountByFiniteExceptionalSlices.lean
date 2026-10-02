import CubicTenVariables.SurfacePointCountByPlaneSlices

/-!
# Finite exceptional sets in a surface slicing count

The pencil at infinity uses reciprocal affine parameters. Counting its bad
parameters as a finite set avoids manufacturing a reciprocal polynomial.
The good fibres use the accepted affine curve Weil input; every exceptional
fibre must still have a nonzero literal equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.SurfacePointCountByFiniteExceptionalSlices
open MvPolynomial
open SurfacePointCountByPlaneSlices
open BinarySliceCounting BinarySliceGeometry FiniteFieldPolynomialZeros
open scoped BigOperators Classical

theorem surface_zero_count_le_of_finite_exceptional_slices
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (bad : Finset (Complement e → K))
    (hfdeg : f.totalDegree ≤ d)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, w ∉ bad →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, w ∉ bad →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) (slice e f w)})) :
    (Nat.card {x : Fin 3 → K // eval x f = 0} : ℝ) ≤
      (Fintype.card K : ℝ) ^ 2 +
      (Fintype.card K : ℝ) * Real.sqrt
        ((Classical.choose (curveWeil d hd)) * (Fintype.card K : ℝ)) +
      (bad.card : ℝ) * (d : ℝ) * (Fintype.card K : ℝ) := by
  let B : ℝ := Classical.choose (curveWeil d hd)
  have hBdata := Classical.choose_spec (curveWeil d hd)
  have hB : 1 ≤ B := hBdata.1
  have hWeil := hBdata.2
  let q : ℝ := Fintype.card K
  let c : (Complement e → K) → ℕ := fun w =>
    Nat.card {z : Fin 2 → K // eval z (slice e f w) = 0}
  have hslice : ∀ w : Complement e → K,
      (c w : ℝ) ≤ q + Real.sqrt (B * q) +
        (if w ∈ bad then (d : ℝ) * q else 0) := by
    intro w
    by_cases hw : w ∈ bad
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
          (if w ∈ bad then (d : ℝ) * q else 0)) :=
    Finset.sum_le_sum fun w _ => hslice w
  have hparamCard : Fintype.card (Complement e → K) = Fintype.card K := by
    simp only [Fintype.card_fun, card_complement, Nat.reduceSub, pow_one]
  have hbad : (bad.card : ℝ) ≤ (bad.card : ℝ) := by
    exact le_rfl
  have hindicator : (∑ w : Complement e → K,
      if w ∈ bad then (d : ℝ) * (Fintype.card K : ℝ) else 0) =
      (bad.card : ℝ) * ((d : ℝ) * (Fintype.card K : ℝ)) := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun w : Complement e → K => w ∈ bad) =
        bad := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  rw [surface_zero_count_eq_sum_slice_counts e f]
  rw [Nat.cast_sum]
  calc
    (∑ w : Complement e → K, (c w : ℝ))
        ≤ ∑ w : Complement e → K,
          (q + Real.sqrt (B * q) +
            (if w ∈ bad then (d : ℝ) * q else 0)) := hsum
    _ = q ^ 2 + q * Real.sqrt (B * q) +
          (bad.card : ℝ) * ((d : ℝ) * q) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hparamCard, q]
      rw [hindicator]
      ring
    _ ≤ q ^ 2 + q * Real.sqrt (B * q) +
          (bad.card : ℝ) * (d : ℝ) * q := by
      have hdq : 0 ≤ (d : ℝ) * q := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hbad hdq]


theorem surface_zero_count_le_K_mul_sq_of_finite_exceptional_slices
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (bad : Finset (Complement e → K))
    (Dg : ℕ) (hgdeg : bad.card ≤ Dg)
    (hfdeg : f.totalDegree ≤ d)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, w ∉ bad →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, w ∉ bad →
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
  have hC : 0 ≤ (bad.card : ℝ) * (d : ℝ) := by positivity
  have hcurve : 4 * B ≤ (K₀ - 1) ^ 2 * q := by
    simpa only [B, q] using hcurveLarge
  have hexceptional : 2 * ((bad.card : ℝ) * (d : ℝ)) ≤
      (K₀ - 1) * q := by
    have hdegree : (bad.card : ℝ) ≤ (Dg : ℝ) := by exact_mod_cast hgdeg
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hmul := mul_le_mul_of_nonneg_right hdegree hd0
    linarith
  have hcount := surface_zero_count_le_of_finite_exceptional_slices curveWeil d hd e f bad
    hfdeg hall hgoodDegree hgoodIntegral
  have herror := surface_error_le_K_mul_sq B
    ((bad.card : ℝ) * (d : ℝ)) q K₀ hB hC hq hK₀ hcurve hexceptional
  exact hcount.trans (by simpa only [B, q, mul_assoc] using herror)


theorem surface_zero_count_le_K_mul_sq_of_finite_exceptional_slices_card_ge
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {K : Type} [Field K] [Fintype K]
    (d : ℕ) (hd : 1 ≤ d) (e : Fin 2 ↪ Fin 3)
    (f : MvPolynomial (Fin 3) K) (bad : Finset (Complement e → K))
    (Dg : ℕ) (hgdeg : bad.card ≤ Dg)
    (hfdeg : f.totalDegree ≤ d)
    (hall : ∀ w : Complement e → K, slice e f w ≠ 0)
    (hgoodDegree : ∀ w : Complement e → K, w ∉ bad →
      1 ≤ (slice e f w).totalDegree)
    (hgoodIntegral : ∀ w : Complement e → K, w ∉ bad →
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
  exact surface_zero_count_le_K_mul_sq_of_finite_exceptional_slices curveWeil d hd e f bad Dg
    hgdeg hfdeg hall hgoodDegree hgoodIntegral K₀ hK₀ hcurveLarge
    hexceptionalLarge

/-- The zero affine slice and the reciprocals of all roots of the actual
one-parameter projective-pencil certificate. -/
def inverseExceptionalParameters {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) : Finset K :=
  insert 0 ((zeros Δ).image (fun w => (w 0)⁻¹))

theorem card_inverseExceptionalParameters_le
    {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) (hΔ : Δ ≠ 0) :
    (inverseExceptionalParameters Δ).card ≤ Δ.totalDegree + 1 := by
  have hz : (zeros Δ).card ≤ Δ.totalDegree := by
    simpa using card_zeros_le_totalDegree_mul Δ hΔ
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans hz) 1)

theorem good_of_not_mem_inverseExceptionalParameters
    {K : Type} [Field K] [Fintype K]
    (Δ : MvPolynomial (Fin 1) K) {u : K}
    (hu : u ∉ inverseExceptionalParameters Δ) :
    u ≠ 0 ∧ eval (fun _ : Fin 1 => u⁻¹) Δ ≠ 0 := by
  constructor
  · intro hzero
    apply hu
    simp [inverseExceptionalParameters, hzero]
  · intro hzero
    apply hu
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(fun _ : Fin 1 => u⁻¹), ?_, ?_⟩
    · simpa only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] using hzero
    · simp

end CubicTenVariables.SurfacePointCountByFiniteExceptionalSlices
