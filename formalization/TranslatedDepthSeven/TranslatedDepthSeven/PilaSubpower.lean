import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Absorbing Pila's explicit exponential factor

This file proves, using only Mathlib, that the factor

`exp (12 * sqrt (d * log H * log (log H)))`

is bounded by `H ^ ε` once `H` exceeds an explicit threshold depending on
`d` and `ε`.  It also records a uniform bound for every `H ≥ 1`, with an
explicit constant.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The explicit subpower factor occurring in Pila's estimate. -/
def pilaFactor (d H : ℝ) : ℝ :=
  Real.exp (12 * Real.sqrt (d * Real.log H * Real.log (Real.log H)))

/-- A convenient explicit threshold for absorbing `pilaFactor d H` into
`H ^ ε`.  No optimization of this threshold is intended. -/
def pilaThreshold (d ε : ℝ) : ℝ :=
  Real.exp (max 1 ((288 * d / ε ^ 2) ^ 2))

/-- An explicit constant for the version valid on the whole range `H ≥ 1`. -/
def pilaConstant (d ε : ℝ) : ℝ :=
  Real.exp
    (12 * Real.sqrt
      (d * (max 1 ((288 * d / ε ^ 2) ^ 2)) ^ 2))

/-- One explicit constant which is uniform over every nonlinear natural
degree `e ≤ D`. -/
def pilaCurveUniformConstant (D : ℕ) (ε : ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 D, pilaConstant e ε

/-- Above the explicit threshold, Pila's factor is at most `H ^ ε`. -/
theorem pilaFactor_le_rpow
    {d ε H : ℝ} (hd : 0 ≤ d) (hε : 0 < ε)
    (hH : pilaThreshold d ε ≤ H) :
    pilaFactor d H ≤ H ^ ε := by
  let x : ℝ := Real.log H
  let a : ℝ := 288 * d / ε ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hthreshold_pos : 0 < pilaThreshold d ε := by
    simp only [pilaThreshold]
    positivity
  have hHpos : 0 < H := lt_of_lt_of_le hthreshold_pos hH
  have hx_bound : max 1 (a ^ 2) ≤ x := by
    apply (Real.le_log_iff_exp_le hHpos).2
    simpa [pilaThreshold, a] using hH
  have hx_one : 1 ≤ x := (le_max_left _ _).trans hx_bound
  have hx_nonneg : 0 ≤ x := zero_le_one.trans hx_one
  have ha_sq_le : a ^ 2 ≤ x := (le_max_right _ _).trans hx_bound
  have ha_le_sqrt : a ≤ Real.sqrt x := by
    have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
    nlinarith [Real.sqrt_nonneg x]
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx_nonneg (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
  have hcoefficient : 288 * d ≤ ε ^ 2 * Real.sqrt x := by
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have := mul_le_mul_of_nonneg_left ha_le_sqrt hεsq.le
    dsimp [a] at this
    field_simp at this
    nlinarith
  have hradicand_nonneg : 0 ≤ d * x * Real.log x := by
    have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_one
    positivity
  have hradicand_bound :
      144 * (d * x * Real.log x) ≤ (ε * x) ^ 2 := by
    calc
      144 * (d * x * Real.log x)
          ≤ 144 * (d * x * (2 * Real.sqrt x)) := by
              gcongr
      _ = (288 * d) * x * Real.sqrt x := by ring
      _ ≤ (ε ^ 2 * Real.sqrt x) * x * Real.sqrt x := by
              gcongr
      _ = (ε * x) ^ 2 := by
              nlinarith
  have hεx_nonneg : 0 ≤ ε * x := mul_nonneg hε.le hx_nonneg
  have hexponent :
      12 * Real.sqrt (d * x * Real.log x) ≤ ε * x := by
    have hsquare :
        (12 * Real.sqrt (d * x * Real.log x)) ^ 2 ≤ (ε * x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hradicand_nonneg]
      norm_num
      exact hradicand_bound
    nlinarith [Real.sqrt_nonneg (d * x * Real.log x)]
  unfold pilaFactor
  change Real.exp (12 * Real.sqrt (d * x * Real.log x)) ≤ H ^ ε
  rw [Real.rpow_def_of_pos hHpos]
  apply Real.exp_le_exp.mpr
  simpa [x, mul_comm] using hexponent

/-- For every `H ≥ 1`, Pila's factor is bounded by an explicit constant
times `H ^ ε`. -/
theorem pilaFactor_le_const_mul_rpow
    {d ε H : ℝ} (hd : 0 ≤ d) (hε : 0 < ε) (hH : 1 ≤ H) :
    pilaFactor d H ≤ pilaConstant d ε * H ^ ε := by
  by_cases hlarge : pilaThreshold d ε ≤ H
  · have hmain := pilaFactor_le_rpow hd hε hlarge
    have hone : 1 ≤ pilaConstant d ε := by
      unfold pilaConstant
      exact Real.one_le_exp (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    refine hmain.trans ?_
    have := mul_le_mul_of_nonneg_right hone
      (Real.rpow_nonneg (zero_le_one.trans hH) ε)
    simpa using this
  · have hthreshold_pos : 0 < pilaThreshold d ε := by
      simp only [pilaThreshold]
      positivity
    have hHpos : 0 < H := zero_lt_one.trans_le hH
    have hlog_mono : Real.log H ≤ Real.log (pilaThreshold d ε) :=
      Real.strictMonoOn_log.monotoneOn hHpos hthreshold_pos (le_of_not_ge hlarge)
    have hlogH_nonneg : 0 ≤ Real.log H := Real.log_nonneg hH
    let M : ℝ := max 1 ((288 * d / ε ^ 2) ^ 2)
    have hM_one : 1 ≤ M := le_max_left _ _
    have hlogthreshold : Real.log (pilaThreshold d ε) = M := by
      simp [pilaThreshold, M]
    have hlogH_le_M : Real.log H ≤ M := by
      simpa [hlogthreshold] using hlog_mono
    have hloglog_le : Real.log (Real.log H) ≤ Real.log H := by
      by_cases hzero : Real.log H = 0
      · simp [hzero]
      · have hpos : 0 < Real.log H := lt_of_le_of_ne hlogH_nonneg (Ne.symm hzero)
        exact (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
    have hproduct :
        d * Real.log H * Real.log (Real.log H) ≤ d * M ^ 2 := by
      calc
        d * Real.log H * Real.log (Real.log H)
            ≤ d * Real.log H * Real.log H := by gcongr
        _ ≤ d * M ^ 2 := by
          have hsquares : (Real.log H) ^ 2 ≤ M ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_left hsquares hd
          nlinarith
    have hsqrt := Real.sqrt_le_sqrt hproduct
    have hfactor : pilaFactor d H ≤ pilaConstant d ε := by
      unfold pilaFactor pilaConstant
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
    have hrpow_one : 1 ≤ H ^ ε := Real.one_le_rpow hH hε.le
    exact hfactor.trans (le_mul_of_one_le_right (Real.exp_nonneg _) hrpow_one)

/-- For a nonlinear curve of natural degree `e ≥ 2`, Pila's main power
`H^(1/e)` is at most the square-root power on the range `H ≥ 1`. -/
theorem curveDegree_rpow_le_half
    {e : ℕ} {H : ℝ} (he : 2 ≤ e) (hH : 1 ≤ H) :
    H ^ ((e : ℝ)⁻¹) ≤ H ^ (1 / 2 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le hH
  have heReal : (2 : ℝ) ≤ e := by exact_mod_cast he
  rw [inv_eq_one_div]
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) heReal)

/-- The exact analytic bridge used after Pila's curve theorem: its printed
power and printed exponential factor are bounded by one fixed constant times
`H^(1/2+ε)`, uniformly for every nonlinear degree `e`. -/
theorem pilaCurvePower_mul_factor_le_const_mul_rpow
    {e : ℕ} {ε H : ℝ} (he : 2 ≤ e) (hε : 0 < ε) (hH : 1 ≤ H) :
    H ^ ((e : ℝ)⁻¹) * pilaFactor e H ≤
      pilaConstant e ε * H ^ ((1 / 2 : ℝ) + ε) := by
  have hfactor := pilaFactor_le_const_mul_rpow
    (d := (e : ℝ)) (ε := ε) (H := H) (by positivity) hε hH
  have hpow := curveDegree_rpow_le_half he hH
  calc
    H ^ ((e : ℝ)⁻¹) * pilaFactor e H ≤
        H ^ ((e : ℝ)⁻¹) * (pilaConstant e ε * H ^ ε) :=
      mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg (by positivity) _)
    _ ≤ H ^ (1 / 2 : ℝ) * (pilaConstant e ε * H ^ ε) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (Real.exp_nonneg _)
          (Real.rpow_nonneg (zero_le_one.trans hH) _))
    _ = pilaConstant e ε * H ^ ((1 / 2 : ℝ) + ε) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hH)]
      ring

/-- Uniform version of the preceding analytic bridge for all nonlinear curve
degrees bounded by one fixed natural number `D`. -/
theorem pilaCurvePower_mul_factor_le_uniformConstant_mul_rpow
    {D e : ℕ} {ε H : ℝ} (he : 2 ≤ e) (heD : e ≤ D)
    (hε : 0 < ε) (hH : 1 ≤ H) :
    H ^ ((e : ℝ)⁻¹) * pilaFactor e H ≤
      pilaCurveUniformConstant D ε * H ^ ((1 / 2 : ℝ) + ε) := by
  have hpoint := pilaCurvePower_mul_factor_le_const_mul_rpow he hε hH
  have hmem : e ∈ Finset.Icc 2 D := Finset.mem_Icc.mpr ⟨he, heD⟩
  have hconstant : pilaConstant e ε ≤ pilaCurveUniformConstant D ε := by
    unfold pilaCurveUniformConstant
    refine Finset.single_le_sum (s := Finset.Icc 2 D)
      (f := fun i : ℕ ↦ pilaConstant i ε) ?_ hmem
    intro i _hi
    unfold pilaConstant
    positivity
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right hconstant
      (Real.rpow_nonneg (zero_le_one.trans hH) _))

/-- Enlarging a box of radius `c*U` to the strict height `c*U+1` changes a
nonnegative real power only by the explicit constant `(c+1)^alpha`, provided
`U >= 1`. -/
theorem affineHeight_add_one_rpow_le
    {c U α : ℝ} (hc : 0 ≤ c) (hU : 1 ≤ U) (hα : 0 ≤ α) :
    (c * U + 1) ^ α ≤ (c + 1) ^ α * U ^ α := by
  have hbase : c * U + 1 ≤ (c + 1) * U := by
    nlinarith
  calc
    (c * U + 1) ^ α ≤ ((c + 1) * U) ^ α :=
      Real.rpow_le_rpow (by positivity) hbase hα
    _ = (c + 1) ^ α * U ^ α := by
      rw [Real.mul_rpow (by positivity) (zero_le_one.trans hU)]

/-- Complete analytic comparison after an `O(U)` affine rescaling and the
harmless `+1` needed for Pila's strict height convention. -/
theorem pilaCurvePower_mul_factor_affineHeight_le
    {D e : ℕ} {ε c U : ℝ} (he : 2 ≤ e) (heD : e ≤ D)
    (hε : 0 < ε) (hc : 0 ≤ c) (hU : 1 ≤ U) :
    (c * U + 1) ^ ((e : ℝ)⁻¹) * pilaFactor e (c * U + 1) ≤
      pilaCurveUniformConstant D ε * (c + 1) ^ ((1 / 2 : ℝ) + ε) *
        U ^ ((1 / 2 : ℝ) + ε) := by
  have hheight : 1 ≤ c * U + 1 := by
    nlinarith [mul_nonneg hc (zero_le_one.trans hU)]
  have hpoint := pilaCurvePower_mul_factor_le_uniformConstant_mul_rpow
    he heD hε hheight
  have hpower := affineHeight_add_one_rpow_le hc hU (by positivity :
    (0 : ℝ) ≤ (1 / 2 : ℝ) + ε)
  have hconstantNonneg : 0 ≤ pilaCurveUniformConstant D ε := by
    unfold pilaCurveUniformConstant
    exact Finset.sum_nonneg fun i _hi ↦ by
      unfold pilaConstant
      positivity
  calc
    (c * U + 1) ^ ((e : ℝ)⁻¹) * pilaFactor e (c * U + 1) ≤
        pilaCurveUniformConstant D ε *
          (c * U + 1) ^ ((1 / 2 : ℝ) + ε) := hpoint
    _ ≤ pilaCurveUniformConstant D ε *
          ((c + 1) ^ ((1 / 2 : ℝ) + ε) *
            U ^ ((1 / 2 : ℝ) + ε)) := by
      exact mul_le_mul_of_nonneg_left hpower hconstantNonneg
    _ = pilaCurveUniformConstant D ε *
          (c + 1) ^ ((1 / 2 : ℝ) + ε) *
            U ^ ((1 / 2 : ℝ) + ε) := by ring

end

end TranslatedDepthSeven
