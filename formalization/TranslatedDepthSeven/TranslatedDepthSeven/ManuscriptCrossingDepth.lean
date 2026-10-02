import TranslatedDepthSeven.ComparableCertificateScale
import TranslatedDepthSeven.ManuscriptReservoirTarget

/-!
# The crossing cardinality fits inside the logarithmic reservoir

This file proves the real-variable comparison left implicit in the finite
reservoir construction.  Uniformly for `1 ≤ T ≤ H`, the least number of
comparable primes needed to reach `ceil (Cres * T ^ a)` is eventually no
larger than

`ceil (B * log H / log (log H))`,

provided `a + 1 < B`.  The spare unit in the exponent absorbs the fixed
factor coming from `Cres` and from rounding the target to an integer.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- Pointwise comparison at a height which is already large enough to
absorb the fixed target constant. -/
theorem manuscriptReservoirCrossing_le_reservoirDepth
    {C Cres H T a B : ℝ}
    (hC : 1 ≤ C) (hCres : 1 < Cres) (ha : 0 ≤ a)
    (hgap : a + 1 < B)
    (hH : 1 < H) (hloglog : 0 < Real.log (Real.log H))
    (hconstant : 2 * Cres ≤ H)
    (hT : 1 ≤ T) (hTH : T ≤ H)
    (hscale : 1 ≤ C * Real.log H) :
    manuscriptReservoirCrossing C Cres H T a hscale ≤
      reservoirDepth B H := by
  have hHpos : 0 < H := zero_lt_one.trans hH
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hpowTH : T ^ a ≤ H ^ a :=
    Real.rpow_le_rpow hTnonneg hTH ha
  have htarget0 :
      ((manuscriptReservoirTarget Cres T a : ℕ) : ℝ) ≤
        2 * Cres * T ^ a :=
    manuscriptReservoirTarget_cast_le_two_mul hCres.le hT ha
  have htarget :
      ((manuscriptReservoirTarget Cres T a : ℕ) : ℝ) ≤
        H ^ (a + 1) := by
    calc
      ((manuscriptReservoirTarget Cres T a : ℕ) : ℝ)
          ≤ 2 * Cres * T ^ a := htarget0
      _ ≤ 2 * Cres * H ^ a := by
        exact mul_le_mul_of_nonneg_left hpowTH
          (mul_nonneg (by norm_num) (zero_le_one.trans hCres.le))
      _ ≤ H * H ^ a := by
        exact mul_le_mul_of_nonneg_right hconstant
          (Real.rpow_nonneg hHpos.le a)
      _ = H ^ (a + 1) := by
        rw [Real.rpow_add hHpos, Real.rpow_one]
        ring
  have htargetPower :
      manuscriptReservoirTarget Cres T a <
        manuscriptReservoirLower C H ^ reservoirDepth B H := by
    simpa only [manuscriptReservoirLower] using
      certificate_lt_comparableBase_pow_reservoirDepth
        (A := a + 1) (B := B) (C := C) (H := H)
        (by linarith) hgap hC hH hloglog htarget
  unfold manuscriptReservoirCrossing
  apply comparableCrossing_le
  exact htargetPower.le

/-- Uniform eventual form.  The quantified proof of the lower-endpoint
scale is included because it is the proof argument occurring in the
definition of `manuscriptReservoirCrossing`. -/
theorem eventually_manuscriptReservoirCrossing_le_reservoirDepth
    {C Cres a B : ℝ}
    (hC : 1 ≤ C) (hCres : 1 < Cres) (ha : 0 ≤ a)
    (hgap : a + 1 < B) :
    ∀ᶠ H : ℝ in atTop, ∀ T : ℝ,
      1 ≤ T → T ≤ H →
      ∀ hscale : 1 ≤ C * Real.log H,
        manuscriptReservoirCrossing C Cres H T a hscale ≤
          reservoirDepth B H := by
  have hloglogTop :
      Tendsto (fun H : ℝ ↦ Real.log (Real.log H)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hloglogTop.eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (2 * Cres)] with H hH hloglog hconstant
  intro T hT hTH hscale
  exact manuscriptReservoirCrossing_le_reservoirDepth
    hC hCres ha hgap hH hloglog hconstant hT hTH hscale

end

end TranslatedDepthSeven
