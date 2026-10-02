import TranslatedDepthSeven.EffectiveCurveResidualNumerics
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffective

/-!
# Numerical absorption for the effective prefix-surface residual

This file connects the literal residual emitted by the quantitative
surface-count assembly to its eventual `Bpoint^(1+epsilon)` form.  The one
remaining scale comparison is stated transparently as the bound on the
actual natural degree mass `d * L`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Turn a real upper bound for the raw determinant degree into a bound for
the literal natural ceiling and the total surface-section degree mass. -/
theorem quantitativePrefixDegreeMass_le_power
    (d b H Baux Bpoint : ℕ) (eta a theta R : ℝ)
    (htheta : 0 ≤ theta)
    (hscale :
      2 * (H : ℝ) ^ eta * (1 + (Baux : ℝ) ^ a) ≤
        R * ((Bpoint : ℝ) + 1) ^ theta) :
    (((d * (b + quantitativePrefixUniformBlockDegree H Baux eta a) : ℕ) : ℝ)) ≤
      (d : ℝ) * ((b : ℝ) + 1 + R) *
        ((Bpoint : ℝ) + 1) ^ theta := by
  let X : ℝ := (Bpoint : ℝ) + 1
  let raw : ℝ := 2 * (H : ℝ) ^ eta * (1 + (Baux : ℝ) ^ a)
  have hraw : 0 ≤ raw := by
    dsimp only [raw]
    positivity
  have hceil :
      ((quantitativePrefixUniformBlockDegree H Baux eta a : ℕ) : ℝ) <
        raw + 1 := by
    simpa only [quantitativePrefixUniformBlockDegree, raw] using
      Nat.ceil_lt_add_one hraw
  have hceilBound :
      ((quantitativePrefixUniformBlockDegree H Baux eta a : ℕ) : ℝ) ≤
        R * X ^ theta + 1 := by
    have hrawBound : raw ≤ R * X ^ theta := by
      simpa only [raw, X] using hscale
    linarith
  have hX : 1 ≤ X := by
    dsimp only [X]
    norm_num
  have hpow : 1 ≤ X ^ theta := Real.one_le_rpow hX htheta
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hmiddle :
      (b : ℝ) + (R * X ^ theta + 1) ≤
        ((b : ℝ) + 1 + R) * X ^ theta := by
    have hb : 0 ≤ (b : ℝ) := by positivity
    nlinarith [mul_nonneg (add_nonneg hb (by norm_num : (0 : ℝ) ≤ 1))
      (sub_nonneg.mpr hpow)]
  have hsum :
      (b : ℝ) +
          (quantitativePrefixUniformBlockDegree H Baux eta a : ℝ) ≤
        ((b : ℝ) + 1 + R) * X ^ theta := by
    linarith
  norm_num only [Nat.cast_mul, Nat.cast_add]
  have hmul := mul_le_mul_of_nonneg_left hsum hd
  simpa only [X, mul_assoc] using hmul

/-- Absorb the literal varying-degree residual once its actual degree mass
is bounded by `A * (Bpoint + 1)^eta`. -/
theorem quantitativePrefixEffectiveCurveResidual_le_target_of_degreeMass
    (C A : ℝ) (d b H Baux Bpoint : ℕ)
    (etaAux a theta epsilon : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (htheta : 0 < theta)
    (hdegreeMass :
      (((d * (b + quantitativePrefixUniformBlockDegree H Baux etaAux a) : ℕ) : ℝ)) ≤
        A * ((Bpoint : ℝ) + 1) ^ theta)
    (hexponent : (1 / 2 : ℝ) + 6 * theta ≤ 1 + epsilon) :
    quantitativePrefixEffectiveCurveResidual
        C d b H Baux Bpoint etaAux a ≤
      C * A ^ (5 : ℕ) * (theta⁻¹ + A) *
        ((Bpoint : ℝ) + 1) ^ (1 + epsilon) := by
  let E : ℝ :=
    ((d * (b + quantitativePrefixUniformBlockDegree H Baux etaAux a) : ℕ) : ℝ)
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hheight : (1 : ℝ) ≤ (Bpoint : ℝ) + 1 := by
    norm_num
  have hbound : E ≤ A * ((Bpoint : ℝ) + 1) ^ theta := by
    simpa only [E] using hdegreeMass
  have hraw := effectiveSurfaceResidual_le_target
    C A E ((Bpoint : ℝ) + 1) theta epsilon
    hC hA hE hheight htheta hbound hexponent
  simpa only [quantitativePrefixEffectiveCurveResidual, E] using hraw

/-- Direct form: it suffices to bound the raw (pre-ceiling) determinant
degree by one power of the point height.  The ceiling, fixed normalization
degree, and surface degree are all absorbed into the displayed constant. -/
theorem quantitativePrefixEffectiveCurveResidual_le_target_of_rawDegreeScale
    (C R : ℝ) (d b H Baux Bpoint : ℕ)
    (etaAux a theta epsilon : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (htheta : 0 < theta)
    (hscale :
      2 * (H : ℝ) ^ etaAux * (1 + (Baux : ℝ) ^ a) ≤
        R * ((Bpoint : ℝ) + 1) ^ theta)
    (hexponent : (1 / 2 : ℝ) + 6 * theta ≤ 1 + epsilon) :
    quantitativePrefixEffectiveCurveResidual
        C d b H Baux Bpoint etaAux a ≤
      C * ((d : ℝ) * ((b : ℝ) + 1 + R)) ^ (5 : ℕ) *
        (theta⁻¹ + (d : ℝ) * ((b : ℝ) + 1 + R)) *
        ((Bpoint : ℝ) + 1) ^ (1 + epsilon) := by
  let A : ℝ := (d : ℝ) * ((b : ℝ) + 1 + R)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hdegreeMass :
      (((d * (b + quantitativePrefixUniformBlockDegree
        H Baux etaAux a) : ℕ) : ℝ)) ≤
        A * ((Bpoint : ℝ) + 1) ^ theta := by
    simpa only [A] using
      quantitativePrefixDegreeMass_le_power
        d b H Baux Bpoint etaAux a theta R htheta.le hscale
  simpa only [A] using
    quantitativePrefixEffectiveCurveResidual_le_target_of_degreeMass
      C A d b H Baux Bpoint etaAux a theta epsilon
      hC hA htheta hdegreeMass hexponent

end

end TranslatedDepthSeven
