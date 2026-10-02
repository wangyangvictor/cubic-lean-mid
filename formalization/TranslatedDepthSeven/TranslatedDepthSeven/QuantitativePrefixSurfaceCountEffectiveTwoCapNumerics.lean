import TranslatedDepthSeven.EffectiveCurveResidualTwoCapNumerics
import TranslatedDepthSeven.QuantitativePrefixEffectiveResidualScaleSpecialization
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCap

/-!
# Actual common-height scales for the two-cap surface residual

The empty-prefix cut and the full-reservoir cuts have different degree
scales.  This file converts their literal natural-number ceilings into the
two real power bounds required by the abstract two-cap bookkeeping.

For `X = Bpoint + 1`, with `H, Baux <= X`, the root degree mass is at most

`d (b + 5) X^(eta+a)`,

whereas the terminal degree mass is at most

`d (b + 5) X^eta`.

Consequently the nonlinear residual has exponent `1/2 + a + 6 eta`, and
the rational-line occurrence mass has exponent `a + 2 eta`.  All ceiling
losses are present in the explicit coefficient `d (b + 5)`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The literal root cutting degree, including its natural-number ceiling,
has the common-height scale `eta + a`. -/
theorem quantitativePrefixRootDegreeMass_le_commonHeight
    (d b H Baux Bpoint : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1) :
    ((d * (b + quantitativePrefixUniformBlockDegree H Baux eta a) : ℕ) : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 5) *
        ((Bpoint : ℝ) + 1) ^ (eta + a) := by
  have hscale := quantitativePrefixRawDegreeScale_le_four_commonHeight
    H Baux Bpoint eta a heta ha hH hBaux
  simpa only [show (b : ℝ) + 1 + 4 = (b : ℝ) + 5 by ring] using
    quantitativePrefixDegreeMass_le_power
      d b H Baux Bpoint eta a (eta + a) 4
        (add_nonneg heta ha) hscale

/-- The full-reservoir terminal cutting degree, including its
natural-number ceiling, has the smaller common-height scale `eta`. -/
theorem quantitativePrefixTerminalDegreeMass_le_commonHeight
    (d b H Bpoint : ℕ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1) :
    ((d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 5) *
        ((Bpoint : ℝ) + 1) ^ eta := by
  let X : ℝ := (Bpoint : ℝ) + 1
  have hX : 1 ≤ X := by
    dsimp only [X]
    norm_num
  have hH0 : 0 ≤ (H : ℝ) := by positivity
  have hHpow : (H : ℝ) ^ eta ≤ X ^ eta :=
    Real.rpow_le_rpow hH0 (by simpa only [X] using hH) heta
  have hceil : ((⌈4 * (H : ℝ) ^ eta⌉₊ : ℕ) : ℝ) <
      4 * (H : ℝ) ^ eta + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hceilBound : ((⌈4 * (H : ℝ) ^ eta⌉₊ : ℕ) : ℝ) ≤
      4 * X ^ eta + 1 := by
    nlinarith
  have hpow : 1 ≤ X ^ eta := Real.one_le_rpow hX heta
  have hb : 0 ≤ (b : ℝ) := by positivity
  have hsum :
      (b : ℝ) + ((⌈4 * (H : ℝ) ^ eta⌉₊ : ℕ) : ℝ) ≤
        ((b : ℝ) + 5) * X ^ eta := by
    calc
      (b : ℝ) + ((⌈4 * (H : ℝ) ^ eta⌉₊ : ℕ) : ℝ) ≤
          (b : ℝ) + (4 * X ^ eta + 1) := by linarith
      _ ≤ ((b : ℝ) + 5) * X ^ eta := by
        nlinarith [mul_nonneg (add_nonneg hb (by norm_num : (0 : ℝ) ≤ 1))
          (sub_nonneg.mpr hpow)]
  have hmul := mul_le_mul_of_nonneg_left hsum
    (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  simpa only [Nat.cast_mul, Nat.cast_add, X, mul_assoc] using hmul

/-- The assembled nonlinear residual at the literal root and terminal caps
has exponent `1/2 + a + 6*eta`. -/
theorem quantitativePrefixEffectiveCurveResidualTwoCap_le_commonHeight
    (C : ℝ) (d b H Baux Bpoint : ℕ) (eta a : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1) :
    quantitativePrefixEffectiveCurveResidualTwoCap C d
        (b + quantitativePrefixUniformBlockDegree H Baux eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) Bpoint ≤
      C * ((d : ℝ) * ((b : ℝ) + 5)) ^ (5 : ℕ) *
        (eta⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
          ((Bpoint : ℝ) + 1) ^ ((1 / 2 : ℝ) + a + 6 * eta) := by
  let A : ℝ := (d : ℝ) * ((b : ℝ) + 5)
  let Eroot : ℝ :=
    ((d * (b + quantitativePrefixUniformBlockDegree H Baux eta a) : ℕ) : ℝ)
  let Eterminal : ℝ := ((d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) : ℝ)
  have hX : (1 : ℝ) ≤ (Bpoint : ℝ) + 1 := by norm_num
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hEterminal : 0 ≤ Eterminal := by
    dsimp only [Eterminal]
    positivity
  have hroot : Eroot ≤ A * ((Bpoint : ℝ) + 1) ^ (eta + a) := by
    simpa only [Eroot, A, mul_assoc] using
      quantitativePrefixRootDegreeMass_le_commonHeight
        d b H Baux Bpoint eta a heta.le ha hH hBaux
  have hterminal : Eterminal ≤ A * ((Bpoint : ℝ) + 1) ^ eta := by
    simpa only [Eterminal, A, mul_assoc] using
      quantitativePrefixTerminalDegreeMass_le_commonHeight
        d b H Bpoint eta heta.le hH
  have h := effectiveCurveResidualTwoCap_le
    C A A Eroot Eterminal ((Bpoint : ℝ) + 1) (eta + a) eta
      hC hA hA hEterminal hX heta hroot hterminal
  have hcoefficient :
      C * A * A ^ (4 : ℕ) * (eta⁻¹ + A) =
        C * A ^ (5 : ℕ) * (eta⁻¹ + A) := by
    ring
  rw [hcoefficient] at h
  simpa only [quantitativePrefixEffectiveCurveResidualTwoCap,
    Eroot, Eterminal, A,
    show (1 / 2 : ℝ) + (eta + a) + 5 * eta =
      (1 / 2 : ℝ) + a + 6 * eta by ring] using h

/-- Under the final exponent inequality, the literal two-cap residual is
absorbed into `X^(1+epsilon)` with the same explicit coefficient. -/
theorem quantitativePrefixEffectiveCurveResidualTwoCap_le_target
    (C : ℝ) (d b H Baux Bpoint : ℕ) (eta a epsilon : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hexponent : (1 / 2 : ℝ) + a + 6 * eta ≤ 1 + epsilon) :
    quantitativePrefixEffectiveCurveResidualTwoCap C d
        (b + quantitativePrefixUniformBlockDegree H Baux eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) Bpoint ≤
      C * ((d : ℝ) * ((b : ℝ) + 5)) ^ (5 : ℕ) *
        (eta⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
          ((Bpoint : ℝ) + 1) ^ (1 + epsilon) := by
  apply (quantitativePrefixEffectiveCurveResidualTwoCap_le_commonHeight
    C d b H Baux Bpoint eta a hC heta ha hH hBaux).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent)
    (mul_nonneg
      (mul_nonneg hC (by positivity))
      (add_nonneg (inv_nonneg.mpr heta.le) (by positivity)))

/-- The literal rational-line occurrence mass has exponent
`a + 2*eta` after the two different degree caps are inserted. -/
theorem quantitativePrefixEffectiveLineOccurrenceMassTwoCap_le_commonHeight
    (d b H Baux Bpoint : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1) :
    (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
      (b + quantitativePrefixUniformBlockDegree H Baux eta a)
      (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℝ) ≤
      ((d : ℝ) * ((b : ℝ) + 5)) ^ (2 : ℕ) *
        ((Bpoint : ℝ) + 1) ^ (a + 2 * eta) := by
  let A : ℝ := (d : ℝ) * ((b : ℝ) + 5)
  let Eroot : ℝ :=
    ((d * (b + quantitativePrefixUniformBlockDegree H Baux eta a) : ℕ) : ℝ)
  let Eterminal : ℝ := ((d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) : ℝ)
  have hX : (1 : ℝ) ≤ (Bpoint : ℝ) + 1 := by norm_num
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hEterminal : 0 ≤ Eterminal := by
    dsimp only [Eterminal]
    positivity
  have hroot : Eroot ≤ A * ((Bpoint : ℝ) + 1) ^ (eta + a) := by
    simpa only [Eroot, A, mul_assoc] using
      quantitativePrefixRootDegreeMass_le_commonHeight
        d b H Baux Bpoint eta a heta ha hH hBaux
  have hterminal : Eterminal ≤ A * ((Bpoint : ℝ) + 1) ^ eta := by
    simpa only [Eterminal, A, mul_assoc] using
      quantitativePrefixTerminalDegreeMass_le_commonHeight
        d b H Bpoint eta heta hH
  have h := twoCapOccurrenceMass_le
    A A Eroot Eterminal ((Bpoint : ℝ) + 1) (eta + a) eta
      hA hEterminal hX hroot hterminal
  simpa only [quantitativePrefixEffectiveLineOccurrenceMassTwoCap,
    Eroot, Eterminal, A, Nat.cast_mul,
    show (eta + a) + eta = a + 2 * eta by ring,
    show A * A = A ^ (2 : ℕ) by ring] using h

end

end TranslatedDepthSeven
