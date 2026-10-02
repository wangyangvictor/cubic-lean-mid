import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-cap absorption for the degree-effective curve residual

The persistent-cell surface argument has two genuinely different degree
scales.  The root degree bounds the number of cells, while the terminal
degree enters the degree-effective curve estimate.  This file records the
resulting elementary power bookkeeping, independently of the geometry and
of the persistent-cell assembly.

If
`Eroot <= Rroot * X ^ thetaRoot` and
`Eterminal <= Rterminal * X ^ thetaTerminal`, then the nonlinear residual

`C * Eroot * Eterminal^4 * X^(1/2) * (log X + Eterminal)`

has exponent `1/2 + thetaRoot + 5 * thetaTerminal`.  The corresponding
root/terminal occurrence mass has exponent `thetaRoot + thetaTerminal`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The product of independent root and terminal degree caps has the sum of
their exponents. -/
theorem twoCapOccurrenceMass_le
    (Rroot Rterminal Eroot Eterminal X thetaRoot thetaTerminal : ℝ)
    (hRroot : 0 ≤ Rroot)
    (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X)
    (hroot : Eroot ≤ Rroot * X ^ thetaRoot)
    (hterminal : Eterminal ≤ Rterminal * X ^ thetaTerminal) :
    Eroot * Eterminal ≤
      Rroot * Rterminal * X ^ (thetaRoot + thetaTerminal) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  calc
    Eroot * Eterminal ≤
        (Rroot * X ^ thetaRoot) * (Rterminal * X ^ thetaTerminal) := by
      exact mul_le_mul hroot hterminal hEterminal
        (mul_nonneg hRroot (Real.rpow_nonneg (le_trans (by norm_num) hX) _))
    _ = Rroot * Rterminal * X ^ (thetaRoot + thetaTerminal) := by
      rw [Real.rpow_add hXpos]
      ring

/-- With separate root and terminal caps, the root exponent occurs once and
the terminal exponent occurs five times: four times from the fourth degree
power and once from `log X + Eterminal`. -/
theorem effectiveCurveResidualTwoCap_le
    (C Rroot Rterminal Eroot Eterminal X thetaRoot thetaTerminal : ℝ)
    (hC : 0 ≤ C) (hRroot : 0 ≤ Rroot) (hRterminal : 0 ≤ Rterminal)
    (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X) (hthetaTerminal : 0 < thetaTerminal)
    (hroot : Eroot ≤ Rroot * X ^ thetaRoot)
    (hterminal : Eterminal ≤ Rterminal * X ^ thetaTerminal) :
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      C * Rroot * Rterminal ^ (4 : ℕ) *
        (thetaTerminal⁻¹ + Rterminal) *
          X ^ ((1 / 2 : ℝ) + thetaRoot + 5 * thetaTerminal) := by
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hinv : 0 ≤ thetaTerminal⁻¹ := inv_nonneg.mpr hthetaTerminal.le
  have hlog : Real.log X ≤ thetaTerminal⁻¹ * X ^ thetaTerminal := by
    have h := Real.log_le_rpow_div hX0 hthetaTerminal
    rw [div_eq_inv_mul] at h
    exact h
  have hsum : Real.log X + Eterminal ≤
      (thetaTerminal⁻¹ + Rterminal) * X ^ thetaTerminal := by
    calc
      Real.log X + Eterminal ≤
          thetaTerminal⁻¹ * X ^ thetaTerminal +
            Rterminal * X ^ thetaTerminal := add_le_add hlog hterminal
      _ = (thetaTerminal⁻¹ + Rterminal) * X ^ thetaTerminal := by ring
  have hterminalPow : Eterminal ^ (4 : ℕ) ≤
      (Rterminal * X ^ thetaTerminal) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hEterminal hterminal 4
  have hsum0 : 0 ≤ Real.log X + Eterminal :=
    add_nonneg (Real.log_nonneg hX) hEterminal
  have hsumCoef0 : 0 ≤ thetaTerminal⁻¹ + Rterminal :=
    add_nonneg hinv hRterminal
  calc
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      C * (Rroot * X ^ thetaRoot) *
          (Rterminal * X ^ thetaTerminal) ^ (4 : ℕ) *
          X ^ (1 / 2 : ℝ) *
          ((thetaTerminal⁻¹ + Rterminal) * X ^ thetaTerminal) := by
      gcongr
    _ = C * Rroot * Rterminal ^ (4 : ℕ) *
        (thetaTerminal⁻¹ + Rterminal) *
          X ^ ((1 / 2 : ℝ) + thetaRoot + 5 * thetaTerminal) := by
      rw [mul_pow]
      rw [show (X ^ thetaTerminal) ^ (4 : ℕ) =
          X ^ (thetaTerminal * 4) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
        norm_num]
      have hpowers :
          X ^ thetaRoot * X ^ (thetaTerminal * 4) * X ^ (1 / 2 : ℝ) *
              X ^ thetaTerminal =
            X ^ ((1 / 2 : ℝ) + thetaRoot + 5 * thetaTerminal) := by
        rw [← Real.rpow_add hXpos thetaRoot (thetaTerminal * 4)]
        rw [← Real.rpow_add hXpos
          (thetaRoot + thetaTerminal * 4) (1 / 2 : ℝ)]
        rw [← Real.rpow_add hXpos
          (thetaRoot + thetaTerminal * 4 + (1 / 2 : ℝ)) thetaTerminal]
        congr 1
        ring
      rw [← hpowers]
      ring

/-- The generic two-cap residual may be absorbed into `X^(1+epsilon)` as
soon as its displayed exponent is at most `1+epsilon`. -/
theorem effectiveCurveResidualTwoCap_le_target
    (C Rroot Rterminal Eroot Eterminal X thetaRoot thetaTerminal epsilon : ℝ)
    (hC : 0 ≤ C) (hRroot : 0 ≤ Rroot) (hRterminal : 0 ≤ Rterminal)
    (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X) (hthetaTerminal : 0 < thetaTerminal)
    (hroot : Eroot ≤ Rroot * X ^ thetaRoot)
    (hterminal : Eterminal ≤ Rterminal * X ^ thetaTerminal)
    (hexponent :
      (1 / 2 : ℝ) + thetaRoot + 5 * thetaTerminal ≤ 1 + epsilon) :
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      C * Rroot * Rterminal ^ (4 : ℕ) *
        (thetaTerminal⁻¹ + Rterminal) * X ^ (1 + epsilon) := by
  apply (effectiveCurveResidualTwoCap_le C Rroot Rterminal Eroot Eterminal X
    thetaRoot thetaTerminal hC hRroot hRterminal hEterminal hX
    hthetaTerminal hroot hterminal).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX hexponent)
    (mul_nonneg
      (mul_nonneg (mul_nonneg hC hRroot) (by positivity))
      (add_nonneg (inv_nonneg.mpr hthetaTerminal.le) hRterminal))

/-- At the actual raw scales supplied by the common-height root estimate and
the full-reservoir terminal estimate, the residual exponent is
`1/2 + a + 6*eta`.  The coefficient `1024 = 4 * 4^4` is explicit. -/
theorem effectiveCurveResidualTwoCap_le_commonHeightRawScales
    (C Eroot Eterminal X eta a : ℝ)
    (hC : 0 ≤ C) (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X) (heta : 0 < eta)
    (hroot : Eroot ≤ 4 * X ^ (eta + a))
    (hterminal : Eterminal ≤ 4 * X ^ eta) :
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      1024 * C * (eta⁻¹ + 4) *
        X ^ ((1 / 2 : ℝ) + a + 6 * eta) := by
  have h := effectiveCurveResidualTwoCap_le
    C 4 4 Eroot Eterminal X (eta + a) eta
    hC (by norm_num) (by norm_num) hEterminal hX heta hroot hterminal
  calc
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      C * 4 * 4 ^ (4 : ℕ) * (eta⁻¹ + 4) *
        X ^ ((1 / 2 : ℝ) + (eta + a) + 5 * eta) := h
    _ = 1024 * C * (eta⁻¹ + 4) *
        X ^ ((1 / 2 : ℝ) + a + 6 * eta) := by
      have hcoefficient :
          C * 4 * 4 ^ (4 : ℕ) * (eta⁻¹ + 4) =
            1024 * C * (eta⁻¹ + 4) := by
        ring_nf
      rw [show (1 / 2 : ℝ) + (eta + a) + 5 * eta =
        (1 / 2 : ℝ) + a + 6 * eta by ring]
      rw [hcoefficient]

/-- The root/terminal occurrence mass at the same actual scales has exponent
`a + 2*eta`; its explicit coefficient is `16 = 4 * 4`. -/
theorem twoCapOccurrenceMass_le_commonHeightRawScales
    (Eroot Eterminal X eta a : ℝ)
    (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X)
    (hroot : Eroot ≤ 4 * X ^ (eta + a))
    (hterminal : Eterminal ≤ 4 * X ^ eta) :
    Eroot * Eterminal ≤ 16 * X ^ (a + 2 * eta) := by
  have h := twoCapOccurrenceMass_le
    4 4 Eroot Eterminal X (eta + a) eta
    (by norm_num) hEterminal hX hroot hterminal
  calc
    Eroot * Eterminal ≤ 4 * 4 * X ^ ((eta + a) + eta) := h
    _ = 16 * X ^ (a + 2 * eta) := by
      rw [show (eta + a) + eta = a + 2 * eta by ring]
      norm_num

/-- The common-height two-cap residual reaches `X^(1+epsilon)` under the
sharp numerical condition `1/2 + a + 6*eta <= 1+epsilon`. -/
theorem effectiveCurveResidualTwoCap_le_commonHeightTarget
    (C Eroot Eterminal X eta a epsilon : ℝ)
    (hC : 0 ≤ C) (hEterminal : 0 ≤ Eterminal)
    (hX : 1 ≤ X) (heta : 0 < eta)
    (hroot : Eroot ≤ 4 * X ^ (eta + a))
    (hterminal : Eterminal ≤ 4 * X ^ eta)
    (hexponent : (1 / 2 : ℝ) + a + 6 * eta ≤ 1 + epsilon) :
    C * Eroot * Eterminal ^ (4 : ℕ) * X ^ (1 / 2 : ℝ) *
        (Real.log X + Eterminal) ≤
      1024 * C * (eta⁻¹ + 4) * X ^ (1 + epsilon) := by
  apply (effectiveCurveResidualTwoCap_le_commonHeightRawScales
    C Eroot Eterminal X eta a hC hEterminal hX heta
      hroot hterminal).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX hexponent)
    (mul_nonneg (mul_nonneg (by positivity) hC)
      (add_nonneg (inv_nonneg.mpr heta.le) (by norm_num)))

end

end TranslatedDepthSeven
