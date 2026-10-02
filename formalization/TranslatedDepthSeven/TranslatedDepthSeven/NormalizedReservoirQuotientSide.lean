import TranslatedDepthSeven.ManuscriptReservoirTarget
import TranslatedDepthSeven.SurfaceReservoirTangentBridge

/-!
# The divided packet side from the reservoir lower bound

The lower bound `q \gg T^(5/7)` directly makes a residue packet have divided
side `O(T^(2/7))`.  No upper bound `q ≤ T` is needed.  This common numerical
lemma applies equally to a reservoir modulus and to the least common
multiple attached to an adjacent pair.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The exact divided-packet side is at most twice the manuscript scale
`T^(2/7)` whenever the modulus satisfies the reservoir lower bound. -/
theorem normalizedReservoirQuotientSide_le_two_rpow
    (p : Parameters) (q : ℕ)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q) :
    1 + (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
      2 * p.T ^ (2 / 7 : ℝ) := by
  have hT : (1 : ℝ) ≤ p.T := p.one_le_T
  have hTnonneg : 0 ≤ p.T := hT.trans' zero_le_one
  have hsideRaw := surfaceTangentNaturalSide_cast_le_three_mul p
  change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hsideRaw
  have hside : (4 * surfaceTangentNaturalSide p : ℝ) ≤ 12 * p.T := by
    linarith
  have hconstant : (12 : ℝ) ≤ normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have hqtarget : normalizedSurfaceReservoirConstant *
      p.T ^ (5 / 7 : ℝ) ≤ (q : ℝ) := by
    calc
      normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) := manuscriptReservoirTarget_cast_lower _ _ _
      _ ≤ (q : ℝ) := by exact_mod_cast hlower
  have hqLower : 12 * p.T ^ (5 / 7 : ℝ) ≤ (q : ℝ) :=
    (mul_le_mul_of_nonneg_right hconstant
      (Real.rpow_nonneg hTnonneg _)).trans hqtarget
  have hqpos : (0 : ℝ) < q := by
    have hpowpos : 0 < p.T ^ (5 / 7 : ℝ) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) _
    nlinarith
  have hdiv : (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
      p.T ^ (2 / 7 : ℝ) := by
    rw [div_le_iff₀ hqpos]
    have hpower :
        p.T ^ (2 / 7 : ℝ) * p.T ^ (5 / 7 : ℝ) = p.T := by
      rw [← Real.rpow_add p.T_pos]
      norm_num
    have hfactor :
        p.T ^ (2 / 7 : ℝ) * (12 * p.T ^ (5 / 7 : ℝ)) =
          12 * p.T := by
      calc
        p.T ^ (2 / 7 : ℝ) * (12 * p.T ^ (5 / 7 : ℝ)) =
            12 * (p.T ^ (2 / 7 : ℝ) * p.T ^ (5 / 7 : ℝ)) := by ring
        _ = 12 * p.T := by rw [hpower]
    calc
      (4 * surfaceTangentNaturalSide p : ℝ) ≤ 12 * p.T := hside
      _ = p.T ^ (2 / 7 : ℝ) *
          (12 * p.T ^ (5 / 7 : ℝ)) := hfactor.symm
      _ ≤ p.T ^ (2 / 7 : ℝ) * q := by
        exact mul_le_mul_of_nonneg_left hqLower
          (Real.rpow_nonneg hTnonneg _)
  have hpowOne : (1 : ℝ) ≤ p.T ^ (2 / 7 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  linarith

end

end TranslatedDepthSeven
