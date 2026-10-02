import TranslatedDepthSeven.QuantitativePrefixEffectiveResidualAbsorption
import TranslatedDepthSeven.NormalizedReservoirQuotientSide

/-!
# The honest scale specialization for the effective surface residual

This file records what the degree-effective curve estimate gives from the
literal determinant degree.  If both natural height parameters are bounded
by the point height, the raw root degree has exponent `eta + a`; this is the
strongest direct specialization of the root-uniform bound.

At a full reservoir vertex the situation is better.  The reservoir modulus
dominates `(2 * surfaceTangentNaturalSide p)^a` for `0 <= a <= 5/7`, so the
factor divided by the modulus is at most one.  Thus a terminal block has
only the arbitrarily small coefficient-height exponent `eta`.  The empty
prefix root has modulus one, so this terminal estimate does not apply to it.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The direct common-height bound for the literal root-uniform raw degree.
No modulus saving is present, so the exponents `eta` and `a` add. -/
theorem quantitativePrefixRawDegreeScale_le_four_commonHeight
    (H Baux Bpoint : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1) :
    2 * (H : ℝ) ^ eta * (1 + (Baux : ℝ) ^ a) ≤
      4 * ((Bpoint : ℝ) + 1) ^ (eta + a) := by
  let X : ℝ := (Bpoint : ℝ) + 1
  have hXone : (1 : ℝ) ≤ X := by
    dsimp only [X]
    norm_num
  have hHpow : (H : ℝ) ^ eta ≤ X ^ eta :=
    Real.rpow_le_rpow (by positivity) (by simpa only [X] using hH) heta
  have hBpow : (Baux : ℝ) ^ a ≤ X ^ a :=
    Real.rpow_le_rpow (by positivity) (by simpa only [X] using hBaux) ha
  have hXapow : (1 : ℝ) ≤ X ^ a := Real.one_le_rpow hXone ha
  have hsum : 1 + (Baux : ℝ) ^ a ≤ 2 * X ^ a := by
    linarith
  calc
    2 * (H : ℝ) ^ eta * (1 + (Baux : ℝ) ^ a) ≤
        2 * X ^ eta * (2 * X ^ a) := by gcongr
    _ = 4 * X ^ (eta + a) := by
      rw [Real.rpow_add (by positivity)]
      ring
    _ = 4 * ((Bpoint : ℝ) + 1) ^ (eta + a) := rfl

/-- The resulting complete one-height absorption statement.  Its exponent
condition displays the genuine cost `6 * (eta + a)` of the current
degree-effective aggregation. -/
theorem quantitativePrefixEffectiveCurveResidual_le_target_of_commonHeight
    (C : ℝ) (d b H Baux Bpoint : ℕ)
    (eta a epsilon : ℝ)
    (hC : 0 ≤ C) (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hetaA : 0 < eta + a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hexponent : (1 / 2 : ℝ) + 6 * (eta + a) ≤ 1 + epsilon) :
    quantitativePrefixEffectiveCurveResidual
        C d b H Baux Bpoint eta a ≤
      C * ((d : ℝ) * ((b : ℝ) + 5)) ^ (5 : ℕ) *
        ((eta + a)⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
        ((Bpoint : ℝ) + 1) ^ (1 + epsilon) := by
  have hscale := quantitativePrefixRawDegreeScale_le_four_commonHeight
    H Baux Bpoint eta a heta ha hH hBaux
  simpa only [show (b : ℝ) + 1 + 4 = (b : ℝ) + 5 by ring] using
    quantitativePrefixEffectiveCurveResidual_le_target_of_rawDegreeScale
      C 4 d b H Baux Bpoint eta a (eta + a) epsilon
      hC (by norm_num) hetaA hscale hexponent

/-- For the cubic determinant range, already the weak inequality `a > 1/2`
makes the preceding one-height exponent condition impossible for every
`epsilon <= 1`.  This is a numerical obstruction, not a missing tactic. -/
theorem rootUniformEffectiveExponent_obstruction
    (eta a epsilon : ℝ) (heta : 0 ≤ eta)
    (ha : (1 / 2 : ℝ) < a) (hepsilon : epsilon ≤ 1) :
    ¬ ((1 / 2 : ℝ) + 6 * (eta + a) ≤ 1 + epsilon) := by
  intro h
  nlinarith

/-- At the actual reservoir scale, the modulus dominates the `a`-th power
of the normalized displacement side whenever `a <= 5/7`. -/
theorem two_surfaceTangentNaturalSide_rpow_le_reservoirModulus
    (p : Parameters) (q : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q) :
    (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a ≤ (q : ℝ) := by
  have hT : (1 : ℝ) ≤ p.T := p.one_le_T
  have hside0 : (0 : ℝ) ≤ 2 * (surfaceTangentNaturalSide p : ℝ) := by
    positivity
  have hside : 2 * (surfaceTangentNaturalSide p : ℝ) ≤ 6 * p.T := by
    have hs := surfaceTangentNaturalSide_cast_le_three_mul p
    change (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T at hs
    linarith
  have hpowSide :
      (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a ≤ (6 * p.T) ^ a :=
    Real.rpow_le_rpow hside0 hside ha0
  have hsixPow : (6 : ℝ) ^ a ≤ 6 := by
    have haone : a ≤ 1 := ha.trans (by norm_num)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) haone
  have hTPow : p.T ^ a ≤ p.T ^ (5 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT ha
  have hmulPow : (6 * p.T) ^ a = (6 : ℝ) ^ a * p.T ^ a := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hpower : (6 * p.T) ^ a ≤ 6 * p.T ^ (5 / 7 : ℝ) := by
    rw [hmulPow]
    exact mul_le_mul hsixPow hTPow (Real.rpow_nonneg p.T_pos.le _)
      (by positivity)
  have hconstant : (6 : ℝ) ≤ normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have htarget : normalizedSurfaceReservoirConstant *
      p.T ^ (5 / 7 : ℝ) ≤ (q : ℝ) := by
    calc
      normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) := manuscriptReservoirTarget_cast_lower _ _ _
      _ ≤ (q : ℝ) := by exact_mod_cast hlower
  calc
    (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a ≤ (6 * p.T) ^ a := hpowSide
    _ ≤ 6 * p.T ^ (5 / 7 : ℝ) := hpower
    _ ≤ normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) := by
      gcongr
    _ ≤ (q : ℝ) := htarget

/-- Consequently, the divided degree factor at every full reservoir vertex
is at most two.  This is the scale actually needed for a subpower terminal
degree. -/
theorem one_add_two_surfaceTangentNaturalSide_rpow_div_le_two
    (p : Parameters) (q : ℕ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q) :
    1 + (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a / (q : ℝ) ≤ 2 := by
  have hpow := two_surfaceTangentNaturalSide_rpow_le_reservoirModulus
    p q a ha0 ha hlower
  have hqpos : (0 : ℝ) < q := by
    have htarget : 1 < manuscriptReservoirTarget
        normalizedSurfaceReservoirConstant p.T (5 / 7) :=
      one_lt_manuscriptReservoirTarget
        (by
          norm_num [normalizedSurfaceReservoirConstant,
            tangentReservoirConstant, tangentCoordinateConstant,
            Nat.factorial])
        p.one_le_T (by norm_num)
    have hq : 0 < q := by omega
    exact_mod_cast hq
  have hdiv : (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqpos]
    exact hpow
  linarith

/-- A full-depth reservoir block therefore has raw determinant degree at
most `4 * H^eta`.  The empty prefix root cannot use this lemma because its
modulus is exactly one. -/
theorem terminalDeterminantRawDegree_le_four_heightPower
    (p : Parameters) (H q : ℕ) (eta a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q) :
    2 * (H : ℝ) ^ eta *
        (1 + (2 * (surfaceTangentNaturalSide p : ℝ)) ^ a / (q : ℝ)) ≤
      4 * (H : ℝ) ^ eta := by
  have hfactor := one_add_two_surfaceTangentNaturalSide_rpow_div_le_two
    p q a ha0 ha hlower
  have hnonneg : 0 ≤ 2 * (H : ℝ) ^ eta := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hfactor hnonneg]

/-- Directly consume the block-degree inequality emitted by the quantitative
auxiliary construction at a full reservoir modulus. -/
theorem terminalBlockDegree_cast_le_four_heightPower
    (p : Parameters) (H q k : ℕ) (eta a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q)
    (hk : (k : ℝ) ≤ 2 * (H : ℝ) ^ eta *
      (1 + ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^ a / (q : ℝ))) :
    (k : ℝ) ≤ 4 * (H : ℝ) ^ eta := by
  have hraw := terminalDeterminantRawDegree_le_four_heightPower
    p H q eta a ha0 ha hlower
  have hcast : ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) =
      2 * (surfaceTangentNaturalSide p : ℝ) := by norm_num
  rw [hcast] at hk
  exact hk.trans hraw

/-- Natural-number form of the terminal degree cap.  Unlike the old fixed
cap, this ceiling may grow by the arbitrarily small power `H^eta`. -/
theorem terminalBlockDegree_le_ceil_four_heightPower
    (p : Parameters) (H q k : ℕ) (eta a : ℝ)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hlower : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q)
    (hk : (k : ℝ) ≤ 2 * (H : ℝ) ^ eta *
      (1 + ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) ^ a / (q : ℝ))) :
    k ≤ ⌈4 * (H : ℝ) ^ eta⌉₊ := by
  exact_mod_cast (terminalBlockDegree_cast_le_four_heightPower
    p H q k eta a ha0 ha hlower hk).trans (Nat.le_ceil _)

end

end TranslatedDepthSeven
