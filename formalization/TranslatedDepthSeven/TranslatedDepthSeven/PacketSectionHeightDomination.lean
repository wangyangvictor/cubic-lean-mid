import TranslatedDepthSeven.AffinePacketProjectiveSection
import TranslatedDepthSeven.SurfaceReservoirTangentBridge

/-!
# A fixed power bound for packet-section heights

This file absorbs the completely explicit Cramer height occurring for a
codimension-four section into one fixed power of the manuscript height.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A fixed exponent which absorbs the explicit codimension-four Cramer
height. -/
def packetSectionHeightExponent : ℕ := 160

theorem codimensionFour_packetSectionHeight_le_ceil_heightPower
    (p : Parameters) {r : ℕ} (hr : r ≤ 9) :
    Nat.factorial 4 *
        ((13 * (2 * surfaceTangentNaturalSide p) + 1) *
          (r.factorial * (4 * surfaceTangentNaturalSide p) ^ r)) ^ 4 ≤
      ⌈p.H ^ packetSectionHeightExponent⌉₊ := by
  let Tn := surfaceTangentNaturalSide p
  have hTn1 : 1 ≤ Tn := one_le_surfaceTangentNaturalSide p
  have hfac : r.factorial ≤ (9 : ℕ).factorial :=
    Nat.factorial_le hr
  have hpow : (4 * Tn) ^ r ≤ (4 * Tn) ^ 9 := by
    exact Nat.pow_le_pow_right (by omega) hr
  have hnat :
      Nat.factorial 4 * ((13 * (2 * Tn) + 1) *
        (r.factorial * (4 * Tn) ^ r)) ^ 4 ≤
      Nat.factorial 4 * ((13 * (2 * Tn) + 1) *
        ((9 : ℕ).factorial * (4 * Tn) ^ 9)) ^ 4 := by
    gcongr
  have hTn : (Tn : ℝ) ≤ 3 * p.H := by
    have h := surfaceTangentNaturalSide_cast_le_three_mul p
    change (Tn : ℝ) ≤ 3 * p.T at h
    nlinarith [p.T_le_H]
  have hH : (5 : ℝ) ≤ p.H := p.five_le_H
  have hfirst : (13 * (2 * Tn) + 1 : ℕ) ≤ (p.H ^ 4 : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hlinear : 26 * (Tn : ℝ) + 1 ≤ 79 * p.H := by
      nlinarith
    have h79 : (79 : ℝ) * p.H ≤ p.H ^ 4 := by
      calc
        (79 : ℝ) * p.H ≤ 5 ^ 3 * p.H := by
          gcongr
          norm_num
        _ ≤ p.H ^ 3 * p.H := by gcongr
        _ = p.H ^ 4 := by ring
    convert hlinear.trans h79 using 1
    all_goals ring
  have hfacReal : ((9 : ℕ).factorial : ℝ) ≤ p.H ^ 8 := by
    calc
      ((9 : ℕ).factorial : ℝ) ≤ 5 ^ 8 := by norm_num
      _ ≤ p.H ^ 8 := by gcongr
  have hfourT : (4 * Tn : ℕ) ≤ (12 * p.H : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hpowReal : ((4 * Tn) ^ 9 : ℕ) ≤ (p.H ^ 27 : ℝ) := by
    norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    have hbasepow : (4 * (Tn : ℝ)) ^ 9 ≤ (12 * p.H) ^ 9 := by
      convert pow_le_pow_left₀ (by positivity) hfourT 9 using 1
      all_goals norm_num
    have hc : (12 : ℝ) ^ 9 ≤ 5 ^ 18 := by norm_num
    have hp : (5 : ℝ) ^ 18 ≤ p.H ^ 18 := by gcongr
    calc
      (4 * (Tn : ℝ)) ^ 9 ≤ (12 * p.H) ^ 9 := hbasepow
      _ = 12 ^ 9 * p.H ^ 9 := by ring
      _ ≤ p.H ^ 18 * p.H ^ 9 := by gcongr; exact hc.trans hp
      _ = p.H ^ 27 := by ring
  have hmiddle : ((9 : ℕ).factorial * (4 * Tn) ^ 9 : ℕ) ≤
      (p.H ^ 35 : ℝ) := by
    norm_num only [Nat.cast_mul]
    calc
      ((9 : ℕ).factorial : ℝ) * ((4 * Tn) ^ 9 : ℕ) ≤
          p.H ^ 8 * p.H ^ 27 := by gcongr
      _ = p.H ^ 35 := by ring
  have hreal :
      (Nat.factorial 4 * ((13 * (2 * Tn) + 1) *
        ((9 : ℕ).factorial * (4 * Tn) ^ 9)) ^ 4 : ℕ) ≤
        (p.H ^ packetSectionHeightExponent : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_factorial,
      packetSectionHeightExponent, Nat.factorial]
    have hinner :
        ((13 * (2 * Tn) + 1 : ℕ) : ℝ) *
            (((9 : ℕ).factorial * (4 * Tn) ^ 9 : ℕ) : ℝ) ≤ p.H ^ 39 := by
      calc
        ((13 * (2 * Tn) + 1 : ℕ) : ℝ) *
            (((9 : ℕ).factorial * (4 * Tn) ^ 9 : ℕ) : ℝ) ≤
              p.H ^ 4 * p.H ^ 35 := by gcongr
        _ = p.H ^ 39 := by ring
    have hinner' :
        (↑(13 * (2 * Tn) + 1) : ℝ) *
            (362880 * (4 * (Tn : ℝ)) ^ 9) ≤ p.H ^ 39 := by
      norm_num [Nat.cast_mul, Nat.cast_pow] at hinner ⊢
      exact hinner
    have hfour : (24 : ℝ) ≤ p.H ^ 4 := by
      calc
        (24 : ℝ) ≤ 5 ^ 4 := by norm_num
        _ ≤ p.H ^ 4 := by gcongr
    calc
      _ ≤ (24 : ℝ) * (p.H ^ 39) ^ 4 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hinner' 4) (by norm_num)
      _ ≤ p.H ^ 4 * (p.H ^ 39) ^ 4 := by
        exact mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = p.H ^ 160 := by ring
  apply hnat.trans
  exact_mod_cast hreal.trans (Nat.le_ceil (p.H ^ packetSectionHeightExponent))

end

end TranslatedDepthSeven
