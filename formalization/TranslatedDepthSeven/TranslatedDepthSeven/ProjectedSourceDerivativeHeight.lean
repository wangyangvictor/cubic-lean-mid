import TranslatedDepthSeven.SurfaceReservoirTangentBridge
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Absorbing the explicit image-derivative bound

The image equation is obtained by Cramer's rule in degree at most `D`.
Its differentiated evaluation has size at most a fixed constant times
`H^(D*(D+1)^4+D)`. One additional power absorbs that constant after a
fixed threshold. Neither the exponent nor the threshold depends on an
auxiliary modulus, a surface coefficient, or the final counting epsilon.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter

/-- Elementary natural-number majorant for the displayed Cramer bound and
its derivative. -/
theorem projectedSourceDerivative_majorant_le
    (D d R Ccoeff : ℕ) (hd : d ≤ D) (hR : 1 ≤ R)
    (hcoeff : Ccoeff ≤ (d + 1) ^ 4 * ((d + 1) ^ 4).factorial *
      R ^ (d * (d + 1) ^ 4)) :
    (d + 1) ^ 4 * d * Ccoeff * R ^ d ≤
      ((D + 1) ^ 4 * D *
        ((D + 1) ^ 4 * ((D + 1) ^ 4).factorial)) *
        R ^ (D * (D + 1) ^ 4 + D) := by
  have hcoeffD : Ccoeff ≤ (D + 1) ^ 4 * ((D + 1) ^ 4).factorial *
      R ^ (D * (D + 1) ^ 4) := by
    apply hcoeff.trans
    gcongr
    exact hR
  calc
    (d + 1) ^ 4 * d * Ccoeff * R ^ d ≤
        (D + 1) ^ 4 * D *
          ((D + 1) ^ 4 * ((D + 1) ^ 4).factorial *
            R ^ (D * (D + 1) ^ 4)) * R ^ D := by
      gcongr
      exact hR
    _ = _ := by rw [pow_add]; ring

/-- A single eventual exponent for every degree, projection row mass,
source box, and coefficient bound in the stated ranges. -/
theorem eventually_projectedSourceDerivative_bound
    (D Cmenu : ℕ) :
    ∀ᶠ H : ℝ in atTop, ∀ d b M Ccoeff : ℕ,
      d ≤ D → b ≤ Cmenu → (M : ℝ) ≤ 6 * H →
      Ccoeff ≤ (d + 1) ^ 4 * ((d + 1) ^ 4).factorial *
        max 1 (b * max 1 M) ^ (d * (d + 1) ^ 4) →
      (((d + 1) ^ 4 * d * Ccoeff *
        max 1 (b * max 1 M) ^ d : ℕ) : ℝ) ≤
        H ^ ((D * (D + 1) ^ 4 + D + 1 : ℕ) : ℝ) := by
  let E : ℕ := D * (D + 1) ^ 4 + D
  let S : ℕ := (D + 1) ^ 4 * D *
    ((D + 1) ^ 4 * ((D + 1) ^ 4).factorial)
  let L : ℝ := 7 * ((Cmenu : ℝ) + 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((S : ℝ) * L ^ E)] with H hH hthreshold
  intro d b M Ccoeff hd hb hM hcoeff
  let R : ℕ := max 1 (b * max 1 M)
  have hRone : 1 ≤ R := Nat.le_max_left _ _
  have hnat := projectedSourceDerivative_majorant_le
    D d R Ccoeff hd hRone hcoeff
  have hcast :
      (((d + 1) ^ 4 * d * Ccoeff * R ^ d : ℕ) : ℝ) ≤
        (S : ℝ) * (R : ℝ) ^ E := by
    exact_mod_cast hnat
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hmaxM : ((max 1 M : ℕ) : ℝ) ≤ 7 * H := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith)
  have hbcast : (b : ℝ) ≤ Cmenu := by exact_mod_cast hb
  have hLone : 1 ≤ L := by
    dsimp only [L]
    nlinarith [show (0 : ℝ) ≤ (Cmenu : ℝ) by positivity]
  have hR : (R : ℝ) ≤ L * H := by
    dsimp only [R]
    rw [Nat.cast_max, Nat.cast_one, Nat.cast_mul]
    apply max_le
    · exact (by nlinarith : (1 : ℝ) ≤ L * H)
    · calc
        (b : ℝ) * (max 1 M : ℕ) ≤ (Cmenu : ℝ) * (7 * H) :=
          mul_le_mul hbcast hmaxM (by positivity) (by positivity)
        _ ≤ L * H := by dsimp only [L]; nlinarith
  have hfinal :
      (((d + 1) ^ 4 * d * Ccoeff * R ^ d : ℕ) : ℝ) ≤
        H ^ (E + 1) := by
    calc
      _ ≤ (S : ℝ) * (R : ℝ) ^ E := hcast
      _ ≤ (S : ℝ) * (L * H) ^ E := by gcongr
      _ = ((S : ℝ) * L ^ E) * H ^ E := by rw [mul_pow]; ring
      _ ≤ H * H ^ E :=
        mul_le_mul_of_nonneg_right hthreshold (pow_nonneg hH0 _)
      _ = H ^ (E + 1) := by rw [pow_succ]; ring
  simpa only [Real.rpow_natCast] using hfinal

/-- Literal tangent-packet specialization. The same exponent and threshold
work for every translated parameter tuple and every bounded menu entry. -/
theorem eventually_projectedSourceDerivative_tangentPacket_bound
    (D Cmenu : ℕ) :
    ∀ᶠ H : ℝ in atTop, ∀ p : Parameters, p.H = H →
      ∀ d b Ccoeff : ℕ, d ≤ D → b ≤ Cmenu →
      Ccoeff ≤ (d + 1) ^ 4 * ((d + 1) ^ 4).factorial *
        max 1 (b * max 1 (2 * surfaceTangentNaturalSide p)) ^
          (d * (d + 1) ^ 4) →
      (((d + 1) ^ 4 * d * Ccoeff *
        max 1 (b * max 1 (2 * surfaceTangentNaturalSide p)) ^ d : ℕ) : ℝ) ≤
        H ^ ((D * (D + 1) ^ 4 + D + 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_projectedSourceDerivative_bound D Cmenu]
    with H hbound
  intro p hp d b Ccoeff hd hb hcoeff
  apply hbound d b (2 * surfaceTangentNaturalSide p) Ccoeff hd hb
  · have hside : (surfaceTangentNaturalSide p : ℝ) ≤ 3 * p.T :=
      surfaceTangentNaturalSide_cast_le_three_mul p
    have hTH : p.T ≤ H := by simpa only [hp] using p.T_le_H
    push_cast
    linarith
  · exact hcoeff

end

end TranslatedDepthSeven
