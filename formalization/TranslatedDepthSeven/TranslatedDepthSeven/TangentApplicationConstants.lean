import TranslatedDepthSeven.PrimitivePowerLaws

/-!
# The two numerical tangent-packet inequalities

This file contains the numerical specialization of the tangent-packet size
condition

`k! * M^k < q^(2*k-d)`

in the only two cases used in the manuscript.  The coordinate constant `4`
comes from subtracting two points whose coordinates have absolute value at
most `2*T`.  We choose one intentionally non-optimal reservoir constant that
works in both cases.

The hypotheses compare natural numbers with `NNReal` scales after the
canonical cast.  Thus the conclusions are literal inequalities in `Nat`, and
there is no implicit real-to-integer rounding step.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The fixed coordinate-difference coefficient used in both applications. -/
def tangentCoordinateConstant : ℕ := 4

/-- A single explicit, deliberately oversized reservoir constant for both
tangent-packet applications. -/
def tangentReservoirConstant : ℕ :=
  Nat.factorial 10 * tangentCoordinateConstant ^ 10 + 1

/-- The least integral surface modulus satisfying the chosen real lower
bound. -/
def surfaceTangentQThreshold (T : ℕ) : ℕ :=
  ⌈(((tangentReservoirConstant : NNReal) * qScale (T : NNReal) : NNReal) : ℝ)⌉₊

/-- The least integral quotient modulus satisfying the chosen real lower
bound. -/
def quotientTangentQThreshold (T : ℕ) : ℕ :=
  ⌈(((tangentReservoirConstant : NNReal) *
    quotientQScale (T : NNReal) : NNReal) : ℝ)⌉₊

theorem surface_scale_le_threshold_cast (T : ℕ) :
    (tangentReservoirConstant : NNReal) * qScale (T : NNReal) ≤
      (surfaceTangentQThreshold T : NNReal) := by
  change (((tangentReservoirConstant : NNReal) *
      qScale (T : NNReal) : NNReal) : ℝ) ≤
    (surfaceTangentQThreshold T : ℝ)
  exact Nat.le_ceil _

theorem quotient_scale_le_threshold_cast (T : ℕ) :
    (tangentReservoirConstant : NNReal) * quotientQScale (T : NNReal) ≤
      (quotientTangentQThreshold T : NNReal) := by
  change (((tangentReservoirConstant : NNReal) *
      quotientQScale (T : NNReal) : NNReal) : ℝ) ≤
    (quotientTangentQThreshold T : ℝ)
  exact Nat.le_ceil _

theorem surface_tangent_coefficient_lt_reservoir_pow :
    Nat.factorial 10 * tangentCoordinateConstant ^ 10 <
      tangentReservoirConstant ^ 14 := by
  have hpos : 0 < tangentReservoirConstant := by
    simp [tangentReservoirConstant]
  calc
    Nat.factorial 10 * tangentCoordinateConstant ^ 10 <
        tangentReservoirConstant := by
      simp [tangentReservoirConstant]
    _ ≤ tangentReservoirConstant ^ 14 := by
      have hone : 1 ≤ tangentReservoirConstant := hpos
      simpa using Nat.pow_le_pow_right hone (show 1 ≤ 14 by omega)

theorem quotient_tangent_coefficient_lt_reservoir_pow :
    Nat.factorial 9 * tangentCoordinateConstant ^ 9 <
      tangentReservoirConstant ^ 13 := by
  have hcoeff :
      Nat.factorial 9 * tangentCoordinateConstant ^ 9 <
        Nat.factorial 10 * tangentCoordinateConstant ^ 10 := by
    norm_num [tangentCoordinateConstant, Nat.factorial]
  have hpos : 0 < tangentReservoirConstant := by
    simp [tangentReservoirConstant]
  calc
    Nat.factorial 9 * tangentCoordinateConstant ^ 9 <
        Nat.factorial 10 * tangentCoordinateConstant ^ 10 := hcoeff
    _ < tangentReservoirConstant := by
      simp [tangentReservoirConstant]
    _ ≤ tangentReservoirConstant ^ 13 := by
      have hone : 1 ≤ tangentReservoirConstant := hpos
      simpa using Nat.pow_le_pow_right hone (show 1 ≤ 13 by omega)

/-- The surface application `(N,d,k)=(13,6,10)`.  The exponent on the
right is `2*10-6=14`; the identity `(T^(5/7))^14=T^10` supplies the exact
balance. -/
theorem surface_tangent_size_inequality
    {T : NNReal} {q M : ℕ} (hT : 1 ≤ T)
    (hM : (M : NNReal) ≤ tangentCoordinateConstant * T)
    (hq : (tangentReservoirConstant : NNReal) * qScale T ≤ (q : NNReal)) :
    Nat.factorial 10 * M ^ 10 < q ^ (2 * 10 - 6) := by
  have hMpow : (M : NNReal) ^ 10 ≤
      ((tangentCoordinateConstant : NNReal) * T) ^ 10 := by
    gcongr
  have hTpowpos : 0 < T ^ (10 : ℕ) := pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hcoeff :
      (Nat.factorial 10 * tangentCoordinateConstant ^ 10 : NNReal) <
        tangentReservoirConstant ^ 14 := by
    exact_mod_cast surface_tangent_coefficient_lt_reservoir_pow
  have hstrict :
      (Nat.factorial 10 : NNReal) *
          ((tangentCoordinateConstant : NNReal) * T) ^ 10 <
        ((tangentReservoirConstant : NNReal) * qScale T) ^ 14 := by
    have hscaleNat : (qScale T) ^ (14 : ℕ) = T ^ (10 : ℕ) := by
      calc
        (qScale T) ^ (14 : ℕ) = (qScale T) ^ (14 : ℝ) :=
          (NNReal.rpow_natCast _ _).symm
        _ = T ^ (10 : ℝ) := qScale_rpow_fourteen T
        _ = T ^ (10 : ℕ) := NNReal.rpow_natCast _ _
    rw [mul_pow, mul_pow]
    rw [hscaleNat]
    simpa [mul_assoc] using mul_lt_mul_of_pos_right hcoeff hTpowpos
  have hqpow :
      ((tangentReservoirConstant : NNReal) * qScale T) ^ 14 ≤
        (q : NNReal) ^ 14 := by
    gcongr
  have hcast :
      (Nat.factorial 10 : NNReal) * (M : NNReal) ^ 10 <
        (q : NNReal) ^ 14 := by
    calc
      (Nat.factorial 10 : NNReal) * (M : NNReal) ^ 10 ≤
          (Nat.factorial 10 : NNReal) *
            ((tangentCoordinateConstant : NNReal) * T) ^ 10 := by
        gcongr
      _ < ((tangentReservoirConstant : NNReal) * qScale T) ^ 14 := hstrict
      _ ≤ (q : NNReal) ^ 14 := hqpow
  norm_num at hcast ⊢
  exact_mod_cast hcast

/-- Entirely integral input form of `surface_tangent_size_inequality`.
The ceiling in `surfaceTangentQThreshold` is sufficient; no further
real-to-natural rounding hypothesis is needed. -/
theorem surface_tangent_size_inequality_of_nat_bounds
    {T q M : ℕ} (hT : 1 ≤ T)
    (hM : M ≤ tangentCoordinateConstant * T)
    (hq : surfaceTangentQThreshold T ≤ q) :
    Nat.factorial 10 * M ^ 10 < q ^ (2 * 10 - 6) := by
  apply surface_tangent_size_inequality (T := (T : NNReal))
    (q := q) (M := M)
  · exact_mod_cast hT
  · exact_mod_cast hM
  · exact (surface_scale_le_threshold_cast T).trans (by exact_mod_cast hq)

/-- The isolated-vertex quotient application `(N,d,k)=(12,5,9)`.  The
exponent on the right is `2*9-5=13`; the identity
`(T^(9/13))^13=T^9` supplies the exact balance. -/
theorem quotient_tangent_size_inequality
    {T : NNReal} {q M : ℕ} (hT : 1 ≤ T)
    (hM : (M : NNReal) ≤ tangentCoordinateConstant * T)
    (hq : (tangentReservoirConstant : NNReal) * quotientQScale T ≤
      (q : NNReal)) :
    Nat.factorial 9 * M ^ 9 < q ^ (2 * 9 - 5) := by
  have hMpow : (M : NNReal) ^ 9 ≤
      ((tangentCoordinateConstant : NNReal) * T) ^ 9 := by
    gcongr
  have hTpowpos : 0 < T ^ (9 : ℕ) := pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hcoeff :
      (Nat.factorial 9 * tangentCoordinateConstant ^ 9 : NNReal) <
        tangentReservoirConstant ^ 13 := by
    exact_mod_cast quotient_tangent_coefficient_lt_reservoir_pow
  have hstrict :
      (Nat.factorial 9 : NNReal) *
          ((tangentCoordinateConstant : NNReal) * T) ^ 9 <
        ((tangentReservoirConstant : NNReal) * quotientQScale T) ^ 13 := by
    have hscaleNat : (quotientQScale T) ^ (13 : ℕ) = T ^ (9 : ℕ) := by
      calc
        (quotientQScale T) ^ (13 : ℕ) =
            (quotientQScale T) ^ (13 : ℝ) :=
          (NNReal.rpow_natCast _ _).symm
        _ = T ^ (9 : ℝ) := quotientQScale_rpow_thirteen T
        _ = T ^ (9 : ℕ) := NNReal.rpow_natCast _ _
    rw [mul_pow, mul_pow]
    rw [hscaleNat]
    simpa [mul_assoc] using mul_lt_mul_of_pos_right hcoeff hTpowpos
  have hqpow :
      ((tangentReservoirConstant : NNReal) * quotientQScale T) ^ 13 ≤
        (q : NNReal) ^ 13 := by
    gcongr
  have hcast :
      (Nat.factorial 9 : NNReal) * (M : NNReal) ^ 9 <
        (q : NNReal) ^ 13 := by
    calc
      (Nat.factorial 9 : NNReal) * (M : NNReal) ^ 9 ≤
          (Nat.factorial 9 : NNReal) *
            ((tangentCoordinateConstant : NNReal) * T) ^ 9 := by
        gcongr
      _ < ((tangentReservoirConstant : NNReal) * quotientQScale T) ^ 13 := hstrict
      _ ≤ (q : NNReal) ^ 13 := hqpow
  norm_num at hcast ⊢
  exact_mod_cast hcast

/-- Entirely integral input form of `quotient_tangent_size_inequality`.
The ceiling in `quotientTangentQThreshold` is sufficient; no further
real-to-natural rounding hypothesis is needed. -/
theorem quotient_tangent_size_inequality_of_nat_bounds
    {T q M : ℕ} (hT : 1 ≤ T)
    (hM : M ≤ tangentCoordinateConstant * T)
    (hq : quotientTangentQThreshold T ≤ q) :
    Nat.factorial 9 * M ^ 9 < q ^ (2 * 9 - 5) := by
  apply quotient_tangent_size_inequality (T := (T : NNReal))
    (q := q) (M := M)
  · exact_mod_cast hT
  · exact_mod_cast hM
  · exact (quotient_scale_le_threshold_cast T).trans (by exact_mod_cast hq)

end

end TranslatedDepthSeven
