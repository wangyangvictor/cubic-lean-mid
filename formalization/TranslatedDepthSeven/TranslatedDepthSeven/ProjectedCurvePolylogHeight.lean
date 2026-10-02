import TranslatedDepthSeven.BoundedAffineProjectionMassInternal
import TranslatedDepthSeven.Salberger2023CurveCountNumerics
import Mathlib.Tactic

/-!
# Polylogarithmic height of the projected plane-curve certificate

The internal bounded projection menu has row mass polynomial in the varying
curve degree.  When the degree is at most a fixed multiple of `1 + log V`,
the literal Cramer small-equation bound and the bound for one derivative are
therefore at most

`V ^ (A * (1 + log V) ^ 5)`

for one constant `A` depending only on the fixed ambient dimension and the
fixed degree multiplier.  This file is purely numerical: it uses the exact
coefficient bound already produced by the internal projection theorem and
adds no geometric or determinant-method premise.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped Topology

/-- The literal radius entering the projected-curve Cramer estimate. -/
def projectedCurveCertificateRadius (N δ M : ℕ) : ℕ :=
  max 1 (boundedAffineProjectionRowMassBound N δ * max 1 M)

/-- The literal coefficient bound furnished by the small-equation theorem. -/
def projectedCurveSmallEquationCoefficientBound (N δ M : ℕ) : ℕ :=
  let s := (δ + 1) ^ 3
  s * s.factorial * projectedCurveCertificateRadius N δ M ^ (δ * s)

/-- The corresponding majorant for all first partial derivatives. -/
def projectedCurveDerivativeCertificateBound (N δ M : ℕ) : ℕ :=
  let s := (δ + 1) ^ 3
  s * δ * projectedCurveSmallEquationCoefficientBound N δ M *
    projectedCurveCertificateRadius N δ M ^ δ

/-- The fixed exponent which absorbs the row mass and the coordinate box. -/
def projectedCurveRadiusExponent (N : ℕ) : ℕ := 3 * (N + 1) + 2

/-- An explicit constant sufficient for the final fifth-power logarithmic
height bound. -/
def projectedCurvePolylogHeightConstant (N : ℕ) (Cd : ℝ) : ℝ :=
  let S := (Cd + 1) ^ 3
  let K : ℝ := projectedCurveRadiusExponent N
  13 + 6 * S + K * (Cd * S + Cd)

private theorem cast_degree_add_one_le_sq
    {δ : ℕ} {V : ℝ} (hV : 2 ≤ V) (hδ : (δ : ℝ) ≤ V) :
    ((δ + 1 : ℕ) : ℝ) ≤ V ^ 2 := by
  push_cast
  have hV0 : 0 ≤ V := by linarith
  have htwoV : 2 * V ≤ V * V :=
    mul_le_mul_of_nonneg_right hV hV0
  linarith

private theorem cast_degree_sq_add_one_le_cube
    {δ : ℕ} {V : ℝ} (hV : 2 ≤ V) (hδ : (δ : ℝ) ≤ V) :
    ((δ * δ + 1 : ℕ) : ℝ) ≤ V ^ 3 := by
  push_cast
  have hV0 : 0 ≤ V := by linarith
  have hδ0 : 0 ≤ (δ : ℝ) := by positivity
  have hsquare : (δ : ℝ) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ hδ0 hδ 2
  have hone : (1 : ℝ) ≤ V ^ 2 := by nlinarith [sq_nonneg V]
  have htwo : 2 * V ^ 2 ≤ V * V ^ 2 :=
    mul_le_mul_of_nonneg_right hV (sq_nonneg V)
  calc
    (δ : ℝ) * δ + 1 = (δ : ℝ) ^ 2 + 1 := by ring
    _ ≤ V ^ 2 + 1 := by linarith
    _ ≤ V ^ 2 + V ^ 2 := by linarith
    _ = 2 * V ^ 2 := by ring
    _ ≤ V * V ^ 2 := htwo
    _ = V ^ 3 := by ring

/-- The explicit projection-menu row mass is bounded by a fixed power of the
height as soon as both the degree and the fixed ambient row length are below
the height. -/
theorem boundedAffineProjectionRowMassBound_cast_le_pow
    (N δ : ℕ) (V : ℝ) (hV : 2 ≤ V)
    (hN : ((N + 1 : ℕ) : ℝ) ≤ V) (hδ : (δ : ℝ) ≤ V) :
    (boundedAffineProjectionRowMassBound N δ : ℝ) ≤
      V ^ (3 * (N + 1) + 1) := by
  have hVone : 1 ≤ V := by linarith
  have hδone := cast_degree_add_one_le_sq hV hδ
  have hδsq := cast_degree_sq_add_one_le_cube hV hδ
  have hδone' : (δ : ℝ) + 1 ≤ V ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hδone
  have hδsq' : (δ : ℝ) * δ + 1 ≤ V ^ 3 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hδsq
  have hfirst : (((δ + 1) ^ N : ℕ) : ℝ) ≤ V ^ (2 * N) := by
    push_cast
    calc
      ((δ : ℝ) + 1) ^ N ≤ (V ^ 2) ^ N :=
        pow_le_pow_left₀ (by positivity) hδone' N
      _ = V ^ (2 * N) := by rw [← pow_mul]
  have hsecond : (((δ * δ + 1) ^ (N + 1) : ℕ) : ℝ) ≤
      V ^ (3 * (N + 1)) := by
    push_cast
    calc
      ((δ : ℝ) * δ + 1) ^ (N + 1) ≤ (V ^ 3) ^ (N + 1) :=
        pow_le_pow_left₀ (by positivity) hδsq' (N + 1)
      _ = V ^ (3 * (N + 1)) := by rw [← pow_mul]
  have hfirst' : (((δ + 1) ^ N : ℕ) : ℝ) ≤
      V ^ (3 * (N + 1)) :=
    hfirst.trans (pow_le_pow_right₀ hVone (by omega))
  have hentry : (boundedAffineProjectionEntryBound N δ : ℝ) ≤
      V ^ (3 * (N + 1)) := by
    rw [boundedAffineProjectionEntryBound, Nat.cast_max]
    exact max_le hfirst' hsecond
  rw [boundedAffineProjectionRowMassBound, Nat.cast_mul]
  calc
    (N + 1 : ℕ) * (boundedAffineProjectionEntryBound N δ : ℝ) ≤
        V * V ^ (3 * (N + 1)) :=
      mul_le_mul hN hentry (by positivity) (by linarith)
    _ = V ^ (3 * (N + 1) + 1) := by rw [pow_succ]; ring

/-- The row mass together with the coordinate box contributes only the
fixed exponent `3(N+1)+2`. -/
theorem projectedCurveCertificateRadius_cast_le_pow
    (N δ M : ℕ) (V : ℝ) (hV : 2 ≤ V)
    (hN : ((N + 1 : ℕ) : ℝ) ≤ V) (hδ : (δ : ℝ) ≤ V)
    (hM : (M : ℝ) ≤ V) :
    (projectedCurveCertificateRadius N δ M : ℝ) ≤
      V ^ projectedCurveRadiusExponent N := by
  have hVone : 1 ≤ V := by linarith
  have hmass := boundedAffineProjectionRowMassBound_cast_le_pow
    N δ V hV hN hδ
  have hmaxM : ((max 1 M : ℕ) : ℝ) ≤ V := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le hVone hM
  rw [projectedCurveCertificateRadius, Nat.cast_max, Nat.cast_one,
    Nat.cast_mul]
  apply max_le
  · exact one_le_pow₀ hVone
  · calc
      (boundedAffineProjectionRowMassBound N δ : ℝ) * (max 1 M : ℕ) ≤
          V ^ (3 * (N + 1) + 1) * V :=
        mul_le_mul hmass hmaxM (by positivity) (by positivity)
      _ = V ^ ((3 * (N + 1) + 1) + 1) := by rw [← pow_succ]
      _ = V ^ projectedCurveRadiusExponent N := by
        congr 1

private theorem degree_block_cast_le_log_cube
    (Cd V : ℝ) (δ : ℕ) (hCd : 0 ≤ Cd)
    (hl : 1 ≤ 1 + Real.log V)
    (hδ : (δ : ℝ) ≤ Cd * (1 + Real.log V)) :
    (((δ + 1) ^ 3 : ℕ) : ℝ) ≤
      (Cd + 1) ^ 3 * (1 + Real.log V) ^ 3 := by
  let l := 1 + Real.log V
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  have hCd1 : 0 ≤ Cd + 1 := by linarith
  have hδone : ((δ + 1 : ℕ) : ℝ) ≤ (Cd + 1) * l := by
    push_cast
    dsimp only [l] at hl0 ⊢
    nlinarith
  have hδone' : (δ : ℝ) + 1 ≤ (Cd + 1) * l := by
    simpa only [Nat.cast_add, Nat.cast_one] using hδone
  push_cast
  calc
    ((δ : ℝ) + 1) ^ 3 ≤ ((Cd + 1) * l) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hδone' 3
    _ = (Cd + 1) ^ 3 * (1 + Real.log V) ^ 3 := by
      dsimp only [l]
      rw [mul_pow]

private theorem common_exponent_cast_le_polylog
    (N : ℕ) (Cd V : ℝ) (δ : ℕ) (hCd : 0 ≤ Cd)
    (hl : 1 ≤ 1 + Real.log V)
    (hδ : (δ : ℝ) ≤ Cd * (1 + Real.log V)) :
    (((13 + 6 * (δ + 1) ^ 3 +
        projectedCurveRadiusExponent N *
          (δ * (δ + 1) ^ 3 + δ) : ℕ) : ℝ)) ≤
      projectedCurvePolylogHeightConstant N Cd *
        (1 + Real.log V) ^ 5 := by
  let l : ℝ := 1 + Real.log V
  let S : ℝ := (Cd + 1) ^ 3
  let K : ℝ := projectedCurveRadiusExponent N
  have hl0 : 0 ≤ l := zero_le_one.trans hl
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hδ0 : 0 ≤ (δ : ℝ) := by positivity
  have hs0 : 0 ≤ (((δ + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hs : (((δ + 1) ^ 3 : ℕ) : ℝ) ≤ S * l ^ 3 := by
    simpa only [S, l] using degree_block_cast_le_log_cube Cd V δ hCd hl hδ
  have hs' : ((δ : ℝ) + 1) ^ 3 ≤ S * l ^ 3 := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hs
  have hδ' : (δ : ℝ) ≤ Cd * l := by simpa only [l] using hδ
  have hδs : (((δ * (δ + 1) ^ 3 : ℕ) : ℝ)) ≤
      Cd * S * l ^ 4 := by
    push_cast
    calc
      (δ : ℝ) * ((δ : ℝ) + 1) ^ 3 ≤
          (Cd * l) * (S * l ^ 3) :=
        mul_le_mul hδ' hs' (by positivity) (mul_nonneg hCd hl0)
      _ = Cd * S * l ^ 4 := by ring
  have hδs' : (δ : ℝ) * ((δ : ℝ) + 1) ^ 3 ≤ Cd * S * l ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hδs
  have hl14 : l ≤ l ^ 4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hl (by omega : 1 ≤ 4)
  have hδ4 : (δ : ℝ) ≤ Cd * l ^ 4 := by
    exact hδ'.trans (mul_le_mul_of_nonneg_left hl14 hCd)
  have hinside : (((δ * (δ + 1) ^ 3 + δ : ℕ) : ℝ)) ≤
      (Cd * S + Cd) * l ^ 4 := by
    push_cast
    calc
      (δ : ℝ) * ((δ : ℝ) + 1) ^ 3 + δ ≤
          Cd * S * l ^ 4 + Cd * l ^ 4 := add_le_add hδs' hδ4
      _ = (Cd * S + Cd) * l ^ 4 := by ring
  have hinside' : (δ : ℝ) * ((δ : ℝ) + 1) ^ 3 + δ ≤
      (Cd * S + Cd) * l ^ 4 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hinside
  have hl35 : l ^ 3 ≤ l ^ 5 := pow_le_pow_right₀ hl (by omega)
  have hl45 : l ^ 4 ≤ l ^ 5 := pow_le_pow_right₀ hl (by omega)
  have h13 : (13 : ℝ) ≤ 13 * l ^ 5 := by
    have : (1 : ℝ) ≤ l ^ 5 := one_le_pow₀ hl
    linarith
  have hs5 : (6 : ℝ) * (((δ + 1) ^ 3 : ℕ) : ℝ) ≤
      6 * S * l ^ 5 := by
    calc
      (6 : ℝ) * (((δ + 1) ^ 3 : ℕ) : ℝ) ≤ 6 * (S * l ^ 3) := by gcongr
      _ ≤ 6 * (S * l ^ 5) := by gcongr
      _ = 6 * S * l ^ 5 := by ring
  have hs5' : (6 : ℝ) * ((δ : ℝ) + 1) ^ 3 ≤ 6 * S * l ^ 5 := by
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hs5
  have hKinside : K * (((δ * (δ + 1) ^ 3 + δ : ℕ) : ℝ)) ≤
      K * ((Cd * S + Cd) * l ^ 5) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    exact hinside.trans (mul_le_mul_of_nonneg_left hl45 (by positivity))
  have hKinside' : K * ((δ : ℝ) * ((δ : ℝ) + 1) ^ 3 + δ) ≤
      K * ((Cd * S + Cd) * l ^ 5) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    exact hinside'.trans (mul_le_mul_of_nonneg_left hl45 (by positivity))
  push_cast
  dsimp only [projectedCurvePolylogHeightConstant, K, S, l] at *
  calc
    13 + 6 * ((δ : ℝ) + 1) ^ 3 +
        (projectedCurveRadiusExponent N : ℝ) *
          ((δ : ℝ) * ((δ : ℝ) + 1) ^ 3 + δ) ≤
      13 * (1 + Real.log V) ^ 5 +
        6 * (Cd + 1) ^ 3 * (1 + Real.log V) ^ 5 +
        (projectedCurveRadiusExponent N : ℝ) *
          ((Cd * (Cd + 1) ^ 3 + Cd) * (1 + Real.log V) ^ 5) :=
      add_le_add (add_le_add h13 hs5') hKinside'
    _ = (13 + 6 * (Cd + 1) ^ 3 +
        (projectedCurveRadiusExponent N : ℝ) *
          (Cd * (Cd + 1) ^ 3 + Cd)) *
            (1 + Real.log V) ^ 5 := by ring

private theorem smallEquationCoefficient_cast_le_common_power
    (N δ M : ℕ) (V : ℝ) (hV : 2 ≤ V)
    (hN : ((N + 1 : ℕ) : ℝ) ≤ V) (hδ : (δ : ℝ) ≤ V)
    (hM : (M : ℝ) ≤ V) :
    (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
      V ^ (13 + 6 * (δ + 1) ^ 3 +
        projectedCurveRadiusExponent N * (δ * (δ + 1) ^ 3 + δ)) := by
  let s : ℕ := (δ + 1) ^ 3
  let K : ℕ := projectedCurveRadiusExponent N
  let R : ℕ := projectedCurveCertificateRadius N δ M
  have hVone : 1 ≤ V := by linarith
  have hs : (s : ℝ) ≤ V ^ 6 := by
    dsimp only [s]
    have hδone := cast_degree_add_one_le_sq hV hδ
    have hδone' : (δ : ℝ) + 1 ≤ V ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hδone
    push_cast
    calc
      ((δ : ℝ) + 1) ^ 3 ≤ (V ^ 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hδone' 3
      _ = V ^ 6 := by norm_num [← pow_mul]
  have hfac0 : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by
    exact_mod_cast Nat.factorial_le_pow s
  have hfac : (s.factorial : ℝ) ≤ V ^ (6 * s) := by
    calc
      (s.factorial : ℝ) ≤ (s : ℝ) ^ s := hfac0
      _ ≤ (V ^ 6) ^ s := pow_le_pow_left₀ (by positivity) hs s
      _ = V ^ (6 * s) := by rw [← pow_mul]
  have hR : (R : ℝ) ≤ V ^ K := by
    simpa only [R, K] using
      projectedCurveCertificateRadius_cast_le_pow N δ M V hV hN hδ hM
  have hRpow : (R : ℝ) ^ (δ * s) ≤ V ^ (K * (δ * s)) := by
    calc
      (R : ℝ) ^ (δ * s) ≤ (V ^ K) ^ (δ * s) :=
        pow_le_pow_left₀ (by positivity) hR (δ * s)
      _ = V ^ (K * (δ * s)) := by rw [← pow_mul]
  have hraw : (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
      V ^ (6 + 6 * s + K * (δ * s)) := by
    change (((s * s.factorial * R ^ (δ * s) : ℕ) : ℝ)) ≤ _
    push_cast
    calc
      (s : ℝ) * (s.factorial : ℝ) * (R : ℝ) ^ (δ * s) ≤
        V ^ 6 * V ^ (6 * s) * V ^ (K * (δ * s)) := by
          gcongr
      _ = V ^ (6 + 6 * s + K * (δ * s)) := by
        rw [← pow_add, ← pow_add]
  refine hraw.trans (pow_le_pow_right₀ hVone ?_)
  change (6 + 6 * s + K * (δ * s)) ≤
    (13 + 6 * s + K * (δ * s + δ))
  have hmul : K * (δ * s) ≤ K * (δ * s + δ) := by
    apply Nat.mul_le_mul_left
    omega
  omega

private theorem derivativeCertificate_cast_le_common_power
    (N δ M : ℕ) (V : ℝ) (hV : 2 ≤ V)
    (hN : ((N + 1 : ℕ) : ℝ) ≤ V) (hδ : (δ : ℝ) ≤ V)
    (hM : (M : ℝ) ≤ V) :
    (projectedCurveDerivativeCertificateBound N δ M : ℝ) ≤
      V ^ (13 + 6 * (δ + 1) ^ 3 +
        projectedCurveRadiusExponent N * (δ * (δ + 1) ^ 3 + δ)) := by
  let s : ℕ := (δ + 1) ^ 3
  let K : ℕ := projectedCurveRadiusExponent N
  let R : ℕ := projectedCurveCertificateRadius N δ M
  have hVone : 1 ≤ V := by linarith
  have hs : (s : ℝ) ≤ V ^ 6 := by
    dsimp only [s]
    have hδone := cast_degree_add_one_le_sq hV hδ
    have hδone' : (δ : ℝ) + 1 ≤ V ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hδone
    push_cast
    calc
      ((δ : ℝ) + 1) ^ 3 ≤ (V ^ 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hδone' 3
      _ = V ^ 6 := by norm_num [← pow_mul]
  have hcoeff' : (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
      V ^ (6 + 6 * s + K * (δ * s)) := by
    -- This is the sharper exponent proved inside the preceding argument; the
    -- same proof is short enough to recover by cancelling the harmless slack.
    let E : ℕ := 6 + 6 * s + K * (δ * s)
    have hfac0 : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by
      exact_mod_cast Nat.factorial_le_pow s
    have hfac : (s.factorial : ℝ) ≤ V ^ (6 * s) := by
      calc
        (s.factorial : ℝ) ≤ (s : ℝ) ^ s := hfac0
        _ ≤ (V ^ 6) ^ s := pow_le_pow_left₀ (by positivity) hs s
        _ = V ^ (6 * s) := by rw [← pow_mul]
    have hR : (R : ℝ) ≤ V ^ K := by
      simpa only [R, K] using
        projectedCurveCertificateRadius_cast_le_pow N δ M V hV hN hδ hM
    have hRpow : (R : ℝ) ^ (δ * s) ≤ V ^ (K * (δ * s)) := by
      calc
        (R : ℝ) ^ (δ * s) ≤ (V ^ K) ^ (δ * s) :=
          pow_le_pow_left₀ (by positivity) hR (δ * s)
        _ = V ^ (K * (δ * s)) := by rw [← pow_mul]
    change (((s * s.factorial * R ^ (δ * s) : ℕ) : ℝ)) ≤ _
    push_cast
    calc
      (s : ℝ) * (s.factorial : ℝ) * (R : ℝ) ^ (δ * s) ≤
        V ^ 6 * V ^ (6 * s) * V ^ (K * (δ * s)) := by gcongr
      _ = V ^ E := by dsimp only [E]; rw [← pow_add, ← pow_add]
  have hR : (R : ℝ) ≤ V ^ K := by
    simpa only [R, K] using
      projectedCurveCertificateRadius_cast_le_pow N δ M V hV hN hδ hM
  have hRδ : (R : ℝ) ^ δ ≤ V ^ (K * δ) := by
    calc
      (R : ℝ) ^ δ ≤ (V ^ K) ^ δ := pow_le_pow_left₀ (by positivity) hR δ
      _ = V ^ (K * δ) := by rw [← pow_mul]
  change (((s * δ * projectedCurveSmallEquationCoefficientBound N δ M *
    R ^ δ : ℕ) : ℝ)) ≤ _
  push_cast
  calc
    (s : ℝ) * δ *
        (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) *
          (R : ℝ) ^ δ ≤
      V ^ 6 * V * V ^ (6 + 6 * s + K * (δ * s)) * V ^ (K * δ) := by
        gcongr
    _ = V ^ (13 + 6 * s + K * (δ * s + δ)) := by
      have h61 : V ^ 6 * V = V ^ (6 + 1) := by
        rw [pow_add, pow_one]
      have hsum₁ :
          V ^ (6 + 1) * V ^ (6 + 6 * s + K * (δ * s)) =
            V ^ ((6 + 1) + (6 + 6 * s + K * (δ * s))) :=
        (pow_add V (6 + 1) (6 + 6 * s + K * (δ * s))).symm
      have hsum₂ :
          V ^ ((6 + 1) + (6 + 6 * s + K * (δ * s))) * V ^ (K * δ) =
            V ^ (((6 + 1) + (6 + 6 * s + K * (δ * s))) + K * δ) :=
        (pow_add V ((6 + 1) + (6 + 6 * s + K * (δ * s))) (K * δ)).symm
      calc
        V ^ 6 * V * V ^ (6 + 6 * s + K * (δ * s)) * V ^ (K * δ) =
            V ^ (6 + 1) * V ^ (6 + 6 * s + K * (δ * s)) *
              V ^ (K * δ) := by rw [h61]
        _ = V ^ ((6 + 1) + (6 + 6 * s + K * (δ * s))) *
              V ^ (K * δ) := by rw [hsum₁]
        _ = V ^ (((6 + 1) + (6 + 6 * s + K * (δ * s))) + K * δ) := by
          rw [hsum₂]
        _ = V ^ (13 + 6 * s + K * (δ * s + δ)) := by
          congr 1
          simp only [Nat.mul_add]
          omega

/-- Explicit uniform coefficient and derivative-certificate heights for every
degree bounded by `Cd * (1 + log V)`.  The threshold is independent of the
varying degree, coordinate box and projected equation. -/
theorem eventually_projectedCurve_polylogHeight
    (N : ℕ) (Cd : ℝ) (hCd : 0 ≤ Cd) :
    0 ≤ projectedCurvePolylogHeightConstant N Cd ∧
      ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
        (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        (M : ℝ) ≤ V →
        (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
            V ^ (projectedCurvePolylogHeightConstant N Cd *
              (1 + Real.log V) ^ 5) ∧
          (projectedCurveDerivativeCertificateBound N δ M : ℝ) ≤
            V ^ (projectedCurvePolylogHeightConstant N Cd *
              (1 + Real.log V) ^ 5) := by
  have hA : 0 ≤ projectedCurvePolylogHeightConstant N Cd := by
    dsimp only [projectedCurvePolylogHeightConstant]
    positivity
  refine ⟨hA, ?_⟩
  have habsorb := eventually_polylog_mul_rpow_le_rpow Cd 0 1 1 hCd (by norm_num)
  filter_upwards [habsorb, eventually_ge_atTop (max 2 ((N + 1 : ℕ) : ℝ)),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with V habsorb hV hlog
  intro δ M hδ hM
  have hVtwo : 2 ≤ V := le_max_left _ _ |>.trans hV
  have hVN : ((N + 1 : ℕ) : ℝ) ≤ V := le_max_right _ _ |>.trans hV
  have hVone : 1 ≤ V := by linarith
  have hl : 1 ≤ 1 + Real.log V := by linarith
  have hCdlog : Cd * (1 + Real.log V) ≤ V := by
    simpa only [pow_one, Real.rpow_zero, mul_one, Real.rpow_one] using habsorb
  have hδV : (δ : ℝ) ≤ V := hδ.trans hCdlog
  have hexp := common_exponent_cast_le_polylog N Cd V δ hCd hl hδ
  constructor
  · calc
      (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
          V ^ (13 + 6 * (δ + 1) ^ 3 +
            projectedCurveRadiusExponent N * (δ * (δ + 1) ^ 3 + δ)) :=
        smallEquationCoefficient_cast_le_common_power N δ M V
          hVtwo hVN hδV hM
      _ = V ^ (((13 + 6 * (δ + 1) ^ 3 +
          projectedCurveRadiusExponent N *
            (δ * (δ + 1) ^ 3 + δ) : ℕ) : ℝ)) :=
        (Real.rpow_natCast V _).symm
      _ ≤ V ^ (projectedCurvePolylogHeightConstant N Cd *
          (1 + Real.log V) ^ 5) :=
        Real.rpow_le_rpow_of_exponent_le hVone hexp
  · calc
      (projectedCurveDerivativeCertificateBound N δ M : ℝ) ≤
          V ^ (13 + 6 * (δ + 1) ^ 3 +
            projectedCurveRadiusExponent N * (δ * (δ + 1) ^ 3 + δ)) :=
        derivativeCertificate_cast_le_common_power N δ M V
          hVtwo hVN hδV hM
      _ = V ^ (((13 + 6 * (δ + 1) ^ 3 +
          projectedCurveRadiusExponent N *
            (δ * (δ + 1) ^ 3 + δ) : ℕ) : ℝ)) :=
        (Real.rpow_natCast V _).symm
      _ ≤ V ^ (projectedCurvePolylogHeightConstant N Cd *
          (1 + Real.log V) ^ 5) :=
        Real.rpow_le_rpow_of_exponent_le hVone hexp

/-- Existential form used by downstream geometric adapters. -/
theorem exists_eventually_projectedCurve_polylogHeight
    (N : ℕ) (Cd : ℝ) (hCd : 0 ≤ Cd) :
    ∃ A0 : ℝ, 0 ≤ A0 ∧
      ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
        (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        (M : ℝ) ≤ V →
        (projectedCurveSmallEquationCoefficientBound N δ M : ℝ) ≤
            V ^ (A0 * (1 + Real.log V) ^ 5) ∧
          (projectedCurveDerivativeCertificateBound N δ M : ℝ) ≤
            V ^ (A0 * (1 + Real.log V) ^ 5) := by
  exact ⟨projectedCurvePolylogHeightConstant N Cd,
    (eventually_projectedCurve_polylogHeight N Cd hCd).1,
    (eventually_projectedCurve_polylogHeight N Cd hCd).2⟩

end

end TranslatedDepthSeven
