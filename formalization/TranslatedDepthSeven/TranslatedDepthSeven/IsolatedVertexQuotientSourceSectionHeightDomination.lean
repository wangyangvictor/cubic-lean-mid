import TranslatedDepthSeven.IsolatedVertexQuotientPointComponent
import TranslatedDepthSeven.IsolatedVertexQuotientCertificateHeight

/-!
# Fixed-power domination of quotient source-section heights

The quotient packet plane and both source sections already have literal
integral matrices and explicit Plucker-height bounds.  This file absorbs
those bounds into one fixed power of the manuscript height.  The exponent
depends only on the fixed unimodular coordinate change, never on the box,
modulus, residue packet, or point.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 4000000

private theorem mul_le_height_pow_add
    {H x y : ℝ} {a b : ℕ}
    (hH : 0 ≤ H) (hy : 0 ≤ y)
    (hx : x ≤ H ^ a) (hy' : y ≤ H ^ b) :
    x * y ≤ H ^ (a + b) := by
  calc
    x * y ≤ H ^ a * H ^ b := by gcongr
    _ = H ^ (a + b) := by rw [pow_add]

private theorem mul_le_height_pows
    {H x y : ℝ} {a b : ℕ}
    (hH : 0 ≤ H) (hy0 : 0 ≤ y)
    (hx : x ≤ H ^ a) (hy : y ≤ H ^ b) :
    x * y ≤ H ^ a * H ^ b :=
  mul_le_mul hx hy hy0 (pow_nonneg hH _)

private theorem pow_le_height_pow_mul
    {H x : ℝ} {a k : ℕ}
    (hx0 : 0 ≤ x) (hx : x ≤ H ^ a) :
    x ^ k ≤ H ^ (k * a) := by
  calc
    x ^ k ≤ (H ^ a) ^ k := pow_le_pow_left₀ hx0 hx k
    _ = H ^ (a * k) := (pow_mul H a k).symm
    _ = H ^ (k * a) := by rw [Nat.mul_comm]

/-- A fixed exponent absorbing the transformed quotient radius. -/
def isolatedVertexQuotientRadiusHeightExponent
    (U : IntegralUnimodularChange 13) : ℕ :=
  6 * integralMatrixL1Norm U.forward + 1

/-- A fixed exponent absorbing every entry of a quotient packet plane. -/
def isolatedVertexQuotientPacketPlaneEntryHeightExponent
    (U : IntegralUnimodularChange 13) : ℕ :=
  let eR := isolatedVertexQuotientRadiusHeightExponent U
  (eR + 13) + (Nat.factorial 8 + 8 * (eR + 2))

/-- Fixed exponent for the codimension-four original source section. -/
def isolatedVertexQuotientSourceFourSectionHeightExponent
    (U : IntegralUnimodularChange 13) : ℕ :=
  let eA := isolatedVertexQuotientPacketPlaneEntryHeightExponent U
  24 + 4 * (13 + eA + integralMatrixL1Norm U.forward)

/-- Fixed exponent for the codimension-three original source section. -/
def isolatedVertexQuotientSourceThreeSectionHeightExponent
    (U : IntegralUnimodularChange 13) : ℕ :=
  let u := integralMatrixL1Norm U.forward
  let eA := isolatedVertexQuotientPacketPlaneEntryHeightExponent U
  6 + 3 * (13 + (2 + (((u + 15) + eA) + eA)) + u)

/-- One cutoff exponent valid in both vertex cases. -/
def isolatedVertexQuotientSourceSectionHeightExponent
    (U : IntegralUnimodularChange 13) : ℕ :=
  max (isolatedVertexQuotientSourceFourSectionHeightExponent U)
    (isolatedVertexQuotientSourceThreeSectionHeightExponent U)

/-- The transformed quotient radius is bounded by the displayed fixed
power of the manuscript height. -/
theorem isolatedVertexTransformedNaturalSide_cast_le_heightPower
    (U : IntegralUnimodularChange 13) (p : Parameters) :
    (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
      p.H ^ isolatedVertexQuotientRadiusHeightExponent U := by
  let u := integralMatrixL1Norm U.forward
  have hside := isolatedVertexTransformedNaturalSide_cast_le U p
  have hu : ((6 * u : ℕ) : ℝ) ≤ p.H ^ (6 * u) :=
    natCast_le_strictHeight_pow_self p (6 * u)
  calc
    (isolatedVertexTransformedNaturalSide U p : ℝ) ≤
        (6 * u : ℕ) * p.T := hside
    _ ≤ (6 * u : ℕ) * p.H := by
      exact mul_le_mul_of_nonneg_left p.T_le_H (Nat.cast_nonneg _)
    _ ≤ p.H ^ (6 * u) * p.H := by
      exact mul_le_mul_of_nonneg_right hu p.H_pos.le
    _ = p.H ^ isolatedVertexQuotientRadiusHeightExponent U := by
      simp [isolatedVertexQuotientRadiusHeightExponent, u, pow_succ]

/-- The literal Cramer entry bound of every integral quotient packet plane
is absorbed by one fixed power. -/
theorem integralQuotientPacketPlane_entryBound_cast_le_heightPower
    (U : IntegralUnimodularChange 13) (p : Parameters)
    {Z : Finset (IntVector 12)} {q : ℕ}
    {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q
      (isolatedVertexTransformedNaturalSide U p) rho) :
    (((12 * isolatedVertexTransformedNaturalSide U p + 1) *
      (plane.spanRank.factorial *
        (2 * isolatedVertexTransformedNaturalSide U p) ^
          plane.spanRank) : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientPacketPlaneEntryHeightExponent U := by
  let R := isolatedVertexTransformedNaturalSide U p
  let eR := isolatedVertexQuotientRadiusHeightExponent U
  have hH : (1 : ℝ) ≤ p.H := by linarith [p.five_le_H]
  have hR : (R : ℝ) ≤ p.H ^ eR := by
    exact isolatedVertexTransformedNaturalSide_cast_le_heightPower U p
  have hpowR : (1 : ℝ) ≤ p.H ^ eR := one_le_pow₀ hH
  have hfirst : ((12 * R + 1 : ℕ) : ℝ) ≤ p.H ^ (eR + 13) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    have h13 : (13 : ℝ) ≤ p.H ^ 13 :=
      natCast_le_strictHeight_pow_self p 13
    calc
      12 * (R : ℝ) + 1 ≤ 12 * p.H ^ eR + 1 := by gcongr
      _ ≤ 13 * p.H ^ eR := by nlinarith
      _ ≤ p.H ^ 13 * p.H ^ eR := by gcongr
      _ = p.H ^ (eR + 13) := by rw [add_comm, pow_add]
  have hfacNat : plane.spanRank.factorial ≤ Nat.factorial 8 :=
    Nat.factorial_le plane.spanRank_le_eight
  have hfac : (plane.spanRank.factorial : ℝ) ≤
      p.H ^ Nat.factorial 8 := by
    calc
      (plane.spanRank.factorial : ℝ) ≤ Nat.factorial 8 := by
        exact_mod_cast hfacNat
      _ ≤ p.H ^ Nat.factorial 8 :=
        natCast_le_strictHeight_pow_self p (Nat.factorial 8)
  have htwo : (2 : ℝ) ≤ p.H ^ 2 := by nlinarith [p.five_le_H]
  have hbase : ((max 1 (2 * R) : ℕ) : ℝ) ≤ p.H ^ (eR + 2) := by
    norm_num only [Nat.cast_max, Nat.cast_one]
    apply max_le
    · exact one_le_pow₀ hH
    · norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        2 * (R : ℝ) ≤ p.H ^ 2 * p.H ^ eR := by gcongr
        _ = p.H ^ (eR + 2) := by rw [add_comm, pow_add]
  have hpowNat : (2 * R) ^ plane.spanRank ≤
      (max 1 (2 * R)) ^ 8 := by
    calc
      (2 * R) ^ plane.spanRank ≤
          (max 1 (2 * R)) ^ plane.spanRank := by gcongr; omega
      _ ≤ (max 1 (2 * R)) ^ 8 := by
        exact Nat.pow_le_pow_right (by omega) plane.spanRank_le_eight
  have hpow : (((2 * R) ^ plane.spanRank : ℕ) : ℝ) ≤
      p.H ^ (8 * (eR + 2)) := by
    calc
      (((2 * R) ^ plane.spanRank : ℕ) : ℝ) ≤
          (((max 1 (2 * R)) ^ 8 : ℕ) : ℝ) := by
            exact_mod_cast hpowNat
      _ ≤ (p.H ^ (eR + 2)) ^ 8 := by
        norm_num only [Nat.cast_pow]
        gcongr
      _ = p.H ^ (8 * (eR + 2)) := by rw [mul_comm, pow_mul]
  have hfacpow : (plane.spanRank.factorial : ℝ) *
      (((2 * R) ^ plane.spanRank : ℕ) : ℝ) ≤
      p.H ^ (Nat.factorial 8 + 8 * (eR + 2)) :=
    mul_le_height_pow_add p.H_pos.le (by positivity) hfac hpow
  have hcombined :
      (((12 * R + 1) *
        (plane.spanRank.factorial * (2 * R) ^ plane.spanRank) : ℕ) : ℝ) ≤
        p.H ^ (eR + 13) *
          p.H ^ (Nat.factorial 8 + 8 * (eR + 2)) := by
    have hsecond :
        ((plane.spanRank.factorial *
          (2 * R) ^ plane.spanRank : ℕ) : ℝ) ≤
          p.H ^ (Nat.factorial 8 + 8 * (eR + 2)) := by
      simpa only [Nat.cast_mul] using hfacpow
    have hmul := mul_le_height_pows
      (H := p.H)
      (x := ((12 * R + 1 : ℕ) : ℝ))
      (y := ((plane.spanRank.factorial *
        (2 * R) ^ plane.spanRank : ℕ) : ℝ))
      (a := eR + 13)
      (b := Nat.factorial 8 + 8 * (eR + 2))
      p.H_pos.le (by positivity) hfirst hsecond
    simpa only [Nat.cast_mul] using hmul
  calc
    (((12 * R + 1) *
      (plane.spanRank.factorial * (2 * R) ^ plane.spanRank) : ℕ) : ℝ) ≤
        p.H ^ (eR + 13) *
          p.H ^ (Nat.factorial 8 + 8 * (eR + 2)) := hcombined
    _ = p.H ^ isolatedVertexQuotientPacketPlaneEntryHeightExponent U := by
      change p.H ^ (eR + 13) *
          p.H ^ (Nat.factorial 8 + 8 * (eR + 2)) =
        p.H ^ ((eR + 13) + (Nat.factorial 8 + 8 * (eR + 2)))
      exact (pow_add _ _ _).symm

/-- The codimension-four source-section height is dominated by its fixed
power. -/
theorem integralQuotientPacketPlane_sourceFourHeight_le_ceil_heightPower
    (U : IntegralUnimodularChange 13) (p : Parameters)
    {Z : Finset (IntVector 12)} {q : ℕ}
    {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q
      (isolatedVertexTransformedNaturalSide U p) rho) :
    integralQuotientOriginalSourceFourSectionHeightBound U
        ((12 * isolatedVertexTransformedNaturalSide U p + 1) *
          (plane.spanRank.factorial *
            (2 * isolatedVertexTransformedNaturalSide U p) ^
              plane.spanRank)) ≤
      ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
  let u := integralMatrixL1Norm U.forward
  let eA := isolatedVertexQuotientPacketPlaneEntryHeightExponent U
  let HA := (12 * isolatedVertexTransformedNaturalSide U p + 1) *
    (plane.spanRank.factorial *
      (2 * isolatedVertexTransformedNaturalSide U p) ^ plane.spanRank)
  have hA : (HA : ℝ) ≤ p.H ^ eA :=
    integralQuotientPacketPlane_entryBound_cast_le_heightPower U p plane
  have h13 : (13 : ℝ) ≤ p.H ^ 13 :=
    natCast_le_strictHeight_pow_self p 13
  have hu : (u : ℝ) ≤ p.H ^ u :=
    natCast_le_strictHeight_pow_self p u
  have h24 : (24 : ℝ) ≤ p.H ^ 24 :=
    natCast_le_strictHeight_pow_self p 24
  have hinner_nonneg : 0 ≤ (13 : ℝ) * HA * u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg HA))
      (Nat.cast_nonneg u)
  have hinner : (13 : ℝ) * HA * u ≤ p.H ^ (13 + eA + u) := by
    have h13A : (13 : ℝ) * HA ≤ p.H ^ (13 + eA) :=
      mul_le_height_pow_add p.H_pos.le (Nat.cast_nonneg _) h13 hA
    exact mul_le_height_pow_add p.H_pos.le (Nat.cast_nonneg _) h13A hu
  have hreal :
      (integralQuotientOriginalSourceFourSectionHeightBound U HA : ℝ) ≤
        p.H ^ isolatedVertexQuotientSourceFourSectionHeightExponent U := by
    norm_num only [integralQuotientOriginalSourceFourSectionHeightBound,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_factorial, Nat.factorial]
    have hinnerPow : (13 * (HA : ℝ) * u) ^ 4 ≤
        p.H ^ (4 * (13 + eA + u)) :=
      pow_le_height_pow_mul
        (H := p.H) (x := (13 : ℝ) * HA * u)
        (a := 13 + eA + u) (k := 4) hinner_nonneg hinner
    calc
      24 * (13 * (HA : ℝ) * u) ^ 4 ≤
          p.H ^ 24 * p.H ^ (4 * (13 + eA + u)) :=
        mul_le_height_pows p.H_pos.le (pow_nonneg hinner_nonneg 4)
          h24 hinnerPow
      _ = p.H ^ isolatedVertexQuotientSourceFourSectionHeightExponent U := by
        change p.H ^ 24 * p.H ^ (4 * (13 + eA + u)) =
          p.H ^ (24 + 4 * (13 + eA + u))
        exact (pow_add _ _ _).symm
  have hexp : isolatedVertexQuotientSourceFourSectionHeightExponent U ≤
      isolatedVertexQuotientSourceSectionHeightExponent U :=
    le_max_left _ _
  have hmono : p.H ^ isolatedVertexQuotientSourceFourSectionHeightExponent U ≤
      p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U :=
    pow_le_pow_right₀ (by linarith [p.five_le_H]) hexp
  exact_mod_cast hreal.trans (hmono.trans
    (Nat.le_ceil (p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U)))

/-- The codimension-three source-section height is dominated by the same
fixed cutoff power. -/
theorem integralQuotientPacketPlane_sourceThreeHeight_le_ceil_heightPower
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    {Z : Finset (IntVector 12)} {q : ℕ}
    {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q
      (isolatedVertexTransformedNaturalSide U p) rho) :
    integralQuotientOriginalSourceThreeSectionHeightBound U
        ((12 * isolatedVertexTransformedNaturalSide U p + 1) *
          (plane.spanRank.factorial *
            (2 * isolatedVertexTransformedNaturalSide U p) ^
              plane.spanRank))
        (integralMatrixL1Norm U.forward *
          depthSevenProjectionBaseHeight x₀) p.m ≤
      ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
  let u := integralMatrixL1Norm U.forward
  let eA := isolatedVertexQuotientPacketPlaneEntryHeightExponent U
  let HA := (12 * isolatedVertexTransformedNaturalSide U p + 1) *
    (plane.spanRank.factorial *
      (2 * isolatedVertexTransformedNaturalSide U p) ^ plane.spanRank)
  let X := u * depthSevenProjectionBaseHeight x₀
  have hH : (1 : ℝ) ≤ p.H := by linarith [p.five_le_H]
  have hA : (HA : ℝ) ≤ p.H ^ eA :=
    integralQuotientPacketPlane_entryBound_cast_le_heightPower U p plane
  have hX : (X : ℝ) ≤ p.H ^ (u + 1) :=
    quotientTranslationBaseHeight_cast_le U p sourceEquations CF hx₀
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hm' : (p.m : ℝ) ≤ p.H ^ (u + 1) := by
    have hp : p.H ^ 1 ≤ p.H ^ (u + 1) :=
      pow_le_pow_right₀ hH (by omega)
    calc
      (p.m : ℝ) ≤ p.H := hm
      _ = p.H ^ 1 := by rw [pow_one]
      _ ≤ p.H ^ (u + 1) := hp
  have h12 : (12 : ℝ) ≤ p.H ^ 12 :=
    natCast_le_strictHeight_pow_self p 12
  have h2 : (2 : ℝ) ≤ p.H ^ 2 := by nlinarith [p.five_le_H]
  have hMX : ((p.m + 12 * X : ℕ) : ℝ) ≤ p.H ^ (u + 15) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      (p.m : ℝ) + 12 * X ≤
          p.H ^ (u + 1) + p.H ^ 12 * p.H ^ (u + 1) := by gcongr
      _ ≤ p.H ^ (12 + (u + 1)) + p.H ^ (12 + (u + 1)) := by
        have hmono : p.H ^ (u + 1) ≤ p.H ^ (12 + (u + 1)) :=
          pow_le_pow_right₀ hH (by omega)
        have heq : p.H ^ 12 * p.H ^ (u + 1) =
            p.H ^ (12 + (u + 1)) := (pow_add _ _ _).symm
        exact add_le_add hmono heq.le
      _ = 2 * p.H ^ (u + 13) := by ring
      _ ≤ p.H ^ 2 * p.H ^ (u + 13) := by gcongr
      _ = p.H ^ (u + 15) := by
        rw [← pow_add]
        congr 1
        omega
  have hMX' : (p.m : ℝ) + 12 * (X : ℝ) ≤ p.H ^ (u + 15) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hMX
  have h13 : (13 : ℝ) ≤ p.H ^ 13 :=
    natCast_le_strictHeight_pow_self p 13
  have hu : (u : ℝ) ≤ p.H ^ u :=
    natCast_le_strictHeight_pow_self p u
  have h6 : (6 : ℝ) ≤ p.H ^ 6 :=
    natCast_le_strictHeight_pow_self p 6
  have hMXbase_nonneg : 0 ≤ (p.m : ℝ) + 12 * X :=
    add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg X))
  have hMXA_nonneg : 0 ≤ (((p.m : ℝ) + 12 * X) * HA) :=
    mul_nonneg hMXbase_nonneg (Nat.cast_nonneg HA)
  have hMXA : (((p.m : ℝ) + 12 * X) * HA) ≤
      p.H ^ ((u + 15) + eA) :=
    mul_le_height_pow_add p.H_pos.le (Nat.cast_nonneg _) hMX' hA
  have hMXAA : ((((p.m : ℝ) + 12 * X) * HA) * HA) ≤
      p.H ^ (((u + 15) + eA) + eA) :=
    mul_le_height_pow_add p.H_pos.le (Nat.cast_nonneg _) hMXA hA
  have hMXAA_nonneg : 0 ≤
      ((((p.m : ℝ) + 12 * X) * HA) * HA) :=
    mul_nonneg hMXA_nonneg (Nat.cast_nonneg HA)
  have htwoMXAA : (2 : ℝ) * ((((p.m : ℝ) + 12 * X) * HA) * HA) ≤
      p.H ^ (2 + (((u + 15) + eA) + eA)) :=
    mul_le_height_pow_add p.H_pos.le hMXAA_nonneg h2 hMXAA
  have htwoMXAA_nonneg : 0 ≤
      (2 : ℝ) * ((((p.m : ℝ) + 12 * X) * HA) * HA) :=
    mul_nonneg (by norm_num) hMXAA_nonneg
  have h13twoMXAA : (13 : ℝ) *
      (2 * ((((p.m : ℝ) + 12 * X) * HA) * HA)) ≤
      p.H ^ (13 + (2 + (((u + 15) + eA) + eA))) :=
    mul_le_height_pow_add p.H_pos.le htwoMXAA_nonneg h13 htwoMXAA
  have h13twoMXAA_nonneg : 0 ≤ (13 : ℝ) *
      (2 * ((((p.m : ℝ) + 12 * X) * HA) * HA)) :=
    mul_nonneg (by norm_num) htwoMXAA_nonneg
  have hinner : (13 : ℝ) *
      (2 * ((((p.m : ℝ) + 12 * X) * HA) * HA)) * u ≤
      p.H ^ (13 + (2 + (((u + 15) + eA) + eA)) + u) :=
    mul_le_height_pow_add p.H_pos.le (Nat.cast_nonneg _) h13twoMXAA hu
  have hinner_nonneg : 0 ≤ (13 : ℝ) *
      (2 * ((((p.m : ℝ) + 12 * X) * HA) * HA)) * u :=
    mul_nonneg h13twoMXAA_nonneg (Nat.cast_nonneg u)
  have hsourceCore : (13 : ℝ) *
      (2 * (((p.m : ℝ) + 12 * X) * HA) * HA) * u ≤
      p.H ^ (13 + (2 + (((u + 15) + eA) + eA)) + u) := by
    convert hinner using 1 <;> ring
  have hsourceCore_nonneg : 0 ≤ (13 : ℝ) *
      (2 * (((p.m : ℝ) + 12 * X) * HA) * HA) * u := by
    convert hinner_nonneg using 1 <;> ring
  have hreal :
      (integralQuotientOriginalSourceThreeSectionHeightBound U HA X p.m : ℝ) ≤
        p.H ^ isolatedVertexQuotientSourceThreeSectionHeightExponent U := by
    norm_num only [integralQuotientOriginalSourceThreeSectionHeightBound,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_factorial, Nat.cast_add,
      Nat.cast_ofNat, Nat.factorial]
    have hinnerPow :
        (13 * (2 * (((p.m : ℝ) + 12 * X) * HA) * HA) * u) ^ 3 ≤
          p.H ^ (3 * (13 + (2 + (((u + 15) + eA) + eA)) + u)) :=
      pow_le_height_pow_mul
        (H := p.H)
        (x := (13 : ℝ) *
          (2 * (((p.m : ℝ) + 12 * X) * HA) * HA) * u)
        (a := 13 + (2 + (((u + 15) + eA) + eA)) + u) (k := 3)
        hsourceCore_nonneg hsourceCore
    calc
      6 * (13 * (2 * (((p.m : ℝ) + 12 * X) * HA) * HA) * u) ^ 3 ≤
          p.H ^ 6 *
            p.H ^ (3 * (13 + (2 + (((u + 15) + eA) + eA)) + u)) :=
        mul_le_height_pows p.H_pos.le (pow_nonneg hsourceCore_nonneg 3)
          h6 hinnerPow
      _ = p.H ^ isolatedVertexQuotientSourceThreeSectionHeightExponent U := by
        change p.H ^ 6 *
            p.H ^ (3 * (13 + (2 + (((u + 15) + eA) + eA)) + u)) =
          p.H ^ (6 +
            3 * (13 + (2 + (((u + 15) + eA) + eA)) + u))
        exact (pow_add _ _ _).symm
  have hexp : isolatedVertexQuotientSourceThreeSectionHeightExponent U ≤
      isolatedVertexQuotientSourceSectionHeightExponent U :=
    le_max_right _ _
  have hmono : p.H ^ isolatedVertexQuotientSourceThreeSectionHeightExponent U ≤
      p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U :=
    pow_le_pow_right₀ hH hexp
  exact_mod_cast hreal.trans (hmono.trans
    (Nat.le_ceil (p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U)))

end

end TranslatedDepthSeven
