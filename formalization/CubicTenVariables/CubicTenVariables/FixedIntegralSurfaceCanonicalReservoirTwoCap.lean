import CubicTenVariables.FixedIntegralSurfacePrimeCountTwoCapModulusSensitiveCenteredReservoirCaps
import TranslatedDepthSeven.ProjectedSurfaceCanonicalReservoir
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCapNumerics

/-!
# Canonical-reservoir caps for the effective fixed-surface estimate

This file is downstream of the fixed-integral, modulus-sensitive two-cap
surface theorem.  It records the two caps supplied by the actual canonical
reservoir: the terminal modulus has size

`normalizedSurfaceReservoirConstant * T^(5/7) * H^delta`,

while an individual pool prime is at most the upper endpoint of the
canonical comparable-prime interval.  These are strictly sharper data than
the fallback bound `(primeCap P)^depth`.

The numerical statements at the end keep the remaining exponent budgets
visible.  In particular, they do not package the desired good-surface fibre
estimate as an extra premise.
-/

set_option autoImplicit false
noncomputable section

namespace TranslatedDepthSeven

open MvPolynomial Published
open Filter
open HessianTheorem11
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The real upper bound for every canonical reservoir modulus gives the
literal natural cap needed by the modulus-sensitive prefix assembly. -/
theorem terminalPrefix_modulus_le_ceil_canonicalReservoirUpper
    (scale : Parameters) {P : Finset ℕ} {depth : ℕ} {delta : ℝ}
    (hupper : ∀ q : ReservoirModulus P depth,
      (q.1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta)
    (v : PrimeSubsetPrefix.Vertex P depth)
    (hv : v.1.card = depth) :
    PrimeSubsetPrefix.modulus v ≤
      ⌈normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊ := by
  have hvMem := terminalPrefix_modulus_mem_modulusReservoir v hv
  have hvUpper := hupper ⟨PrimeSubsetPrefix.modulus v, hvMem⟩
  exact_mod_cast hvUpper.trans (Nat.le_ceil _)

/-- The upper endpoint of the actual comparable-prime interval bounds the
intrinsic prime cap used in the prefix graph. -/
theorem primeCap_le_canonicalPrimeInterval
    {A a H : ℝ} {P : Finset ℕ}
    (hinterval : ∀ p ∈ P,
      p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊) :
    PrimeSubsetPrefix.primeCap P ≤
      ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ := by
  exact PrimeSubsetPrefix.primeCap_le hinterval

/-- Eventually the fallback branch in `manuscriptPrimePoolAt` is absent,
so every prime in the literal canonical pool satisfies its displayed dyadic
upper endpoint. -/
theorem eventually_manuscriptPrimePoolAt_le_upperEndpoint
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1) :
    ∀ᶠ H : ℝ in atTop, ∀ p ∈ manuscriptPrimePoolAt A a H,
      p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ := by
  have hreservoir := eventually_exists_manuscriptReservoir
    (A := A) (a := a) (Cres := (2 : ℝ)) (ε := (1 : ℝ))
      hA ha haOne (by norm_num) (by norm_num)
  filter_upwards [hreservoir, eventually_ge_atTop (1 : ℝ)]
    with H hreservoirH hH
  obtain ⟨P, _k, hPcanonical, _hkcanonical, _hPcard, hinterval,
      _hkP, _hmoduli, _hmass, _hlcm, _hcertOne, _hcertTwo⟩ :=
    hreservoirH 1 (by norm_num) hH
  intro p hp
  have hpP : p ∈ P := by simpa only [hPcanonical] using hp
  exact (hinterval p hpP).2.2

/-- The canonical pool has exactly the advertised logarithmic reservoir
depth once its fallback branch is eventually absent. -/
theorem eventually_card_manuscriptPrimePoolAt
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1) :
    ∀ᶠ H : ℝ in atTop,
      (manuscriptPrimePoolAt A a H).card =
        reservoirDepth (manuscriptPoolDepthCoefficient A a) H := by
  have hreservoir := eventually_exists_manuscriptReservoir
    (A := A) (a := a) (Cres := (2 : ℝ)) (ε := (1 : ℝ))
      hA ha haOne (by norm_num) (by norm_num)
  filter_upwards [hreservoir, eventually_ge_atTop (1 : ℝ)]
    with H hreservoirH hH
  obtain ⟨P, _k, hPcanonical, _hkcanonical, hPcard, _hinterval,
      _hkP, _hmoduli, _hmass, _hlcm, _hcertOne, _hcertTwo⟩ :=
    hreservoirH 1 (by norm_num) hH
  simpa only [← hPcanonical] using hPcard

/-- The whole rooted prefix graph over a canonical-size pool is subpower.
This is the graph cardinality which multiplies the modulus-sensitive cell
majorant; the fixed-cardinality reservoir edge count alone would not bound
it. -/
theorem prefixDirectedEdges_cast_le_reservoirSubpower
    (P : Finset ℕ) (depth : ℕ) {M₀ H tau : ℝ}
    (hM₀ : 0 ≤ M₀) (htau : 0 < tau)
    (hPcard : P.card ≤ reservoirDepth M₀ H)
    (hthreshold : reservoirSubpowerThreshold M₀ 4 tau ≤ H) :
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) ≤ H ^ tau := by
  have hedgesNat : (PrimeSubsetPrefix.directedEdges P depth).card ≤
      4 ^ reservoirDepth M₀ H :=
    (PrimeSubsetPrefix.card_directedEdges_le_four_pow P depth).trans
      (Nat.pow_le_pow_right (by norm_num : 1 ≤ 4) hPcard)
  have hedges : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) ≤
      (4 : ℝ) ^ reservoirDepth M₀ H := by
    exact_mod_cast hedgesNat
  exact hedges.trans
    (reservoirBase_pow_depth_le_rpow hM₀ (by norm_num) htau hthreshold)

/-- Companion cap data for any canonical reservoir returned by
`eventually_exists_projectedSurface_canonicalReservoir`.  The terminal cap
uses its direct modulus bound; the prime cap comes from the same canonical
pool's actual comparable-prime interval. -/
theorem eventually_projectedSurfaceCanonical_prefixCaps
    {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ H : ℝ in atTop, ∀ (scale : Parameters), scale.H = H →
      ∀ (P : Finset ℕ) (depth : ℕ),
      P = manuscriptPrimePoolAt A (5 / 7) H →
      ∀ delta : ℝ,
      (∀ q : ReservoirModulus P depth,
        (q.1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
          scale.T ^ (5 / 7 : ℝ) * H ^ delta) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth, v.1.card = depth →
        PrimeSubsetPrefix.modulus v ≤
          ⌈normalizedSurfaceReservoirConstant *
            scale.T ^ (5 / 7 : ℝ) * H ^ delta⌉₊) ∧
      (∀ p ∈ P, p ≤
        ⌊2 * (manuscriptPrimeIntervalCoefficient A (5 / 7) *
          Real.log H)⌋₊) := by
  have hpool := eventually_manuscriptPrimePoolAt_le_upperEndpoint
    hA (by norm_num : (0 : ℝ) < 5 / 7) (by norm_num : (5 / 7 : ℝ) < 1)
  filter_upwards [hpool] with H hpoolH
  intro scale hscale P depth hPcanonical delta hupper
  subst H
  constructor
  · intro v hv
    exact terminalPrefix_modulus_le_ceil_canonicalReservoirUpper
      scale hupper v hv
  · intro p hp
    exact hpoolH p (by simpa only [hPcanonical] using hp)

/-- A convenient real form of a natural ceiling. -/
theorem natCeil_le_two_mul_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one (zero_le_one.trans hx)
  linarith

/-- The canonical terminal cap costs only a factor two when converted back
to a real inequality. -/
theorem canonicalTerminalCap_cast_le
    (scale : Parameters) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (⌈normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊ : ℝ) ≤
      2 * normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta := by
  have hC : (1 : ℝ) ≤ normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have hT : (1 : ℝ) ≤ scale.T ^ (5 / 7 : ℝ) :=
    Real.one_le_rpow scale.one_le_T (by norm_num)
  have hH : (1 : ℝ) ≤ scale.H ^ delta :=
    Real.one_le_rpow
      (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) hdelta
  have hx : (1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
      scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta := by
    nlinarith [mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hT)]
  simpa only [mul_assoc] using natCeil_le_two_mul_of_one_le hx

/-- A logarithmic canonical prime cap is subpower once a pointwise logarithm
bound is supplied.  The hypothesis is deliberately the standard explicit
inequality, rather than an opaque eventual predicate. -/
theorem canonicalPrimeInterval_cast_le_subpower
    {A a H rho : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hH : 1 ≤ H) (hrho : 0 < rho) :
    (⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ : ℝ) ≤
      2 * manuscriptPrimeIntervalCoefficient A a * (H ^ rho / rho) := by
  have hC : 0 ≤ manuscriptPrimeIntervalCoefficient A a := by
    unfold manuscriptPrimeIntervalCoefficient manuscriptPoolDepthCoefficient
    linarith
  have hlog : Real.log H ≤ H ^ rho / rho :=
    Real.log_le_rpow_div (zero_le_one.trans hH) hrho
  have hfloor :
      (⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ : ℝ) ≤
        2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H) := by
    exact Nat.floor_le (mul_nonneg (by positivity)
      (mul_nonneg hC (Real.log_nonneg hH)))
  calc
    (⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊ : ℝ) ≤
        2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H) := hfloor
    _ ≤ 2 * manuscriptPrimeIntervalCoefficient A a * (H ^ rho / rho) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hlog
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC))

/-- The centered closed-line ledger has the expected single progression
factor after casting.  This is the exact factor which later sits inside the
square in `GoodSurfaceFibreProgressionEstimate`. -/
theorem centeredLineFactor_cast_le
    {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 0 < m) :
    ((1 + ⌈2 * R⌉₊ / m : ℕ) : ℝ) ≤
      2 * (1 + R / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : ((⌈2 * R⌉₊ / m : ℕ) : ℝ) ≤
      (⌈2 * R⌉₊ : ℝ) / (m : ℝ) := Nat.cast_div_le
  have hceil : (⌈2 * R⌉₊ : ℝ) < 2 * R + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hR)
  have hone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have honeDiv : 1 / (m : ℝ) ≤ 1 := by
    exact (div_le_one hmR).2 hone
  push_cast
  calc
    (1 : ℝ) + (⌈2 * R⌉₊ / m : ℕ) ≤
        1 + (⌈2 * R⌉₊ : ℝ) / (m : ℝ) := by linarith
    _ ≤ 1 + (2 * R + 1) / (m : ℝ) := by
      gcongr
    _ ≤ 2 * (1 + R / (m : ℝ)) := by
      rw [add_div]
      have hRdiv : 0 ≤ R / (m : ℝ) := div_nonneg hR hmR.le
      have htwo : 2 * R / (m : ℝ) = 2 * (R / (m : ℝ)) := by ring
      rw [htwo]
      nlinarith

/-- The complete natural line-occurrence contribution is bounded by the
real occurrence mass times one centered progression factor. -/
theorem quantitativePrefixCenteredLineContribution_le
    (d Lroot Lterminal : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {m : ℕ} (hm : 0 < m) :
    ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal +
      quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal *
        (1 + ⌈2 * R⌉₊ / m) : ℕ) : ℝ) ≤
      3 * (quantitativePrefixEffectiveLineOccurrenceMassTwoCap
        d Lroot Lterminal : ℝ) * (1 + R / (m : ℝ)) := by
  let M := quantitativePrefixEffectiveLineOccurrenceMassTwoCap
    d Lroot Lterminal
  have hfac := centeredLineFactor_cast_le hR hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hratio : 1 ≤ 1 + R / (m : ℝ) :=
    le_add_of_nonneg_right (div_nonneg hR hmR.le)
  have hM : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hfac' : (1 : ℝ) + ((⌈2 * R⌉₊ / m : ℕ) : ℝ) ≤
      2 * (1 + R / (m : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hfac
  norm_num only [Nat.cast_add, Nat.cast_mul]
  dsimp only [M] at hM ⊢
  calc
    (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal : ℝ) +
        quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal *
          (1 + ((⌈2 * R⌉₊ / m : ℕ) : ℝ)) ≤
      (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal : ℝ) +
        quantitativePrefixEffectiveLineOccurrenceMassTwoCap d Lroot Lterminal *
          (2 * (1 + R / (m : ℝ))) := by
      simpa only [add_comm] using
        (add_le_add_left
          (mul_le_mul_of_nonneg_left hfac'
            (show (0 : ℝ) ≤
              quantitativePrefixEffectiveLineOccurrenceMassTwoCap
                d Lroot Lterminal by positivity))
          (quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal : ℝ))
    _ ≤ 3 * (quantitativePrefixEffectiveLineOccurrenceMassTwoCap
        d Lroot Lterminal : ℝ) * (1 + R / (m : ℝ)) := by
      nlinarith

/-- Insert the literal two-cap degree scales into the centered line ledger.
This records its exact current cost: one centered progression factor and the
degree exponent `a + 2*eta` in the absolute common height. -/
theorem quantitativePrefixCenteredLineContribution_le_commonHeight
    (d b H Baux Bpoint : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBaux : (Baux : ℝ) ≤ (Bpoint : ℝ) + 1)
    {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 0 < m) :
    ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H Baux eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) +
      quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H Baux eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) *
          (1 + ⌈2 * R⌉₊ / m) : ℕ) : ℝ) ≤
      3 * (((d : ℝ) * ((b : ℝ) + 5)) ^ (2 : ℕ) *
        ((Bpoint : ℝ) + 1) ^ (a + 2 * eta)) *
          (1 + R / (m : ℝ)) := by
  have hledger := quantitativePrefixCenteredLineContribution_le
    d (b + quantitativePrefixUniformBlockDegree H Baux eta a)
      (b + ⌈4 * (H : ℝ) ^ eta⌉₊) hR hm
  have hoccurrence :=
    quantitativePrefixEffectiveLineOccurrenceMassTwoCap_le_commonHeight
      d b H Baux Bpoint eta a heta ha hH hBaux
  apply hledger.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hoccurrence (by norm_num : (0 : ℝ) ≤ 3))
    (by positivity)

/-- The empty-root degree separates into the normalized-side power `T^a`
and the arbitrarily small determinant-height power `H^eta`. -/
theorem quantitativePrefixRootDegreeMass_le_normalizedSideHeight
    (scale : Parameters) (d b H : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ scale.H) :
    ((d * (b + quantitativePrefixUniformBlockDegree H
        (2 * surfaceTangentNaturalSide scale) eta a) : ℕ) : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a) *
        scale.H ^ eta * scale.T ^ a := by
  let X : ℝ := scale.H ^ eta * scale.T ^ a
  let C : ℝ := 4 * (6 : ℝ) ^ a
  have hHpow : (H : ℝ) ^ eta ≤ scale.H ^ eta :=
    Real.rpow_le_rpow (Nat.cast_nonneg H) hH heta
  have hBaux : ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ≤
      (6 : ℝ) * scale.T := by
    have hside := surfaceTangentNaturalSide_cast_le_three_mul scale
    change (surfaceTangentNaturalSide scale : ℝ) ≤ 3 * scale.T at hside
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hBpow : ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a ≤
      (6 : ℝ) ^ a * scale.T ^ a := by
    calc
      ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a ≤
          ((6 : ℝ) * scale.T) ^ a :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hBaux ha
      _ = (6 : ℝ) ^ a * scale.T ^ a := by
        rw [Real.mul_rpow (by norm_num) scale.T_pos.le]
  have hfactor : 1 ≤ (6 : ℝ) ^ a * scale.T ^ a := by
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (by norm_num) ha)
      (Real.one_le_rpow scale.one_le_T ha)
  have hraw :
      2 * (H : ℝ) ^ eta *
          (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a) ≤
        C * X := by
    calc
      2 * (H : ℝ) ^ eta *
          (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a) ≤
        2 * scale.H ^ eta *
          (1 + (6 : ℝ) ^ a * scale.T ^ a) := by
        have hsumPow :
            1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a ≤
              1 + (6 : ℝ) ^ a * scale.T ^ a :=
          by simpa only [add_comm] using add_le_add_right hBpow 1
        have hinner := mul_le_mul hHpow hsumPow
            (add_nonneg (by norm_num)
              (Real.rpow_nonneg (Nat.cast_nonneg _) a))
            (Real.rpow_nonneg scale.H_pos.le eta)
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hinner (show (0 : ℝ) ≤ 2 by norm_num))
      _ ≤ 2 * scale.H ^ eta *
          (2 * ((6 : ℝ) ^ a * scale.T ^ a)) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (by norm_num) (Real.rpow_nonneg scale.H_pos.le eta))
      _ = C * X := by
        dsimp only [C, X]
        ring
  have hraw0 : 0 ≤ 2 * (H : ℝ) ^ eta *
      (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a) := by
    positivity
  have hceil :
      (quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a : ℝ) ≤
        C * X + 1 := by
    have hlt :
        (quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a : ℝ) <
        2 * (H : ℝ) ^ eta *
          (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a) + 1 := by
      simpa only [quantitativePrefixUniformBlockDegree] using
        Nat.ceil_lt_add_one hraw0
    linarith
  have hX : 1 ≤ X := by
    dsimp only [X]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow
        (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) heta)
      (Real.one_le_rpow scale.one_le_T ha)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hb : 0 ≤ (b : ℝ) := by positivity
  have hsum : (b : ℝ) +
      (quantitativePrefixUniformBlockDegree H
        (2 * surfaceTangentNaturalSide scale) eta a : ℝ) ≤
      ((b : ℝ) + 1 + C) * X := by
    calc
      (b : ℝ) +
          (quantitativePrefixUniformBlockDegree H
            (2 * surfaceTangentNaturalSide scale) eta a : ℝ) ≤
        (b : ℝ) + (C * X + 1) := by linarith
      _ ≤ ((b : ℝ) + 1 + C) * X := by
        nlinarith [mul_nonneg (add_nonneg hb (by norm_num : (0 : ℝ) ≤ 1))
          (sub_nonneg.mpr hX)]
  norm_num only [Nat.cast_mul, Nat.cast_add]
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
  simpa only [C, X, mul_assoc] using hmul

/-- The full-reservoir terminal degree has no normalized-side loss. -/
theorem quantitativePrefixTerminalDegreeMass_le_height
    (scale : Parameters) (d b H : ℕ) (eta : ℝ)
    (heta : 0 ≤ eta) (hH : (H : ℝ) ≤ scale.H) :
    ((d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 5) * scale.H ^ eta := by
  have hHpow : (H : ℝ) ^ eta ≤ scale.H ^ eta :=
    Real.rpow_le_rpow (Nat.cast_nonneg H) hH heta
  have hceil : (⌈4 * (H : ℝ) ^ eta⌉₊ : ℝ) <
      4 * (H : ℝ) ^ eta + 1 := Nat.ceil_lt_add_one (by positivity)
  have hceilBound : (⌈4 * (H : ℝ) ^ eta⌉₊ : ℝ) ≤
      4 * scale.H ^ eta + 1 := by linarith
  have hpow : 1 ≤ scale.H ^ eta := Real.one_le_rpow
    (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) heta
  have hb : 0 ≤ (b : ℝ) := by positivity
  have hsum : (b : ℝ) + (⌈4 * (H : ℝ) ^ eta⌉₊ : ℝ) ≤
      ((b : ℝ) + 5) * scale.H ^ eta := by
    calc
      (b : ℝ) + (⌈4 * (H : ℝ) ^ eta⌉₊ : ℝ) ≤
          (b : ℝ) + (4 * scale.H ^ eta + 1) := by linarith
      _ ≤ ((b : ℝ) + 5) * scale.H ^ eta := by
        nlinarith [mul_nonneg (add_nonneg hb (by norm_num : (0 : ℝ) ≤ 1))
          (sub_nonneg.mpr hpow)]
  norm_num only [Nat.cast_mul, Nat.cast_add]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d))

/-- The two-cap occurrence mass has the sharp split scale
`T^a * H^(2*eta)`. -/
theorem quantitativePrefixEffectiveLineOccurrenceMassTwoCap_le_normalizedSideHeight
    (scale : Parameters) (d b H : ℕ) (eta a : ℝ)
    (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hH : (H : ℝ) ≤ scale.H) :
    (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
      (b + quantitativePrefixUniformBlockDegree H
        (2 * surfaceTangentNaturalSide scale) eta a)
      (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℝ) ≤
      ((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5)) *
        scale.T ^ a * scale.H ^ (2 * eta) := by
  have hroot := quantitativePrefixRootDegreeMass_le_normalizedSideHeight
    scale d b H eta a heta ha hH
  have hterminal := quantitativePrefixTerminalDegreeMass_le_height
    scale d b H eta heta hH
  have hterminal0 : (0 : ℝ) ≤
      (d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) := by positivity
  have hrootRhs0 : (0 : ℝ) ≤
      (d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a) *
        scale.H ^ eta * scale.T ^ a := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg d)
          (add_nonneg
            (add_nonneg (Nat.cast_nonneg b) (by norm_num))
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) a))))
        (Real.rpow_nonneg scale.H_pos.le eta))
      (Real.rpow_nonneg scale.T_pos.le a)
  calc
    (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℝ) =
      ((d * (b + quantitativePrefixUniformBlockDegree H
        (2 * surfaceTangentNaturalSide scale) eta a) : ℕ) : ℝ) *
      ((d * (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℕ) : ℝ) := by
        simp only [quantitativePrefixEffectiveLineOccurrenceMassTwoCap,
          Nat.cast_mul]
    _ ≤ ((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a) *
          scale.H ^ eta * scale.T ^ a) *
        ((d : ℝ) * ((b : ℝ) + 5) * scale.H ^ eta) :=
      mul_le_mul hroot hterminal hterminal0 hrootRhs0
    _ = ((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5)) *
        scale.T ^ a * scale.H ^ (2 * eta) := by
      rw [show (2 * eta) = eta + eta by ring, Real.rpow_add scale.H_pos]
      ring

/-- With the centered radius equal to the original progression radius, the
entire rational-line term is absorbed by `T^2 H^epsilon` as soon as
`2*eta <= epsilon` and `a <= 1`. -/
theorem quantitativePrefixCenteredLineContribution_le_goodSurfaceScale
    (scale : Parameters) (d b H : ℕ) (eta a epsilon : ℝ)
    (heta : 0 ≤ eta) (ha0 : 0 ≤ a) (haOne : a ≤ 1)
    (hH : (H : ℝ) ≤ scale.H) (hm : 0 < scale.m)
    (hbudget : 2 * eta ≤ epsilon) :
    ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) +
      quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) *
          (1 + ⌈2 * scale.L⌉₊ / scale.m) : ℕ) : ℝ) ≤
      3 * (((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5))) *
          scale.T ^ (2 : ℝ) * scale.H ^ epsilon := by
  have hledger := quantitativePrefixCenteredLineContribution_le
    d (b + quantitativePrefixUniformBlockDegree H
      (2 * surfaceTangentNaturalSide scale) eta a)
      (b + ⌈4 * (H : ℝ) ^ eta⌉₊) scale.L_nonneg hm
  have hoccurrence :=
    quantitativePrefixEffectiveLineOccurrenceMassTwoCap_le_normalizedSideHeight
      scale d b H eta a heta ha0 hH
  have hTexp : scale.T ^ (a + 1) ≤ scale.T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le scale.one_le_T (by linarith)
  have hHexp : scale.H ^ (2 * eta) ≤ scale.H ^ epsilon :=
    Real.rpow_le_rpow_of_exponent_le
      (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) hbudget
  apply hledger.trans
  have hfactor : 1 + scale.L / (scale.m : ℝ) = scale.T := rfl
  rw [hfactor]
  calc
    3 * (quantitativePrefixEffectiveLineOccurrenceMassTwoCap d
        (b + quantitativePrefixUniformBlockDegree H
          (2 * surfaceTangentNaturalSide scale) eta a)
        (b + ⌈4 * (H : ℝ) ^ eta⌉₊) : ℝ) * scale.T ≤
      3 * ((((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5)) * scale.T ^ a *
          scale.H ^ (2 * eta)) * scale.T) := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hoccurrence scale.T_pos.le)
            (show (0 : ℝ) ≤ 3 by norm_num))
    _ = 3 * (((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5))) *
          scale.T ^ (a + 1) * scale.H ^ (2 * eta) := by
      rw [Real.rpow_add scale.T_pos, Real.rpow_one]
      ring
    _ ≤ 3 * (((d : ℝ) * ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5))) *
          scale.T ^ (2 : ℝ) * scale.H ^ epsilon := by
      let K : ℝ := 3 * (((d : ℝ) *
        ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
          ((d : ℝ) * ((b : ℝ) + 5)))
      have hK : 0 ≤ K := by dsimp only [K]; positivity
      have hfirst : K * scale.T ^ (a + 1) ≤ K * scale.T ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hTexp hK
      exact mul_le_mul hfirst hHexp
        (Real.rpow_nonneg scale.H_pos.le _)
        (mul_nonneg hK (Real.rpow_nonneg scale.T_pos.le _))

/-- Once the canonical majorant has been obtained, the reservoir-family
cardinality and every displayed subpower loss absorb into the target height
power.  The normalized-side exponent `10/7` is strictly below the desired
quadratic progression factor. -/
theorem canonicalChangedEdgeContribution_le_goodSurfaceScale
    (scale : Parameters) (edgeCount : ℕ) (majorant C tau loss epsilon : ℝ)
    (hC : 0 ≤ C)
    (hedges : (edgeCount : ℝ) ≤ 2 * scale.H ^ tau)
    (hmajorant : majorant ≤
      C * scale.T ^ (10 / 7 : ℝ) * scale.H ^ loss)
    (hmajorant0 : 0 ≤ majorant)
    (hbudget : tau + loss ≤ epsilon) :
    (edgeCount : ℝ) * majorant ≤
      2 * C * scale.T ^ (2 : ℝ) * scale.H ^ epsilon := by
  have hHone : (1 : ℝ) ≤ scale.H :=
    scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)
  have hTpow : scale.T ^ (10 / 7 : ℝ) ≤ scale.T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le scale.one_le_T (by norm_num)
  have hHpow : scale.H ^ (tau + loss) ≤ scale.H ^ epsilon :=
    Real.rpow_le_rpow_of_exponent_le hHone hbudget
  calc
    (edgeCount : ℝ) * majorant ≤
        (2 * scale.H ^ tau) *
          (C * scale.T ^ (10 / 7 : ℝ) * scale.H ^ loss) := by
      exact mul_le_mul hedges hmajorant hmajorant0 (by positivity)
    _ = 2 * C * scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (tau + loss) := by
      rw [Real.rpow_add scale.H_pos]
      ring
    _ ≤ 2 * C * scale.T ^ (2 : ℝ) * scale.H ^ epsilon := by
      have hfirst : 2 * C * scale.T ^ (10 / 7 : ℝ) ≤
          2 * C * scale.T ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hTpow
          (mul_nonneg (by norm_num) hC)
      exact mul_le_mul hfirst hHpow
        (Real.rpow_nonneg scale.H_pos.le _)
        (mul_nonneg (mul_nonneg (by norm_num) hC)
          (Real.rpow_nonneg scale.T_pos.le _))

/-- Pure arithmetic behind the canonical `T^(10/7)` changed-edge scale.
Here `Tfive` denotes `T^(5/7)`, while `Xdelta` and `Xrho` carry the two
explicit subpower losses. -/
theorem modulusSensitiveBracket_le_canonicalProduct
    {A Q R Tfive Xdelta Xrho cA cQ cR : ℝ}
    (hA0 : 0 ≤ A) (hQ0 : 0 ≤ Q) (hR0 : 0 ≤ R)
    (hcA : 0 ≤ cA) (hcQ : 0 ≤ cQ) (hcR : 0 ≤ cR)
    (hTfive : 1 ≤ Tfive) (hXdelta : 1 ≤ Xdelta)
    (hXrho : 1 ≤ Xrho)
    (hA : A ≤ cA * Tfive)
    (hQ : Q ≤ cQ * Tfive * Xdelta)
    (hR : R ≤ cR * Xrho) :
    Q ^ (2 : ℕ) + A * Q * R + A * Q + A ^ (2 : ℕ) * R ≤
      (cQ ^ (2 : ℕ) + cA * cQ * cR + cA * cQ +
          cA ^ (2 : ℕ) * cR) *
        Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho := by
  have hTf0 : 0 ≤ Tfive := zero_le_one.trans hTfive
  have hXd0 : 0 ≤ Xdelta := zero_le_one.trans hXdelta
  have hXr0 : 0 ≤ Xrho := zero_le_one.trans hXrho
  have hq2 : Q ^ (2 : ℕ) ≤
      cQ ^ (2 : ℕ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho := by
    calc
      Q ^ (2 : ℕ) ≤ (cQ * Tfive * Xdelta) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hQ0 hQ 2
      _ = cQ ^ (2 : ℕ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) := by ring
      _ ≤ cQ ^ (2 : ℕ) * Tfive ^ (2 : ℕ) *
          Xdelta ^ (2 : ℕ) * Xrho := by
        exact le_mul_of_one_le_right (by positivity) hXrho
  have hAQR : A * Q * R ≤
      (cA * cQ * cR) * Tfive ^ (2 : ℕ) *
        Xdelta ^ (2 : ℕ) * Xrho := by
    calc
      A * Q * R ≤ (cA * Tfive) * (cQ * Tfive * Xdelta) *
          (cR * Xrho) := by gcongr
      _ = (cA * cQ * cR) * Tfive ^ (2 : ℕ) * Xdelta * Xrho := by ring
      _ ≤ (cA * cQ * cR) * Tfive ^ (2 : ℕ) *
          Xdelta ^ (2 : ℕ) * Xrho := by
        have hpad : Xdelta ≤ Xdelta ^ (2 : ℕ) := by
          simpa only [pow_two] using
            (le_mul_of_one_le_right hXd0 hXdelta)
        gcongr
  have hAQ : A * Q ≤
      (cA * cQ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho := by
    calc
      A * Q ≤ (cA * Tfive) * (cQ * Tfive * Xdelta) := by gcongr
      _ = (cA * cQ) * Tfive ^ (2 : ℕ) * Xdelta := by ring
      _ ≤ (cA * cQ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) := by
        have hpad : Xdelta ≤ Xdelta ^ (2 : ℕ) := by
          simpa only [pow_two] using
            (le_mul_of_one_le_right hXd0 hXdelta)
        gcongr
      _ ≤ (cA * cQ) * Tfive ^ (2 : ℕ) *
          Xdelta ^ (2 : ℕ) * Xrho := by
        exact le_mul_of_one_le_right (by positivity) hXrho
  have hA2R : A ^ (2 : ℕ) * R ≤
      (cA ^ (2 : ℕ) * cR) * Tfive ^ (2 : ℕ) *
        Xdelta ^ (2 : ℕ) * Xrho := by
    calc
      A ^ (2 : ℕ) * R ≤ (cA * Tfive) ^ (2 : ℕ) * (cR * Xrho) := by
        gcongr
      _ = (cA ^ (2 : ℕ) * cR) * Tfive ^ (2 : ℕ) * Xrho := by ring
      _ ≤ (cA ^ (2 : ℕ) * cR) * Tfive ^ (2 : ℕ) *
          Xdelta ^ (2 : ℕ) * Xrho := by
        have hone : 1 ≤ Xdelta ^ (2 : ℕ) := one_le_pow₀ hXdelta
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg cA) hcR)
          (sq_nonneg Tfive), mul_nonneg hXr0
          (mul_nonneg (mul_nonneg (sq_nonneg cA) hcR)
            (sq_nonneg Tfive))]
  calc
    Q ^ (2 : ℕ) + A * Q * R + A * Q + A ^ (2 : ℕ) * R ≤
        (cQ ^ (2 : ℕ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho) +
        ((cA * cQ * cR) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho) +
        ((cA * cQ) * Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho) +
        ((cA ^ (2 : ℕ) * cR) * Tfive ^ (2 : ℕ) *
          Xdelta ^ (2 : ℕ) * Xrho) := by linarith
    _ = (cQ ^ (2 : ℕ) + cA * cQ * cR + cA * cQ +
          cA ^ (2 : ℕ) * cR) *
        Tfive ^ (2 : ℕ) * Xdelta ^ (2 : ℕ) * Xrho := by ring

/-- Insert the actual canonical powers into the preceding product estimate.
The `T` exponent is exactly `10/7`; all losses from the modulus ceiling and
the logarithmic prime cap remain in the displayed `H` exponent. -/
theorem modulusSensitiveBracket_le_canonicalScale
    (scale : Parameters) (B Q R : ℕ)
    (cB cQ cR a delta rho : ℝ)
    (hcB : 0 ≤ cB) (hcQ : 0 ≤ cQ) (hcR : 0 ≤ cR)
    (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (hB : (B : ℝ) ≤ cB * scale.T)
    (hQ : (Q : ℝ) ≤ cQ * scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta)
    (hR : (R : ℝ) ≤ cR * scale.H ^ rho) :
    (Q : ℝ) ^ (2 : ℕ) + (B : ℝ) ^ a * Q * R +
        (B : ℝ) ^ a * Q + ((B : ℝ) ^ a) ^ (2 : ℕ) * R ≤
      (cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
          (cB ^ a) ^ (2 : ℕ) * cR) *
        scale.T ^ (10 / 7 : ℝ) * scale.H ^ (2 * delta + rho) := by
  have hA : (B : ℝ) ^ a ≤ cB ^ a * scale.T ^ (5 / 7 : ℝ) := by
    calc
      (B : ℝ) ^ a ≤ (cB * scale.T) ^ a :=
        Real.rpow_le_rpow (Nat.cast_nonneg B) hB ha0
      _ = cB ^ a * scale.T ^ a := by
        rw [Real.mul_rpow hcB scale.T_pos.le]
      _ ≤ cB ^ a * scale.T ^ (5 / 7 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le scale.one_le_T ha)
          (Real.rpow_nonneg hcB a)
  have hraw := modulusSensitiveBracket_le_canonicalProduct
    (A := (B : ℝ) ^ a) (Q := (Q : ℝ)) (R := (R : ℝ))
    (Tfive := scale.T ^ (5 / 7 : ℝ))
    (Xdelta := scale.H ^ delta) (Xrho := scale.H ^ rho)
    (cA := cB ^ a) (cQ := cQ) (cR := cR)
    (Real.rpow_nonneg (Nat.cast_nonneg B) a) (Nat.cast_nonneg Q)
    (Nat.cast_nonneg R) (Real.rpow_nonneg hcB a) hcQ hcR
    (Real.one_le_rpow scale.one_le_T (by norm_num))
    (Real.one_le_rpow
      (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) hdelta)
    (Real.one_le_rpow
      (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) hrho)
    hA hQ hR
  have hTpow : (scale.T ^ (5 / 7 : ℝ)) ^ (2 : ℕ) =
      scale.T ^ (10 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul scale.T_pos.le]
    congr 1
    norm_num
  have hHpow : (scale.H ^ delta) ^ (2 : ℕ) =
      scale.H ^ (2 * delta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul scale.H_pos.le]
    congr 1
    ring
  calc
    (Q : ℝ) ^ (2 : ℕ) + (B : ℝ) ^ a * Q * R +
        (B : ℝ) ^ a * Q + ((B : ℝ) ^ a) ^ (2 : ℕ) * R ≤
      (cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
          (cB ^ a) ^ (2 : ℕ) * cR) *
        (scale.T ^ (5 / 7 : ℝ)) ^ (2 : ℕ) *
        (scale.H ^ delta) ^ (2 : ℕ) * scale.H ^ rho := hraw
    _ = (cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
          (cB ^ a) ^ (2 : ℕ) * cR) *
        scale.T ^ (10 / 7 : ℝ) * scale.H ^ (2 * delta + rho) := by
      rw [hTpow, hHpow]
      have hadd : scale.H ^ (2 * delta) * scale.H ^ rho =
          scale.H ^ (2 * delta + rho) := by
        rw [← Real.rpow_add scale.H_pos]
      rw [← hadd]
      ring

/-- The complete changed-edge majorant at canonical reservoir scale.  The
leading normalized-side power is `T^(10/7)`.  The separate losses are the
prefix discriminant factor `sigma`, the two determinant degrees `2*eta`,
the squared terminal modulus `2*delta`, and the logarithmic prime-cap loss
`rho`. -/
theorem quantitativePrefixModulusSensitiveEdgeMajorant_le_canonicalScale
    (scale : Parameters)
    (Delta depth d b H B Q R : ℕ)
    (cB cQ cR eta a sigma delta rho : ℝ)
    (hcB : 0 ≤ cB) (hcQ : 0 ≤ cQ) (hcR : 0 ≤ cR)
    (heta : 0 ≤ eta) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rho)
    (hDelta : (((max 1 Delta : ℕ) : ℝ) ^ depth) ≤ scale.H ^ sigma)
    (hH : (H : ℝ) ≤ scale.H)
    (hB : (B : ℝ) ≤ cB * scale.T)
    (hQ : (Q : ℝ) ≤ cQ * scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta)
    (hR : (R : ℝ) ≤ cR * scale.H ^ rho) :
    quantitativePrefixModulusSensitiveEdgeMajorant
        Delta depth d b H B Q R eta a ≤
      ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
        (cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
          (cB ^ a) ^ (2 : ℕ) * cR) *
        scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
  let K : ℝ := cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
    (cB ^ a) ^ (2 : ℕ) * cR
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hHpow : (H : ℝ) ^ (2 * eta) ≤ scale.H ^ (2 * eta) :=
    Real.rpow_le_rpow (Nat.cast_nonneg H) hH (mul_nonneg (by norm_num) heta)
  have hbracket := modulusSensitiveBracket_le_canonicalScale
    scale B Q R cB cQ cR a delta rho hcB hcQ hcR ha0 ha hdelta hrho
      hB hQ hR
  have hscaleH : (1 : ℝ) ≤ scale.H :=
    scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)
  have hDcoef : 0 ≤ (d : ℝ) * ((b : ℝ) + 2) := by positivity
  have hpow : scale.H ^ sigma * scale.H ^ (2 * eta) *
      scale.H ^ (2 * delta + rho) =
      scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
    calc
      scale.H ^ sigma * scale.H ^ (2 * eta) *
          scale.H ^ (2 * delta + rho) =
        scale.H ^ (sigma + 2 * eta) *
          scale.H ^ (2 * delta + rho) := by
            rw [← Real.rpow_add scale.H_pos]
      _ = scale.H ^ ((sigma + 2 * eta) + (2 * delta + rho)) := by
        rw [← Real.rpow_add scale.H_pos]
      _ = scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
        congr 1
        ring
  unfold quantitativePrefixModulusSensitiveEdgeMajorant
  calc
    ((max 1 Delta : ℕ) : ℝ) ^ depth *
        (((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
          (H : ℝ) ^ (2 * eta) *
          ((Q : ℝ) ^ (2 : ℕ) + (B : ℝ) ^ a * Q * R +
            (B : ℝ) ^ a * Q + ((B : ℝ) ^ a) ^ (2 : ℕ) * R)) ≤
      scale.H ^ sigma *
        (((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
          scale.H ^ (2 * eta) *
          (K * scale.T ^ (10 / 7 : ℝ) *
            scale.H ^ (2 * delta + rho))) := by
      gcongr
    _ = ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) * K *
        scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
      rw [← hpow]
      ring
    _ = ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
        (cQ ^ (2 : ℕ) + cB ^ a * cQ * cR + cB ^ a * cQ +
          (cB ^ a) ^ (2 : ℕ) * cR) *
        scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
      rfl

/-- The fixed prefix discriminant factor is subpower at any depth bounded by
the canonical reservoir depth. -/
theorem prefixDiscriminantFactor_le_reservoirSubpower
    (scale : Parameters) (Delta depth : ℕ) (M₀ sigma : ℝ)
    (hM₀ : 0 ≤ M₀) (hsigma : 0 < sigma)
    (hdepth : depth ≤ reservoirDepth M₀ scale.H)
    (hthreshold : reservoirSubpowerThreshold M₀
      ((max 1 Delta : ℕ) : ℝ) sigma ≤ scale.H) :
    (((max 1 Delta : ℕ) : ℝ) ^ depth) ≤ scale.H ^ sigma := by
  have hbaseNat : 1 ≤ max 1 Delta := le_max_left _ _
  have hpowNat : (max 1 Delta) ^ depth ≤
      (max 1 Delta) ^ reservoirDepth M₀ scale.H :=
    Nat.pow_le_pow_right hbaseNat hdepth
  have hpow : (((max 1 Delta : ℕ) : ℝ) ^ depth) ≤
      ((max 1 Delta : ℕ) : ℝ) ^ reservoirDepth M₀ scale.H := by
    exact_mod_cast hpowNat
  exact hpow.trans (reservoirBase_pow_depth_le_rpow hM₀
    (by exact_mod_cast hbaseNat) hsigma hthreshold)

/-- Concrete numerical specialization using exactly the ceiling terminal
cap and floor prime cap supplied by the projected-surface canonical
reservoir.  Its leading changed-edge scale is `T^(10/7)`, with the fully
displayed subpower loss `sigma + 2*eta + 2*delta + rho`. -/
theorem
    quantitativePrefixModulusSensitiveEdgeMajorant_le_projectedSurfaceCanonicalCaps
    (scale : Parameters) (Delta depth d b H : ℕ)
    (Ares M₀ eta a sigma delta rho : ℝ)
    (hAres : 0 ≤ Ares) (hM₀ : 0 ≤ M₀)
    (heta : 0 ≤ eta) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (hsigma : 0 < sigma) (hdelta : 0 ≤ delta) (hrho : 0 < rho)
    (hdepth : depth ≤ reservoirDepth M₀ scale.H)
    (hthreshold : reservoirSubpowerThreshold M₀
      ((max 1 Delta : ℕ) : ℝ) sigma ≤ scale.H)
    (hH : (H : ℝ) ≤ scale.H) :
    let Baux := 2 * surfaceTangentNaturalSide scale
    let Q := ⌈normalizedSurfaceReservoirConstant *
      scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
    let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
      Real.log scale.H)⌋₊
    let cQ : ℝ := 2 * normalizedSurfaceReservoirConstant
    let cR : ℝ := 2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho
    quantitativePrefixModulusSensitiveEdgeMajorant
        Delta depth d b H Baux Q Rprime eta a ≤
      ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
        (cQ ^ (2 : ℕ) + (6 : ℝ) ^ a * cQ * cR +
          (6 : ℝ) ^ a * cQ + ((6 : ℝ) ^ a) ^ (2 : ℕ) * cR) *
        scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
  dsimp only
  have hDelta := prefixDiscriminantFactor_le_reservoirSubpower
    scale Delta depth M₀ sigma hM₀ hsigma hdepth hthreshold
  have hB : ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ≤
      (6 : ℝ) * scale.T := by
    have hside := surfaceTangentNaturalSide_cast_le_three_mul scale
    change (surfaceTangentNaturalSide scale : ℝ) ≤ 3 * scale.T at hside
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hQ := canonicalTerminalCap_cast_le scale hdelta
  have hRraw := canonicalPrimeInterval_cast_le_subpower
    hAres (by norm_num : (0 : ℝ) ≤ 5 / 7)
    (scale.five_le_H.trans' (by norm_num : (1 : ℝ) ≤ 5)) hrho
  have hR :
      (⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
          Real.log scale.H)⌋₊ : ℝ) ≤
        (2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho) *
          scale.H ^ rho := by
    calc
      (⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
          Real.log scale.H)⌋₊ : ℝ) ≤
        2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
          (scale.H ^ rho / rho) := hRraw
      _ = (2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho) *
          scale.H ^ rho := by ring
  have hCprime : 0 ≤ manuscriptPrimeIntervalCoefficient Ares (5 / 7) := by
    unfold manuscriptPrimeIntervalCoefficient manuscriptPoolDepthCoefficient
    linarith
  exact quantitativePrefixModulusSensitiveEdgeMajorant_le_canonicalScale
    scale Delta depth d b H (2 * surfaceTangentNaturalSide scale)
      ⌈normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
      ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
        Real.log scale.H)⌋₊
      6 (2 * normalizedSurfaceReservoirConstant)
      (2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho)
      eta a sigma delta rho
      (by norm_num)
      (by
        norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
          tangentCoordinateConstant, Nat.factorial])
      (div_nonneg (mul_nonneg (by norm_num) hCprime) hrho.le)
      heta ha0 ha hdelta hrho.le hDelta hH hB
      (by simpa only [mul_assoc] using hQ) hR

/-- Complete absorption of the actual rooted-prefix changed-edge term.  The
pool-cardinality loss `tau` and all cell losses are charged to the final
height epsilon, while `T^(10/7)` is absorbed by the quadratic progression
factor. -/
theorem
    quantitativePrefixCanonicalChangedEdgeTerm_le_goodSurfaceScale
    (scale : Parameters) (P : Finset ℕ)
    (Delta depth d b H : ℕ)
    (Ares Mpool M₀ eta a tau sigma delta rho epsilon : ℝ)
    (hAres : 0 ≤ Ares) (hMpool : 0 ≤ Mpool) (hM₀ : 0 ≤ M₀)
    (heta : 0 ≤ eta) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (htau : 0 < tau) (hsigma : 0 < sigma)
    (hdelta : 0 ≤ delta) (hrho : 0 < rho)
    (hPcard : P.card ≤ reservoirDepth Mpool scale.H)
    (hgraphThreshold : reservoirSubpowerThreshold Mpool 4 tau ≤ scale.H)
    (hdepth : depth ≤ reservoirDepth M₀ scale.H)
    (hDeltaThreshold : reservoirSubpowerThreshold M₀
      ((max 1 Delta : ℕ) : ℝ) sigma ≤ scale.H)
    (hH : (H : ℝ) ≤ scale.H)
    (hbudget : tau + (sigma + 2 * eta + 2 * delta + rho) ≤ epsilon) :
    let Baux := 2 * surfaceTangentNaturalSide scale
    let Q := ⌈normalizedSurfaceReservoirConstant *
      scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
    let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
      Real.log scale.H)⌋₊
    let cQ : ℝ := 2 * normalizedSurfaceReservoirConstant
    let cR : ℝ := 2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho
    let Cedge : ℝ := ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
      (cQ ^ (2 : ℕ) + (6 : ℝ) ^ a * cQ * cR +
        (6 : ℝ) ^ a * cQ + ((6 : ℝ) ^ a) ^ (2 : ℕ) * cR)
    ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
        quantitativePrefixModulusSensitiveEdgeMajorant
          Delta depth d b H Baux Q Rprime eta a ≤
      2 * Cedge * scale.T ^ (2 : ℝ) * scale.H ^ epsilon := by
  dsimp only
  let cQ : ℝ := 2 * normalizedSurfaceReservoirConstant
  let cR : ℝ := 2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho
  let Cedge : ℝ := ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
    (cQ ^ (2 : ℕ) + (6 : ℝ) ^ a * cQ * cR +
      (6 : ℝ) ^ a * cQ + ((6 : ℝ) ^ a) ^ (2 : ℕ) * cR)
  let majorant := quantitativePrefixModulusSensitiveEdgeMajorant
    Delta depth d b H (2 * surfaceTangentNaturalSide scale)
      ⌈normalizedSurfaceReservoirConstant *
        scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
      ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
        Real.log scale.H)⌋₊ eta a
  have hmajorant : majorant ≤
      Cedge * scale.T ^ (10 / 7 : ℝ) *
        scale.H ^ (sigma + 2 * eta + 2 * delta + rho) := by
    dsimp only [majorant, Cedge, cQ, cR]
    exact
      quantitativePrefixModulusSensitiveEdgeMajorant_le_projectedSurfaceCanonicalCaps
        scale Delta depth d b H Ares M₀ eta a sigma delta rho
          hAres hM₀ heta ha0 ha hsigma hdelta hrho hdepth
          hDeltaThreshold hH
  have hmajorant0 : 0 ≤ majorant := by
    dsimp only [majorant, quantitativePrefixModulusSensitiveEdgeMajorant]
    positivity
  have hCedge : 0 ≤ Cedge := by
    dsimp only [Cedge, cQ, cR]
    have hCprime : 0 ≤ manuscriptPrimeIntervalCoefficient Ares (5 / 7) := by
      unfold manuscriptPrimeIntervalCoefficient manuscriptPoolDepthCoefficient
      linarith
    have hcQ : 0 ≤ 2 * normalizedSurfaceReservoirConstant := by
      norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
        tangentCoordinateConstant, Nat.factorial]
    have hcR : 0 ≤
        2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho :=
      div_nonneg (mul_nonneg (by norm_num) hCprime) hrho.le
    positivity
  have hedgeRaw := prefixDirectedEdges_cast_le_reservoirSubpower
    P depth hMpool htau hPcard hgraphThreshold
  have hedges : ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) ≤
      2 * scale.H ^ tau := by
    exact hedgeRaw.trans (by
      have hnonneg := Real.rpow_nonneg scale.H_pos.le tau
      linarith)
  exact canonicalChangedEdgeContribution_le_goodSurfaceScale
    scale (PrimeSubsetPrefix.directedEdges P depth).card majorant Cedge tau
      (sigma + 2 * eta + 2 * delta + rho) epsilon hCedge hedges
      hmajorant hmajorant0 hbudget

/-- Numerical closure of the complete canonical two-cap ledger.  The
changed-edge term is in the desired `T^2 H^epsilon` shape.  The last two
summands display honestly what remains before the full good-surface fibre
estimate: the line occurrence degree and nonlinear curve residual still use
the absolute point-height parameter `Bpoint + 1`. -/
theorem quantitativePrefixCanonicalTwoCapLedger_le_numericalEnvelope
    (scale : Parameters) (P : Finset ℕ)
    (Delta depth d b H Bpoint m : ℕ) (Rbox Ccurve : ℝ)
    (Ares Mpool M₀ eta a tau sigma delta rho epsilon : ℝ)
    (hAres : 0 ≤ Ares) (hMpool : 0 ≤ Mpool) (hM₀ : 0 ≤ M₀)
    (hCcurve : 0 ≤ Ccurve)
    (heta : 0 < eta) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (htau : 0 < tau) (hsigma : 0 < sigma)
    (hdelta : 0 ≤ delta) (hrho : 0 < rho)
    (hPcard : P.card ≤ reservoirDepth Mpool scale.H)
    (hgraphThreshold : reservoirSubpowerThreshold Mpool 4 tau ≤ scale.H)
    (hdepth : depth ≤ reservoirDepth M₀ scale.H)
    (hDeltaThreshold : reservoirSubpowerThreshold M₀
      ((max 1 Delta : ℕ) : ℝ) sigma ≤ scale.H)
    (hHscale : (H : ℝ) ≤ scale.H)
    (hHpoint : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBauxPoint : ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ≤
      (Bpoint : ℝ) + 1)
    (hRbox : 0 ≤ Rbox) (hm : 0 < m)
    (hbudget : tau + (sigma + 2 * eta + 2 * delta + rho) ≤ epsilon)
    (Xcard : ℝ) :
    let Baux := 2 * surfaceTangentNaturalSide scale
    let Lroot := b + quantitativePrefixUniformBlockDegree H Baux eta a
    let Lterminal := b + ⌈4 * (H : ℝ) ^ eta⌉₊
    let Q := ⌈normalizedSurfaceReservoirConstant *
      scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
    let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
      Real.log scale.H)⌋₊
    let cQ : ℝ := 2 * normalizedSurfaceReservoirConstant
    let cR : ℝ := 2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho
    let Cedge : ℝ := ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
      (cQ ^ (2 : ℕ) + (6 : ℝ) ^ a * cQ * cR +
        (6 : ℝ) ^ a * cQ + ((6 : ℝ) ^ a) ^ (2 : ℕ) * cR)
    Xcard ≤
      ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
          quantitativePrefixModulusSensitiveEdgeMajorant
            Delta depth d b H Baux Q Rprime eta a +
        ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal +
          quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal * (1 + ⌈2 * Rbox⌉₊ / m) : ℕ) : ℝ) +
        quantitativePrefixEffectiveCurveResidualTwoCap
          Ccurve d Lroot Lterminal Bpoint →
    Xcard ≤
      2 * Cedge * scale.T ^ (2 : ℝ) * scale.H ^ epsilon +
      3 * (((d : ℝ) * ((b : ℝ) + 5)) ^ (2 : ℕ) *
        ((Bpoint : ℝ) + 1) ^ (a + 2 * eta)) *
          (1 + Rbox / (m : ℝ)) +
      Ccurve * ((d : ℝ) * ((b : ℝ) + 5)) ^ (5 : ℕ) *
        (eta⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
          ((Bpoint : ℝ) + 1) ^ ((1 / 2 : ℝ) + a + 6 * eta) := by
  dsimp only
  intro hcount
  have hedge :=
    quantitativePrefixCanonicalChangedEdgeTerm_le_goodSurfaceScale
      scale P Delta depth d b H Ares Mpool M₀ eta a tau sigma delta rho
        epsilon hAres hMpool hM₀ heta.le ha0 ha htau hsigma hdelta hrho
        hPcard hgraphThreshold hdepth hDeltaThreshold hHscale hbudget
  have hline := quantitativePrefixCenteredLineContribution_le_commonHeight
    d b H (2 * surfaceTangentNaturalSide scale) Bpoint eta a heta.le ha0
      hHpoint hBauxPoint hRbox hm
  have hresidual :=
    quantitativePrefixEffectiveCurveResidualTwoCap_le_commonHeight
      Ccurve d b H (2 * surfaceTangentNaturalSide scale) Bpoint eta a
        hCcurve heta ha0 hHpoint hBauxPoint
  linarith

/-- When the centered ledger uses the actual progression radius `scale.L`
and modulus `scale.m`, both the changed-edge and rational-line terms have the
good-surface shape `T^2 H^epsilon`.  The sole remaining numerical summand is
the nonlinear curve residual at the absolute height `Bpoint + 1`. -/
theorem
    quantitativePrefixCanonicalTwoCapLedger_le_goodSurfaceScale_plusNonlinearResidual
    (scale : Parameters) (P : Finset ℕ)
    (Delta depth d b H Bpoint : ℕ) (Ccurve : ℝ)
    (Ares Mpool M₀ eta a tau sigma delta rho epsilon : ℝ)
    (hAres : 0 ≤ Ares) (hMpool : 0 ≤ Mpool) (hM₀ : 0 ≤ M₀)
    (hCcurve : 0 ≤ Ccurve)
    (heta : 0 < eta) (ha0 : 0 ≤ a) (ha : a ≤ 5 / 7)
    (htau : 0 < tau) (hsigma : 0 < sigma)
    (hdelta : 0 ≤ delta) (hrho : 0 < rho)
    (hPcard : P.card ≤ reservoirDepth Mpool scale.H)
    (hgraphThreshold : reservoirSubpowerThreshold Mpool 4 tau ≤ scale.H)
    (hdepth : depth ≤ reservoirDepth M₀ scale.H)
    (hDeltaThreshold : reservoirSubpowerThreshold M₀
      ((max 1 Delta : ℕ) : ℝ) sigma ≤ scale.H)
    (hHscale : (H : ℝ) ≤ scale.H)
    (hHpoint : (H : ℝ) ≤ (Bpoint : ℝ) + 1)
    (hBauxPoint : ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ≤
      (Bpoint : ℝ) + 1)
    (hedgeBudget : tau + (sigma + 2 * eta + 2 * delta + rho) ≤ epsilon)
    (hlineBudget : 2 * eta ≤ epsilon)
    (Xcard : ℝ) :
    let Baux := 2 * surfaceTangentNaturalSide scale
    let Lroot := b + quantitativePrefixUniformBlockDegree H Baux eta a
    let Lterminal := b + ⌈4 * (H : ℝ) ^ eta⌉₊
    let Q := ⌈normalizedSurfaceReservoirConstant *
      scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
    let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
      Real.log scale.H)⌋₊
    let cQ : ℝ := 2 * normalizedSurfaceReservoirConstant
    let cR : ℝ := 2 * manuscriptPrimeIntervalCoefficient Ares (5 / 7) / rho
    let Cedge : ℝ := ((d : ℝ) * ((b : ℝ) + 2)) ^ (2 : ℕ) *
      (cQ ^ (2 : ℕ) + (6 : ℝ) ^ a * cQ * cR +
        (6 : ℝ) ^ a * cQ + ((6 : ℝ) ^ a) ^ (2 : ℕ) * cR)
    let Cline : ℝ := ((d : ℝ) *
      ((b : ℝ) + 1 + 4 * (6 : ℝ) ^ a)) *
        ((d : ℝ) * ((b : ℝ) + 5))
    Xcard ≤
      ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
          quantitativePrefixModulusSensitiveEdgeMajorant
            Delta depth d b H Baux Q Rprime eta a +
        ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal +
          quantitativePrefixEffectiveLineOccurrenceMassTwoCap
            d Lroot Lterminal *
              (1 + ⌈2 * scale.L⌉₊ / scale.m) : ℕ) : ℝ) +
        quantitativePrefixEffectiveCurveResidualTwoCap
          Ccurve d Lroot Lterminal Bpoint →
    Xcard ≤
      2 * Cedge * scale.T ^ (2 : ℝ) * scale.H ^ epsilon +
      3 * Cline * scale.T ^ (2 : ℝ) * scale.H ^ epsilon +
      Ccurve * ((d : ℝ) * ((b : ℝ) + 5)) ^ (5 : ℕ) *
        (eta⁻¹ + (d : ℝ) * ((b : ℝ) + 5)) *
          ((Bpoint : ℝ) + 1) ^ ((1 / 2 : ℝ) + a + 6 * eta) := by
  dsimp only
  intro hcount
  have hedge :=
    quantitativePrefixCanonicalChangedEdgeTerm_le_goodSurfaceScale
      scale P Delta depth d b H Ares Mpool M₀ eta a tau sigma delta rho
        epsilon hAres hMpool hM₀ heta.le ha0 ha htau hsigma hdelta hrho
        hPcard hgraphThreshold hdepth hDeltaThreshold hHscale hedgeBudget
  have hline := quantitativePrefixCenteredLineContribution_le_goodSurfaceScale
    scale d b H eta a epsilon heta.le ha0 (ha.trans (by norm_num))
      hHscale scale.hm hlineBudget
  have hresidual :=
    quantitativePrefixEffectiveCurveResidualTwoCap_le_commonHeight
      Ccurve d b H (2 * surfaceTangentNaturalSide scale) Bpoint eta a
        hCcurve heta ha0 hHpoint hBauxPoint
  linarith

/-- Fixed-integral-surface endpoint specialized to the actual terminal and
prime caps of the projected-surface canonical reservoir.  In particular,
the changed-edge term uses the ceiling of the direct `T^(5/7)` modulus bound,
not `(primeCap P)^depth`. -/
theorem
    exists_fixedSurface_quantitativePrefixSurfaceCount_effective_twoCap_projectedSurfaceCanonicalCaps_closedLines_centered_of_integralSurface
    (integralityOpen : CubicTenVariables.Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : CubicTenVariables.Literature.AffinePlaneCurveWeil)
    (hCurve : CDHNV2025Corollary22)
    {d : ℕ} (hd : 2 ≤ d)
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (Kred : ℝ) (hKred : 1 < Kred) (Aex : ℕ)
    (Ares delta eta a : ℝ)
    (heta : 0 < eta) (ha0 : 0 ≤ a) (haUpper : a ≤ 5 / 7)
    (haDet : Real.sqrt Kred / Real.sqrt (d : ℝ) < a) :
    ∃ Dsurface b D A H₀ : ℕ, ∃ Cdet Ccurve : ℝ,
      0 < Dsurface ∧
      1 ≤ D ∧ 2 ≤ A ∧ 2 ≤ H₀ ∧ 0 ≤ Cdet ∧ 0 < Ccurve ∧
      ∀ (scale : Parameters) (P : Finset ℕ)
        (depth H Bpoint m Dex : ℕ)
        (u : IntVector 3) (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3)
        (center : RealVector 3) (Rbox : ℝ),
      Dsurface ∣ Dex →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ¬ p ∣ m) →
      H₀ ≤ H →
      0 < Dex → Dex ≤ H ^ Aex → m * primeProduct P ∣ Dex →
      m ≠ 0 →
      (∀ q ∈ modulusReservoir P depth,
        manuscriptReservoirTarget normalizedSurfaceReservoirConstant
          scale.T (5 / 7) ≤ q) →
      (∀ q : ReservoirModulus P depth,
        (q.1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
          scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta) →
      (∀ p ∈ P, p ≤
        ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
          Real.log scale.H)⌋₊) →
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ z ∈ X, ∀ i,
        (progressionHomogeneousPoint u m z i).natAbs ≤ H) →
      (∀ z ∈ X, ∀ i,
        (z i).natAbs ≤ 2 * surfaceTangentNaturalSide scale) →
      (∀ z ∈ X,
        MvPolynomial.eval (progressionHomogeneousPoint u m z) F = 0) →
      (∀ z ∈ X, ∃ v, MvPolynomial.eval
        (fun i => u i + (m : ℤ) * z i)
        (MvPolynomial.pderiv v
          (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      (∀ z ∈ X, ∀ p ∈ P, ∃ v,
        (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
          (MvPolynomial.pderiv v
            (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      1 ≤ Bpoint →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ (Bpoint : ℝ)) →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ Rbox) →
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ,
        (∀ v : PrimeSubsetPrefix.Vertex P depth,
          0 < blockDegree v ∧
          ((blockDegree v : ℕ) : ℝ) ≤ 2 * (H : ℝ) ^ eta *
            (1 + ((2 * surfaceTangentNaturalSide scale : ℕ) : ℝ) ^ a /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (∀ rho ∈ occupiedIntegralResidues
              (PrimeSubsetPrefix.modulus v) X,
            (auxiliary v rho).IsHomogeneous (b + blockDegree v) ∧
              auxiliary v rho ∉ finiteEquationIdeal sourceEquations) ∧
          ∀ z ∈ X, MvPolynomial.eval
            (fun i => (progressionHomogeneousPoint u m z i : ℚ))
              (auxiliary v (integralResidueVector z)) = 0) ∧
        let Baux := 2 * surfaceTangentNaturalSide scale
        let Lroot := b + quantitativePrefixUniformBlockDegree H Baux eta a
        let Lterminal := b + ⌈4 * (H : ℝ) ^ eta⌉₊
        let Q := ⌈normalizedSurfaceReservoirConstant *
          scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
        let Rprime := ⌊2 * (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
          Real.log scale.H)⌋₊
        (X.card : ℝ) ≤
          ((PrimeSubsetPrefix.directedEdges P depth).card : ℝ) *
            quantitativePrefixModulusSensitiveEdgeMajorant
              (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree
              depth d b H Baux Q Rprime eta a +
          ((quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal +
            quantitativePrefixEffectiveLineOccurrenceMassTwoCap
              d Lroot Lterminal *
                (1 + ⌈2 * Rbox⌉₊ / m) : ℕ) : ℝ) +
          quantitativePrefixEffectiveCurveResidualTwoCap
            Ccurve d Lroot Lterminal Bpoint := by
  classical
  obtain ⟨Dsurface, b, D, A, H₀, Cdet, Ccurve, hDsurface, hD, hA,
      hH₀, hCdet, hCcurve, hbound⟩ :=
    exists_fixedSurface_quantitativePrefixSurfaceCount_effective_twoCap_modulusSensitive_closedLines_centered_of_integralSurface_with_reservoirCaps
      integralityOpen curveWeil hCurve hd sourceEquations hprime
        hgeometricPrime hhom hchart hdegree F hF0 hF hgeom Kred hKred Aex
        eta a heta ha0 haUpper haDet
  refine ⟨Dsurface, b, D, A, H₀, Cdet, Ccurve,
    hDsurface, hD, hA, hH₀, hCdet, hCcurve, ?_⟩
  intro scale P depth H Bpoint m Dex u X allowed z₀ center Rbox
    hDsurfaceDex hP hPm hH hDex hDexHeight hmPDex hm hlower
    hmodulusUpper hprimeUpper hz₀ hallowed hroom hheight hboxAux hzero
    hgradient hsmooth hsource hBpoint hboxPoint hboxCentered
  let Q : ℕ := ⌈normalizedSurfaceReservoirConstant *
    scale.T ^ (5 / 7 : ℝ) * scale.H ^ delta⌉₊
  let Rprime : ℕ := ⌊2 *
    (manuscriptPrimeIntervalCoefficient Ares (5 / 7) *
      Real.log scale.H)⌋₊
  have hmodulusCap : ∀ q ∈ modulusReservoir P depth, q ≤ Q := by
    intro q hq
    dsimp only [Q]
    have hqUpper := hmodulusUpper ⟨q, hq⟩
    exact_mod_cast hqUpper.trans (Nat.le_ceil _)
  obtain ⟨blockDegree, auxiliary, hauxiliary, hcount⟩ :=
    hbound scale P depth H Bpoint m Dex Q Rprime u X allowed z₀ center Rbox
      hDsurfaceDex hP hPm hH hDex hDexHeight hmPDex hm hlower
      hmodulusCap hprimeUpper hz₀ hallowed hroom hheight hboxAux hzero
      hgradient hsmooth hsource hBpoint hboxPoint hboxCentered
  refine ⟨blockDegree, auxiliary, hauxiliary, ?_⟩
  simpa only [Q, Rprime] using hcount

end TranslatedDepthSeven
