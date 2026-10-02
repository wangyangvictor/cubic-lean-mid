import TranslatedDepthSeven.ComparableCertificateScale
import TranslatedDepthSeven.ComparableCoprimality
import TranslatedDepthSeven.ManuscriptCrossingDepth
import TranslatedDepthSeven.ManuscriptPrimeScale
import TranslatedDepthSeven.ManuscriptReservoirTarget
import TranslatedDepthSeven.ReservoirDepthRoom
import TranslatedDepthSeven.ReservoirSizeBridge

/-!
# The complete square-free reservoir at the manuscript scale

This file assembles the separately proved prime-supply, crossing, size,
certificate-deletion, connectivity, and graph-cardinality statements.  The
main theorem returns literal finite sets of primes and literal fixed-cardinality
subsets; it does not package any geometric or analytic conclusion in a record.

The deliberately generous coefficients below remove all hidden choices from
the proof.  If the certificate exponent is `A` and the target exponent is
`a`, then

* `4*A+4` pays for each certificate;
* `a+2` pays for the crossing cardinality;
* `8*A+a+11` pays for the crossing and two certificates, including ceilings;
* eight times the last coefficient is the fixed multiplier in the interval
  of comparable primes.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

def manuscriptCertificateDepthCoefficient (A : ℝ) : ℝ := 4 * A + 4

def manuscriptCrossingDepthCoefficient (a : ℝ) : ℝ := a + 2

def manuscriptPoolDepthCoefficient (A a : ℝ) : ℝ := 8 * A + a + 11

def manuscriptPrimeIntervalCoefficient (A a : ℝ) : ℝ :=
  8 * manuscriptPoolDepthCoefficient A a

/-- The canonical comparable-prime pool.  The fallback branch makes the
definition total; the prime number theorem proves that it is never used once
`H` is sufficiently large.  In particular this choice does not depend on the
epsilon used later to state subpower estimates. -/
def manuscriptPrimePoolAt (A a H : ℝ) : Finset ℕ :=
  let M := reservoirDepth (manuscriptPoolDepthCoefficient A a) H
  let C := manuscriptPrimeIntervalCoefficient A a
  if h : M ≤ (comparablePrimeCandidates (C * Real.log H)).card then
    comparablePrimePool (C * Real.log H) M h
  else ∅

/-- The canonical crossing cardinality.  As above, the fallback branch is
eventually absent and only makes the definition total. -/
def manuscriptCrossingAt (A a Cres H T : ℝ) : ℕ :=
  let C := manuscriptPrimeIntervalCoefficient A a
  if h : 1 ≤ C * Real.log H then
    manuscriptReservoirCrossing C Cres H T a h
  else 0

/-- All three clauses of the manuscript's square-free reservoir lemma, with
explicit constants and quantifiers.  The vertices are the literal
`k`-element subsets of `P`, and their modulus is `primeProduct`.  Consequently
the final two clauses state nonemptiness and connectivity of exactly the
subfamilies whose moduli are coprime to one or two integer certificates. -/
theorem eventually_exists_manuscriptReservoir
    {A a Cres ε : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ H →
      ∃ (P : Finset ℕ) (k : ℕ),
        P = manuscriptPrimePoolAt A a H ∧
        k = manuscriptCrossingAt A a Cres H T ∧
        P.card = reservoirDepth (manuscriptPoolDepthCoefficient A a) H ∧
        (∀ p ∈ P,
          p.Prime ∧
            ⌊manuscriptPrimeIntervalCoefficient A a * Real.log H⌋₊ < p ∧
            p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a *
              Real.log H)⌋₊) ∧
        k ≤ P.card ∧
        (∀ s ∈ P.powersetCard k,
          Squarefree (primeProduct s) ∧
            Cres * T ^ a ≤ (primeProduct s : ℝ) ∧
            (primeProduct s : ℝ) ≤
              (4 * manuscriptPrimeIntervalCoefficient A a * (ε / 3)⁻¹) *
                Cres * T ^ a * H ^ ε) ∧
        (((P.powersetCard k).card +
            (reservoirDirectedEdges P k).card : ℕ) : ℝ) ≤ 2 * H ^ ε ∧
        (∀ s ∈ P.powersetCard k, ∀ t ∈ P.powersetCard k,
          OneExchange s t →
            Cres * T ^ a ≤
              (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ∧
            (Nat.lcm (primeProduct s) (primeProduct t) : ℝ) ≤
              (16 * (manuscriptPrimeIntervalCoefficient A a) ^ 2 *
                ((ε / 3)⁻¹) ^ 2) * Cres * T ^ a * H ^ ε) ∧
        (∀ D : ℤ, D ≠ 0 → (D.natAbs : ℝ) ≤ H ^ A →
          (∀ s : Finset ℕ, s ⊆ P →
            (s ⊆ certificateAllowedPrimes P D ↔
              Nat.Coprime (primeProduct s) D.natAbs)) ∧
          Nonempty (ReservoirVertex (certificateAllowedPrimes P D) k) ∧
          (reservoirGraph (certificateAllowedPrimes P D) k).Connected) ∧
        (∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
          (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
          (∀ s : Finset ℕ, s ⊆ P →
            (s ⊆ certificateAllowedPrimesTwo P D₁ D₂ ↔
              Nat.Coprime (primeProduct s) D₁.natAbs ∧
                Nat.Coprime (primeProduct s) D₂.natAbs)) ∧
          Nonempty (ReservoirVertex
            (certificateAllowedPrimesTwo P D₁ D₂) k) ∧
          (reservoirGraph
            (certificateAllowedPrimesTwo P D₁ D₂) k).Connected) := by
  let Bcert := manuscriptCertificateDepthCoefficient A
  let Bcross := manuscriptCrossingDepthCoefficient a
  let M0 := manuscriptPoolDepthCoefficient A a
  let C := manuscriptPrimeIntervalCoefficient A a
  have hBcert : 0 ≤ Bcert := by
    dsimp [Bcert, manuscriptCertificateDepthCoefficient]
    linarith
  have hBcross : 0 ≤ Bcross := by
    dsimp [Bcross, manuscriptCrossingDepthCoefficient]
    linarith
  have hM0 : 0 ≤ M0 := by
    dsimp [M0, manuscriptPoolDepthCoefficient]
    linarith
  have hC : 1 ≤ C := by
    dsimp [C, manuscriptPrimeIntervalCoefficient,
      manuscriptPoolDepthCoefficient]
    linarith
  have hPntRoom : 8 * M0 ≤ C := by
    dsimp [C, M0, manuscriptPrimeIntervalCoefficient]
    rfl
  have hCertSafe : 4 * A + 4 ≤ Bcert := by
    dsimp [Bcert, manuscriptCertificateDepthCoefficient]
    rfl
  have hCrossGap : a + 1 < Bcross := by
    dsimp [Bcross, manuscriptCrossingDepthCoefficient]
    linarith
  have hDepthRoom : Bcross + 2 * Bcert < M0 := by
    dsimp [Bcross, Bcert, M0, manuscriptCrossingDepthCoefficient,
      manuscriptCertificateDepthCoefficient, manuscriptPoolDepthCoefficient]
    linarith
  have hsupply := eventually_manuscriptPrimeScale_le_candidateCard
    hC hM0 hPntRoom
  have hcross := eventually_manuscriptReservoirCrossing_le_reservoirDepth
    hC hCres ha.le hCrossGap
  have hroom := eventually_reservoirDepth_add_two_mul_le
    hBcross hBcert hDepthRoom
  have hscale := eventually_manuscriptReservoir_scale_and_threshold
    (M0 := M0) (ε := ε) hC
  have hgraphThreshold :
      ∀ᶠ H : ℝ in atTop,
        reservoirSubpowerThreshold M0 4 ε ≤ H :=
    eventually_ge_atTop _
  have hbadOne := eventually_card_comparableIntegerBadPrimes_lt_depth
    hA hCertSafe hC
  have hbadTwo := eventually_card_comparableIntegerBadPrimesTwo_lt_two_depth
    hA hCertSafe hC
  filter_upwards [hsupply, hcross, hroom, hscale, hgraphThreshold,
    hbadOne, hbadTwo] with H hSupplyH hCrossH hRoomH hScaleH
      hGraphH hBadOneH hBadTwoH
  intro T hT hTH
  let M := reservoirDepth M0 H
  have hPoolRoom : M ≤ (comparablePrimeCandidates (C * Real.log H)).card := by
    change ⌈M0 * Real.log H / Real.log (Real.log H)⌉₊ ≤
      (comparablePrimeCandidates (C * Real.log H)).card
    simpa only [div_eq_mul_inv, mul_assoc] using hSupplyH
  let P := comparablePrimePool (C * Real.log H) M hPoolRoom
  have hPcard : P.card = reservoirDepth M0 H := by
    simpa only [P, M] using
      card_comparablePrimePool (C * Real.log H) M hPoolRoom
  have hPprime : ∀ p ∈ P,
      p.Prime ∧ ⌊C * Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (C * Real.log H)⌋₊ := by
    intro p hp
    exact prime_and_bounds_of_mem_comparablePrimePool (by simpa only [P] using hp)
  have hscaleLower : 1 ≤ C * Real.log H := hScaleH.1
  have htargetThreshold :
      reservoirSubpowerThreshold M0 2 (ε / 3) ≤ H := hScaleH.2
  let k := manuscriptReservoirCrossing C Cres H T a hscaleLower
  have hkCross : k ≤ reservoirDepth Bcross H := by
    simpa only [k] using hCrossH T hT hTH hscaleLower
  have hkRoom : k + 2 * reservoirDepth Bcert H ≤ M := by
    dsimp only [M]
    exact (Nat.add_le_add_right hkCross _).trans hRoomH
  have hkM : k ≤ M := by omega
  have hkDepthM :
      manuscriptReservoirCrossing C Cres H T a hscaleLower ≤
        reservoirDepth M0 H := by
    simpa only [k, M] using hkM
  have hkP : k ≤ P.card := by simpa only [hPcard] using hkM
  have hCanonicalPoolRoom :
      reservoirDepth (manuscriptPoolDepthCoefficient A a) H ≤
        (comparablePrimeCandidates
          (manuscriptPrimeIntervalCoefficient A a * Real.log H)).card := by
    simpa only [M0, C] using hPoolRoom
  have hPcanonical : P = manuscriptPrimePoolAt A a H := by
    simp only [manuscriptPrimePoolAt, hCanonicalPoolRoom, ↓reduceDIte,
      P, M, C, M0]
  have hkcanonical : k = manuscriptCrossingAt A a Cres H T := by
    simp [manuscriptCrossingAt, k, C, hscaleLower]
  refine ⟨P, k, hPcanonical, hkcanonical, hPcard, ?_, hkP,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [C, manuscriptPrimeIntervalCoefficient] using hPprime
  · intro s hs
    have hs' := Finset.mem_powersetCard.mp hs
    have hsP : s ⊆ comparablePrimePool (C * Real.log H) M hPoolRoom := by
      simpa only [P] using hs'.1
    have hsquare : Squarefree (primeProduct s) :=
      comparable_primeProduct_squarefree hsP
    have hbounds := manuscript_crossing_primeProduct_le_rpow
      hC hscaleLower hCres hT hTH ha.le hM0 hε htargetThreshold
      (s := s)
      (fun p hp ↦ (hPprime p (hs'.1 hp)).2)
      (by simpa only [k] using hs'.2) hkDepthM
    exact ⟨hsquare, hbounds.1, by
      simpa only [C, manuscriptPrimeIntervalCoefficient] using hbounds.2⟩
  · exact reservoirGraph_size_cast_le_two_mul_rpow hPcard hM0 hε hGraphH
  · intro s hs t ht hex
    have hs' := Finset.mem_powersetCard.mp hs
    have ht' := Finset.mem_powersetCard.mp ht
    have hprimeInterval : ∀ p ∈ s ∪ t,
        p.Prime ∧ ⌊C * Real.log H⌋₊ < p ∧
          p ≤ ⌊2 * (C * Real.log H)⌋₊ := by
      intro p hp
      exact hPprime p (Finset.union_subset hs'.1 ht'.1 hp)
    have hbounds := manuscript_crossing_oneExchange_lcm_le_rpow
      hC hscaleLower hCres hT hTH ha.le hM0 hε htargetThreshold
      hprimeInterval (by simpa only [k] using hs'.2) hkDepthM hex
    exact ⟨hbounds.1, by
      simpa only [C, manuscriptPrimeIntervalCoefficient] using hbounds.2⟩
  · intro D hD hDsize
    let bad := comparableIntegerBadPrimes (C * Real.log H) M hPoolRoom D
    have hbadCard : bad.card < reservoirDepth Bcert H := by
      simpa only [bad, M] using hBadOneH M hPoolRoom D hD hDsize
    have hsurviveRoom : bad.card + k ≤ M := by omega
    have hallowed : certificateAllowedPrimes P D =
        comparablePrimePool (C * Real.log H) M hPoolRoom \ bad := by
      ext p
      by_cases hp : p ∈ comparablePrimePool
          (C * Real.log H) M hPoolRoom <;>
        simp [certificateAllowedPrimes, comparableIntegerBadPrimes, bad, P, hp]
    have hlower := card_allowed_comparablePrimePool_ge hPoolRoom bad
    have hkAllowed : k ≤ (certificateAllowedPrimes P D).card := by
      rw [hallowed]
      omega
    have hconnected := reservoirGraph_connected hkAllowed
    refine ⟨?_, hconnected.nonempty, hconnected⟩
    intro s hs
    exact subset_certificateAllowedPrimes_iff_coprime
      (fun p hp ↦ (hPprime p hp).1) hs D
  · intro D₁ D₂ hD₁ hD₂ hDsize₁ hDsize₂
    let bad := comparableIntegerBadPrimesTwo
      (C * Real.log H) M hPoolRoom D₁ D₂
    have hbadCard : bad.card <
        reservoirDepth Bcert H + reservoirDepth Bcert H := by
      simpa only [bad, M] using
        hBadTwoH M hPoolRoom D₁ D₂ hD₁ hD₂ hDsize₁ hDsize₂
    have hsurviveRoom : bad.card + k ≤ M := by omega
    have hallowed : certificateAllowedPrimesTwo P D₁ D₂ =
        comparablePrimePool (C * Real.log H) M hPoolRoom \ bad := by
      ext p
      by_cases hp : p ∈ comparablePrimePool
          (C * Real.log H) M hPoolRoom <;>
        simp [certificateAllowedPrimesTwo, comparableIntegerBadPrimesTwo,
          comparableIntegerBadPrimes, bad, P, hp]
    have hlower := card_allowed_comparablePrimePool_ge hPoolRoom bad
    have hkAllowed : k ≤
        (certificateAllowedPrimesTwo P D₁ D₂).card := by
      rw [hallowed]
      omega
    have hconnected := reservoirGraph_connected hkAllowed
    refine ⟨?_, hconnected.nonempty, hconnected⟩
    intro s hs
    exact subset_certificateAllowedPrimesTwo_iff_coprime
      (fun p hp ↦ (hPprime p hp).1) hs D₁ D₂

end

end TranslatedDepthSeven
