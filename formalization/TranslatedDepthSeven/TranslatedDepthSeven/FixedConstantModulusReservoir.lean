import TranslatedDepthSeven.ManuscriptModulusReservoir
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A square-free reservoir with fixed numerical multipliers

The canonical prime pool and crossing cardinality do not depend on epsilon.
This version also fixes the multipliers in the modulus and adjacent-lcm
upper bounds before epsilon.  Only the eventual height threshold changes.
It is useful when a subsequent exceptional-height cutoff is selected from
these multipliers before epsilon is given.

The existing reservoir theorem is applied at half the requested exponent.
Its two numerical constants are then absorbed by the other half.  Two
crossing depths fit into the displayed enlarged logarithmic depth, so the
same statement supplies the local-factor threshold used for both nodes and
edges.  No new prime-supply or counting assumption is made.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 4000000

/-- All reservoir multipliers and the certificate exponent are fixed
before epsilon.  The exact connected coprime subfamilies are retained. -/
theorem eventually_exists_fixedConstant_modulusReservoir
    {A a Cres : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (b : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ H →
      ∃ (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime),
        P = manuscriptPrimePoolAt A a H ∧
        k = manuscriptCrossingAt A a Cres H T ∧
        P.card = reservoirDepth (manuscriptPoolDepthCoefficient A a) H ∧
        (∀ p ∈ P,
          ⌊manuscriptPrimeIntervalCoefficient A a * Real.log H⌋₊ < p ∧
          p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a * Real.log H)⌋₊) ∧
        k ≤ P.card ∧
        2 * k ≤ reservoirDepth (2 * manuscriptPoolDepthCoefficient A a + 1) H ∧
        reservoirSubpowerThreshold
            (2 * manuscriptPoolDepthCoefficient A a + 1) b ε ≤ H ∧
        (∀ q : ReservoirModulus P k,
          Squarefree q.1 ∧
          manuscriptReservoirTarget Cres T a ≤ q.1 ∧
          (q.1 : ℝ) ≤ Cres * T ^ a * H ^ ε) ∧
        (modulusReservoirGraph P k hP).Connected ∧
        ((((modulusReservoir P k).card +
            (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
          2 * H ^ ε) ∧
        (∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hP).Adj q r →
          manuscriptReservoirTarget Cres T a ≤ Nat.lcm q.1 r.1 ∧
          (Nat.lcm q.1 r.1 : ℝ) ≤ Cres * T ^ a * H ^ ε) ∧
        (∀ D : ℤ, D ≠ 0 → (D.natAbs : ℝ) ≤ H ^ A →
          (∀ q : ℕ,
            q ∈ modulusReservoir (certificateAllowedPrimes P D) k ↔
              q ∈ modulusReservoir P k ∧ Nat.Coprime q D.natAbs) ∧
          Nonempty (ReservoirModulus (certificateAllowedPrimes P D) k) ∧
          (modulusReservoirGraph (certificateAllowedPrimes P D) k
            (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) ∧
        (∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
          (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
          (∀ q : ℕ,
            q ∈ modulusReservoir (certificateAllowedPrimesTwo P D₁ D₂) k ↔
              q ∈ modulusReservoir P k ∧ Nat.Coprime q (D₁ * D₂).natAbs) ∧
          Nonempty (ReservoirModulus (certificateAllowedPrimesTwo P D₁ D₂) k) ∧
          (modulusReservoirGraph (certificateAllowedPrimesTwo P D₁ D₂) k
            (fun p hp ↦ hP p (Finset.mem_filter.mp hp).1)).Connected) := by
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  let M : ℝ := manuscriptPoolDepthCoefficient A a
  have hM : 0 ≤ M := by
    dsimp only [M, manuscriptPoolDepthCoefficient]
    linarith
  let C₁ : ℝ := 4 * manuscriptPrimeIntervalCoefficient A a * (η / 3)⁻¹
  let C₂ : ℝ :=
    16 * (manuscriptPrimeIntervalCoefficient A a) ^ 2 * ((η / 3)⁻¹) ^ 2
  have hdepth := eventually_reservoirDepth_add_le
    (b₁ := M) (b₂ := M) (M₀ := 2 * M + 1) hM hM (by linarith)
  filter_upwards [eventually_exists_manuscriptModulusReservoir
      hA ha haOne hCres hη,
    hdepth,
    (tendsto_rpow_atTop hη).eventually_ge_atTop C₁,
    (tendsto_rpow_atTop hη).eventually_ge_atTop C₂,
    eventually_ge_atTop (reservoirSubpowerThreshold (2 * M + 1) b ε)]
    with H hreservoir hdepthH hC₁ hC₂ hthreshold
  intro T hT hTH
  have hHone : 1 ≤ H := hT.trans hTH
  have hHpos : 0 < H := zero_lt_one.trans_le hHone
  have hηε : η + η = ε := by dsimp only [η]; ring
  have habsorb (C : ℝ) (hC : C ≤ H ^ η) :
      C * Cres * T ^ a * H ^ η ≤ Cres * T ^ a * H ^ ε := by
    calc
      C * Cres * T ^ a * H ^ η = Cres * T ^ a * (C * H ^ η) := by ring
      _ ≤ Cres * T ^ a * (H ^ η * H ^ η) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hHpos.le _)
        · exact mul_nonneg (le_of_lt (zero_lt_one.trans hCres))
            (Real.rpow_nonneg (zero_le_one.trans hT) _)
      _ = Cres * T ^ a * H ^ ε := by rw [← Real.rpow_add hHpos, hηε]
  obtain ⟨P, k, hP, hPcanonical, hkcanonical, hPcard, hPinterval,
      hkP, hmoduli, hconnected, hfamily, hlcm, hcertOne, hcertTwo⟩ :=
    hreservoir T hT hTH
  have hkDepth : 2 * k ≤ reservoirDepth (2 * M + 1) H := by
    have hk : k ≤ reservoirDepth M H := by simpa only [M, ← hPcard] using hkP
    omega
  refine ⟨P, k, hP, hPcanonical, hkcanonical, hPcard, hPinterval,
    hkP, hkDepth, hthreshold, ?_, hconnected, ?_, ?_, hcertOne, hcertTwo⟩
  · intro q
    refine ⟨(hmoduli q).1, ?_, ?_⟩
    · exact Nat.ceil_le.mpr (hmoduli q).2.1
    · exact (hmoduli q).2.2.trans (habsorb C₁ hC₁)
  · apply hfamily.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    exact Real.rpow_le_rpow_of_exponent_le hHone (by dsimp only [η]; linarith)
  · intro q r hqr
    exact ⟨Nat.ceil_le.mpr (hlcm q r hqr).1,
      (hlcm q r hqr).2.trans (habsorb C₂ hC₂)⟩

end

end TranslatedDepthSeven
