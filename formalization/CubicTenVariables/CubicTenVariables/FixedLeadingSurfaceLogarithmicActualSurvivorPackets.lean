import CubicTenVariables.FixedLeadingSurfacePrimeReservoir
import CubicTenVariables.FixedLeadingSurfaceLogarithmicSurvivorAuxiliaryChoice
import CubicTenVariables.FixedLeadingSurfaceGeometricPrime
import CubicTenVariables.FixedLeadingSurfaceLogarithmicNumerics
import TranslatedDepthSeven.QuantitativePrefixTerminalReservoirScale

/-!
# Actual survivor packets with logarithmic terminal degree

This is the logarithmic-degree sibling of
`FixedLeadingSurfaceActualSurvivorPackets`.  It records both the sharp
logarithmic degree and a coarser power majorant, allowing the existing
changed-edge estimates to be reused unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicActualSurvivorPackets

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedPrimeCount FixedPolynomialSubstitutionHeight
open FixedLeadingSurfacePrimeReservoir
open FixedLeadingSurfaceLogarithmicNumerics

def ordinaryPrimePool (d e : ℕ) (alpha : ℝ) (H : ℕ) : Finset ℕ :=
  certificateAllowedPrimes
    (manuscriptPrimePoolAt (e + 1 + d + 2 : ℕ) alpha H) (1 : ℤ)

def ordinaryDepth (d e : ℕ) (alpha : ℝ) (H : ℕ) : ℕ :=
  manuscriptCrossingAt (e + 1 + d + 2 : ℕ) alpha 2 H H

theorem ordinaryPoint_eq (z : Fin 3 → ℤ) :
    progressionHomogeneousPoint 0 1 z = Fin.cases 1 z := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [progressionHomogeneousPoint]

/-- The actual normalized packet family with sharp logarithmic degrees.
The root and terminal caps include the fixed homogenizing offset `d-1`.
The coarse `H^eta` bound is emitted simultaneously for existing edge
estimates. -/
theorem exists_normalized_logarithmic_actual_survivor_packets
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d e : ℕ} (hd : 2 ≤ d)
    (k₀ : MvPolynomial (Fin 3) ℤ) (hk₀ : k₀.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k₀))
    (K eta alpha delta : ℝ) (hK : 1 < K) (heta : 0 < eta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (hdelta : 0 < delta)
    (halpha : Real.sqrt K / Real.sqrt (d : ℝ) < alpha) :
    ∃ (a b : ℤ) (L : ℝ) (H₀ : ℕ),
      (coordinateMatrix a b).det = 1 ∧ 1 ≤ L ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H →
      let P := ordinaryPrimePool d e alpha H
      let depth := ordinaryDepth d e alpha H
      (∀ p ∈ P, p.Prime) ∧ (∀ p ∈ P, ¬ p ∣ 1) ∧
      depth ≤ P.card ∧
      P.card ≤ reservoirDepth
        (manuscriptPoolDepthCoefficient (e + 1 + d + 2 : ℕ) alpha) H ∧
      (∀ p ∈ P,
        ⌊manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) alpha *
          Real.log H⌋₊ < p ∧
        p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient
          (e + 1 + d + 2 : ℕ) alpha * Real.log H)⌋₊) ∧
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        PrimeSubsetPrefix.modulus v ≤ H ^ prefixHeightExponent d (e + 1) alpha) ∧
      (∀ q ∈ modulusReservoir P depth,
        Squarefree q ∧ 2 * (H : ℝ) ^ alpha ≤ (q : ℝ) ∧
        (q : ℝ) ≤
          (4 * manuscriptPrimeIntervalCoefficient (e + 1 + d + 2 : ℕ) alpha *
            (delta / 3)⁻¹) * 2 * (H : ℝ) ^ alpha * H ^ delta) ∧
      ∃ blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ,
        (∀ v, 0 < blockDegree v ∧
          (blockDegree v : ℝ) ≤ 2 * L * Real.log (H : ℝ) *
            (1 + (H : ℝ) ^ alpha /
              (PrimeSubsetPrefix.modulus v : ℝ)) ∧
          (blockDegree v : ℝ) ≤ 2 * (H : ℝ) ^ eta *
            (1 + (H : ℝ) ^ alpha /
              (PrimeSubsetPrefix.modulus v : ℝ))) ∧
        d - 1 + blockDegree (PrimeSubsetPrefix.root P depth) ≤
          d - 1 + ⌈4 * L * Real.log (H : ℝ) *
            (1 + (H : ℝ) ^ alpha)⌉₊ ∧
        (∀ v : PrimeSubsetPrefix.Vertex P depth, v.1.card = depth →
          d - 1 + blockDegree v ≤
            d - 1 + ⌈4 * L * Real.log (H : ℝ)⌉₊) ∧
        ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
          g.totalDegree ≤ d →
          map (Int.castRingHom ℚ) (homogeneousComponent d g) =
            C c * map (Int.castRingHom ℚ) k₀ →
          mvPolynomialCoefficientNatAbsMax g ≤ H ^ e →
          let F := projectiveEquiv a b (homogenize d g)
          let allowed := smoothAllowedPrimes P F
          ∀ X : Finset (Fin 3 → ℤ),
          (∀ z ∈ X, ∀ i, (z i).natAbs ≤ H) →
          (∀ z ∈ X, eval z
            (surfaceHypersurfaceFirstChartDehomogenize F) = 0) →
          (∀ z ∈ X, ∃ i, eval z
            (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
          (∀ z ∈ X, depth ≤ (allowed z).card) ∧
          ∃ auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
            (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
              MvPolynomial (Fin 4) ℚ,
            ∀ z ∈ X, ∀ v ∈
              PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
              (auxiliary v (integralResidueVector z)).IsHomogeneous
                (d - 1 + blockDegree v) ∧
              auxiliary v (integralResidueVector z) ∉
                Ideal.span {map (Int.castRingHom ℚ) F} ∧
              eval (fun i => (progressionHomogeneousPoint 0 1 z i : ℚ))
                (auxiliary v (integralResidueVector z)) = 0 := by
  classical
  let A := prefixHeightExponent d (e + 1) alpha
  obtain ⟨a, b, L, Haux, hdet, hL, hHaux, haux⟩ :=
    CubicTenVariables.FixedLeadingSurfaceLogarithmicSurvivorAuxiliaryChoice.exists_uniform_logarithmic_prefix_auxiliaries
        (e := e) integralityOpen curveWeil hd k₀ hk₀ hirr K hK A alpha halpha
  obtain ⟨Hpow, hHpow, hpower⟩ :=
    exists_logarithmicFactor_le_power L eta (by linarith) heta
  obtain ⟨Hres, hHres, hres⟩ := exists_uniform_actual_smooth_prime_reservoir
    d (e + 1) alpha 2 delta halpha0 halpha1 (by norm_num) hdelta
  let Cnorm := substitutionHeightConstant (coordinateEquiv a b).toAlgHom d
  let H₀ := max Haux (max Hpow (max Hres Cnorm))
  refine ⟨a, b, L, H₀, hdet, hL,
    hHaux.trans (Nat.le_max_left _ _), ?_⟩
  intro H hH
  have hHa : Haux ≤ H := (Nat.le_max_left _ _).trans hH
  have hHp : Hpow ≤ H :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hH)
  have hHr : Hres ≤ H :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hH))
  have hHc : Cnorm ≤ H :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hH))
  have hHone : 1 ≤ H := by omega
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hHone
  have hLnonneg : 0 ≤ L := by linarith
  have hLHpower : L * Real.log (H : ℝ) ≤ (H : ℝ) ^ eta := hpower H hHp
  obtain ⟨hP, hPm, hdepth, hcard, hinterval, hmoduli, hterminal, hroom⟩ :=
    hres H hHr H hHreal le_rfl 1 (by decide) hHone
  let P := ordinaryPrimePool d e alpha H
  let depth := ordinaryDepth d e alpha H
  have hP' : ∀ p ∈ P, p.Prime := hP
  have hPm' : ∀ p ∈ P, ¬ p ∣ 1 := hPm
  have hmoduli' : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      1 * PrimeSubsetPrefix.modulus v ≤ H ^ A := hmoduli
  obtain ⟨blockDegree, hblock, hfamily⟩ :=
    haux P depth H H 1 hP' hPm' hHa hHone (by decide) hmoduli'
  have hqpos (v : PrimeSubsetPrefix.Vertex P depth) :
      0 < PrimeSubsetPrefix.modulus v := by
    apply Nat.pos_of_ne_zero
    apply primeProduct_ne_zero
    intro p hp
    exact hP p ((PrimeSubsetPrefix.mem_vertices.mp v.2).1 hp)
  have hcoarse : ∀ v, (blockDegree v : ℝ) ≤
      2 * (H : ℝ) ^ eta *
        (1 + (H : ℝ) ^ alpha /
          (PrimeSubsetPrefix.modulus v : ℝ)) := by
    intro v
    exact logarithmic_block_bound_le_power hLHpower hHone (hqpos v) (hblock v).2
  have hroot : d - 1 + blockDegree (PrimeSubsetPrefix.root P depth) ≤
      d - 1 + ⌈4 * L * Real.log (H : ℝ) *
        (1 + (H : ℝ) ^ alpha)⌉₊ :=
    logarithmic_root_degree_cap hLnonneg hHone blockDegree (fun v => (hblock v).2)
  have hterminalCap : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      v.1.card = depth → d - 1 + blockDegree v ≤
        d - 1 + ⌈4 * L * Real.log (H : ℝ)⌉₊ := by
    intro v hv
    have ht := hterminal (PrimeSubsetPrefix.modulus v)
      (terminalPrefix_modulus_mem_modulusReservoir v hv)
    exact logarithmic_terminal_degree_cap hLnonneg hHone hP' blockDegree
      (fun w => (hblock w).2) v (by linarith [ht.2.1])
  refine ⟨hP, hPm, hdepth, hcard, hinterval, ?_, hterminal,
    blockDegree, ?_, hroot, hterminalCap, ?_⟩
  · simpa only [one_mul] using hmoduli
  · intro v
    exact ⟨(hblock v).1, (hblock v).2, hcoarse v⟩
  · intro g c hc hdegree htop hheight
    dsimp only
    let F := projectiveEquiv a b (homogenize d g)
    let allowed := smoothAllowedPrimes P F
    intro X hbox hzero hgrad
    have hchartDegree :
        (surfaceHypersurfaceFirstChartDehomogenize F).totalDegree ≤ d := by
      rw [firstChart_transformed_homogenize a b g hdegree]
      exact (totalDegree_integral_coordinateEquiv_le a b g).trans hdegree
    have hchartHeight : mvPolynomialCoefficientNatAbsMax
        (surfaceHypersurfaceFirstChartDehomogenize F) ≤ H ^ (e + 1) := by
      rw [firstChart_transformed_homogenize a b g hdegree]
      exact height_substitution_le_power (coordinateEquiv a b).toAlgHom d g
        hdegree hHc hheight
    refine ⟨fun z hz => hroom F hchartDegree hchartHeight z
      (hbox z hz) (hgrad z hz), ?_⟩
    apply hfamily g c hc hdegree htop hheight 0 X allowed
    · intro z hz i
      rw [ordinaryPoint_eq]
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hHone
      · exact hbox z hz j
    · exact hbox
    · intro z hz
      rw [ordinaryPoint_eq, ← eval_standardDehomogenizationHom]
      exact hzero z hz
    · intro z hz
      simpa only [Pi.zero_apply, Nat.cast_one, one_mul, zero_add] using hgrad z hz
    · intro z hz p hp
      simpa only [Pi.zero_apply, Nat.cast_one, one_mul, zero_add] using
        ((mem_smoothAllowedPrimes P F z p).mp hp).2

end CubicTenVariables.FixedLeadingSurfaceLogarithmicActualSurvivorPackets
