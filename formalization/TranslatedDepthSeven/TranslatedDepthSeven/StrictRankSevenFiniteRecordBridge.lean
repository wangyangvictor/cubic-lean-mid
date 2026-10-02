import TranslatedDepthSeven.RankSevenSurvivingRecordCover
import TranslatedDepthSeven.StrictChartReservoirBridge

/-!
# The strict rank-seven chart reduced to finite records

The manuscript reservoir is inserted into the literal finite-record
partition.  Both certificate-size conditions, the connectedness after their
deletion, the modulus scale `T^(5/7)`, and the number of reservoir vertices
and directed edges are retained explicitly.  The conclusion is still an
identity-level reduction: it assumes no estimate for any node, edge, or
persistent-surface cell.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter MvPolynomial Published
open scoped Topology

local instance strictRankSevenFiniteRecordPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 4000000

/-- For all sufficiently large strict heights, every rank-seven chart has
the canonical `T^(5/7)` reservoir and the exact finite node/edge/persistent
record inequality. -/
theorem eventually_exists_strict_rankSevenChart_finiteRecordPartition
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    {ε : ℝ} (hε : 0 < ε)
    (A : ℝ)
    (hA : (strictChartCertificateExponent
      equations model.denominator : ℝ) ≤ A) :
    ∀ᶠ H : ℝ in atTop,
      ∀ (p : Parameters), p.H = H →
      ∀ (x₀ : IntVector 13) (CF : ℕ)
        (C : IntegralDepthSevenJacobianChartIndex equations),
      ∃ (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime),
      ∃ hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1,
        P = manuscriptPrimePoolAt
          A (5 / 7) H ∧
        k = manuscriptCrossingAt
          A (5 / 7) normalizedSurfaceReservoirConstant H p.T ∧
        P.card = reservoirDepth
          (manuscriptPoolDepthCoefficient A (5 / 7)) H ∧
        k ≤ P.card ∧
        ((((modulusReservoir P k).card +
            (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
          2 * H ^ ε) ∧
        (∀ q : ReservoirModulus P k,
          Squarefree q.1 ∧
          normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤ q.1 ∧
          (q.1 : ℝ) ≤
            (4 * manuscriptPrimeIntervalCoefficient
              A (5 / 7) * (ε / 3)⁻¹) *
              normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) *
                H ^ ε) ∧
        (∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hP).Adj q r →
            normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) ≤
                (Nat.lcm q.1 r.1 : ℝ) ∧
            (Nat.lcm q.1 r.1 : ℝ) ≤
              (16 * (manuscriptPrimeIntervalCoefficient
                A (5 / 7)) ^ 2 *
                  ((ε / 3)⁻¹) ^ 2) *
                normalizedSurfaceReservoirConstant * p.T ^ (5 / 7 : ℝ) *
                  H ^ ε) ∧
        (depthSevenNormalizedJacobianChartCell p x₀ equations CF C).card ≤
          (∑ q : ReservoirModulus P k,
            ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
                p x₀ equations CF C model.denominator P k hP hlower q,
              (rankSevenSurvivingNonSurfaceNodeRecordPointCell
                p x₀ equations CF C model.denominator P k hP hlower
                  q record).card) +
          (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
            ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF C model.denominator P k hP hlower q r,
              ∑ L ∈ finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent),
                (rankSevenSurfaceEdgeFrontierPointCell
                  p x₀ equations CF C P k record L).card) +
          (∑ o ∈ occurringRankSevenStaticSurfaceLabels
              p x₀ equations CF C model.denominator P k hP
                hlower,
            ((depthSevenNormalizedJacobianChartCell
              p x₀ equations CF C).filter fun z ↦
                o ≠ none ∧ ∀ q : ReservoirModulus P k,
                  survivesTwoCertificates q
                    ((p.m : ℤ) * model.denominator)
                    (MvPolynomial.eval (integralAffineMap x₀ z p.m)
                      C.determinant) →
                  rankSevenStaticSurfaceLabel
                    p x₀ equations CF C model.denominator P k hP
                      hlower z q = o).card) := by
  have hAnonneg : 0 ≤ A :=
    (Nat.cast_nonneg
      (strictChartCertificateExponent equations model.denominator)).trans hA
  have ha : (0 : ℝ) < 5 / 7 := by norm_num
  have haOne : (5 / 7 : ℝ) < 1 := by norm_num
  have hCres : (1 : ℝ) < normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant]
  filter_upwards [eventually_exists_manuscriptModulusReservoir
    (A := A) (a := (5 / 7 : ℝ))
      (Cres := normalizedSurfaceReservoirConstant) hAnonneg ha haOne hCres hε]
      with H hreservoir
  intro p hpH x₀ CF C
  have hTH : p.T ≤ H := by
    rw [← hpH]
    exact p.T_le_H
  obtain ⟨P, k, hP, hPcanonical, hkcanonical, hPcard,
      _hPinterval, hkP, hmoduli, _hconnected, hfamily, hlcm,
      _hcertOne, hcertTwo⟩ :=
    hreservoir p.T p.one_le_T hTH
  have hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1 := by
    intro q
    apply Nat.ceil_le.mpr
    exact (hmoduli q).2.1
  refine ⟨P, k, hP, hlower, ?_, ?_, hPcard, hkP,
    hfamily, hmoduli, hlcm, ?_⟩
  · exact hPcanonical
  · exact hkcanonical
  · have hmNe : (p.m : ℤ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (p.one_le_m.trans_lt' Nat.zero_lt_one))
    have hfixedNe : (p.m : ℤ) * model.denominator ≠ 0 :=
      mul_ne_zero hmNe model.denominator_ne_zero
    have hHone : 1 ≤ H := p.one_le_T.trans hTH
    have hfixedBase :
        ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤
          H ^ (strictChartCertificateExponent
            equations model.denominator : ℝ) := by
      simpa only [← hpH, Real.rpow_natCast] using
        scale_mul_denominator_natAbs_le_heightPower
          p equations model.denominator
    have hfixedSize :
        ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤ H ^ A := by
      exact hfixedBase.trans
        (Real.rpow_le_rpow_of_exponent_le hHone hA)
    have hdetNe : ∀ z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C,
        MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant ≠ 0 := by
      intro z hz
      exact eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
        p x₀ equations CF C hz
    have hdetSize : ∀ z ∈ depthSevenNormalizedJacobianChartCell
        p x₀ equations CF C,
        (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A := by
      intro z hz
      have hdetBase :
          (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant).natAbs : ℕ) : ℝ) ≤
            H ^ (strictChartCertificateExponent
              equations model.denominator : ℝ) := by
        simpa only [← hpH, Real.rpow_natCast] using
          chartDeterminant_natAbs_le_heightPower
            p x₀ equations CF C model.denominator hz
      exact hdetBase.trans
        (Real.rpow_le_rpow_of_exponent_le hHone hA)
    have hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
        (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
        Nonempty (ReservoirModulus
          (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
        (modulusReservoirGraph
          (certificateAllowedPrimesTwo P E₁ E₂) k
          (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected := by
      intro E₁ E₂ hE₁ hE₂ hE₁size hE₂size
      exact (hcertTwo E₁ E₂ hE₁ hE₂ hE₁size hE₂size).2
    exact card_rankSevenChart_le_survivingNodeRecords_edgeFrontiers_persistent
      p x₀ equations CF hhomogeneous C model.denominator P k hP hlower
        H A hsurvival hfixedNe hfixedSize hdetNe hdetSize

end

end TranslatedDepthSeven
