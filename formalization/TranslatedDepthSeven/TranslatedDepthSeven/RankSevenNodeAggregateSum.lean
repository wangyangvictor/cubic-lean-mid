import TranslatedDepthSeven.RankSevenNodeAggregatePila

/-!
# Summing the nonlinear Pila contribution over all node records

`RankSevenNodeAggregatePila` gives one coefficient-uniform estimate for
every surviving non-surface node record.  `RankSevenRecordOccurrenceScale`
counts the literal record occurrences.  This file combines those two
statements and performs the exact exponent calculation

`T^(30/7) * (T^(2/7))^(1/2+epsilon)
  = T^(31/7+(2/7)epsilon)`.

The points on degree-one curve components remain as a literal finite sum;
they are not included in the nonlinear Pila term.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 4000000

/-- The complete nonlinear contribution of all surviving non-surface node
records has the manuscript exponent `31/7 + (2/7) epsilon`.  The hypotheses
`hcomponentGeometry` and `hnonlinearCount` concern the actual affine ideals
attached to the literal records, while `hrecordComponents` is the independent
degree-mass cardinality bound used in counting record occurrences. -/
theorem exists_uniform_rankSevenSurvivingNonSurfaceNode_sum_constant
    (hPila : Pila1995TheoremA) (Dcurve E : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ {M₀ δ Cres : ℝ},
      0 ≤ M₀ → 0 < δ → 0 ≤ Cres →
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (model : FixedFivefoldResidueModel
          (indexedFinsetFamily (rationalizedEquationFinset equations)))
        (P : Finset ℕ) (k Drecords : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1),
      (∀ (q : ReservoirModulus P k)
          (rho : Fin 13 → ZMod q.1),
        rho ∈ occupiedIntegralResidues q.1
            (depthSevenNormalizedJacobianChartCell
              p x₀ equations CF Cchart) →
        (rankSevenNonSurfaceNodeComponents
          p x₀ equations CF Cchart q.1 rho).card ≤ Drecords) →
      k ≤ reservoirDepth M₀ p.H →
      reservoirSubpowerThreshold M₀
          (model.localConstant : ℝ) δ ≤ p.H →
      ((((modulusReservoir P k).card +
        (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
          2 * p.H ^ δ) →
      (∀ q : ReservoirModulus P k,
        (q.1 : ℝ) ≤ Cres * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) →
      (∀ (q : ReservoirModulus P k)
          (record : RankSevenNonSurfaceNodeRecord q.1),
        record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q →
        ∀ Q ∈ finiteMinimalPrimes
            (realProjectiveAffineChartIdeal record.component),
          ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ Dcurve ∧
            HasAffineHilbertDimensionDegree Q n d) →
      (∀ (q : ReservoirModulus P k)
          (record : RankSevenNonSurfaceNodeRecord q.1),
        record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q →
        (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal record.component)).card ≤ E) →
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q,
          ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart model.denominator P k hP hlower q
              record).card : ℝ)) ≤
        (∑ q : ReservoirModulus P k,
          ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower q,
            ((finitePointsOnLinearCurveComponents
              (realProjectiveAffineChartIdeal record.component)
              (rankSevenNonSurfaceNodeRecordPointCell
                p x₀ equations CF Cchart record)).card : ℝ)) +
        (Cgeom * Cres ^ 6 * Drecords) *
          p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) * p.H ^ (8 * δ) := by
  obtain ⟨C₁, hC₁, hperRecord⟩ :=
    exists_uniform_rankSevenSurvivingNonSurfaceNodeRecord_scale_constant
      hPila Dcurve E ε hε
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro M₀ δ Cres hM₀ hδ hCres p x₀ equations CF Cchart model P k
    Drecords hP hlower hrecordComponents hk hH hfamily hupper
    hcomponentGeometry hnonlinearCount
  let records := fun q : ReservoirModulus P k ↦
    occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower q
  let nonlinearScale : ℝ :=
    C₁ * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε)
  let linearContribution := fun (q : ReservoirModulus P k)
      (record : RankSevenNonSurfaceNodeRecord q.1) ↦
    ((finitePointsOnLinearCurveComponents
      (realProjectiveAffineChartIdeal record.component)
      (rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record)).card : ℝ)
  have hpointwise : ∀ (q : ReservoirModulus P k)
      (record : RankSevenNonSurfaceNodeRecord q.1),
      record ∈ records q →
      ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart model.denominator P k hP hlower q
          record).card : ℝ) ≤
        linearContribution q record + nonlinearScale := by
    intro q record hrecord
    exact hperRecord p x₀ equations CF Cchart model.denominator P k hP
      hlower q record hrecord (hcomponentGeometry q record hrecord)
        (hnonlinearCount q record hrecord)
  have hsumPointwise :
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ records q,
          ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart model.denominator P k hP hlower q
              record).card : ℝ)) ≤
        (∑ q : ReservoirModulus P k,
          ∑ record ∈ records q, linearContribution q record) +
        (∑ q : ReservoirModulus P k, ((records q).card : ℝ)) *
          nonlinearScale := by
    calc
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ records q,
          ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart model.denominator P k hP hlower q
              record).card : ℝ)) ≤
          ∑ q : ReservoirModulus P k,
            ∑ record ∈ records q,
              (linearContribution q record + nonlinearScale) := by
        apply Finset.sum_le_sum
        intro q _hq
        apply Finset.sum_le_sum
        intro record hrecord
        exact hpointwise q record hrecord
      _ = (∑ q : ReservoirModulus P k,
            ∑ record ∈ records q, linearContribution q record) +
          (∑ q : ReservoirModulus P k, ((records q).card : ℝ)) *
            nonlinearScale := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_mul]
  have hrecordMass :=
    sum_occupiedRankSevenSurvivingNonSurfaceNodeRecords_cast_le_scale
      hM₀ hδ hCres p x₀ equations CF Cchart model P k hP hlower
        Drecords hrecordComponents hk hH hfamily hupper
  have hscaleNonneg : 0 ≤ nonlinearScale := by
    dsimp only [nonlinearScale]
    exact mul_nonneg hC₁.le
      (Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _)
  have hmassTimes :
      (∑ q : ReservoirModulus P k, ((records q).card : ℝ)) *
          nonlinearScale ≤
        (2 * Cres ^ 6 * Drecords * p.T ^ (30 / 7 : ℝ) *
          p.H ^ (8 * δ)) * nonlinearScale := by
    exact mul_le_mul_of_nonneg_right hrecordMass hscaleNonneg
  have hTnonneg : 0 ≤ p.T := p.T_pos.le
  have hpower :
      p.T ^ (30 / 7 : ℝ) *
          (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) =
        p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) := by
    rw [← Real.rpow_mul hTnonneg, ← Real.rpow_add p.T_pos]
    congr 1
    ring
  apply hsumPointwise.trans
  calc
    (∑ q : ReservoirModulus P k,
          ∑ record ∈ records q, linearContribution q record) +
        (∑ q : ReservoirModulus P k, ((records q).card : ℝ)) *
          nonlinearScale ≤
        (∑ q : ReservoirModulus P k,
          ∑ record ∈ records q, linearContribution q record) +
        (2 * Cres ^ 6 * Drecords * p.T ^ (30 / 7 : ℝ) *
          p.H ^ (8 * δ)) * nonlinearScale :=
      add_le_add_right hmassTimes _
    _ = (∑ q : ReservoirModulus P k,
          ∑ record ∈ records q, linearContribution q record) +
        ((2 * C₁) * Cres ^ 6 * Drecords) *
          p.T ^ (31 / 7 + (2 / 7) * ε : ℝ) * p.H ^ (8 * δ) := by
      dsimp only [nonlinearScale]
      rw [← hpower]
      ring

end

end TranslatedDepthSeven
