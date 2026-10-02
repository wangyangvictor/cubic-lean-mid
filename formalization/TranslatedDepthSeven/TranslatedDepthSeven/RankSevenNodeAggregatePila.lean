import TranslatedDepthSeven.RankSevenRecordOccurrenceScale
import TranslatedDepthSeven.RankSevenRecordPila

/-!
# Uniform Pila estimate over the rank-seven node records

Pila's constant is coefficient-uniform once the ambient dimension and a
degree bound have been fixed.  The first theorem below retains that order of
quantifiers: its constant is selected before the translated point, modulus,
residue class, component ideal, and record.  The second theorem converts the
literal divided-box side to `T^(2/7)` and absorbs only a separately displayed
uniform bound for the number of affine minimal components.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 3000000

/-- Coefficient-uniform Pila estimate for every non-surface node record of
bounded affine component degree. -/
theorem exists_uniform_rankSevenNonSurfaceNodeRecord_rescaledPila_constant
    (hPila : Pila1995TheoremA) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
        (q : ReservoirModulus P k)
        (record : RankSevenNonSurfaceNodeRecord q.1),
      record ∈ occupiedRankSevenNonSurfaceNodeRecords
          p x₀ equations CF Cchart q →
      (∀ Q ∈ finiteMinimalPrimes
          (realProjectiveAffineChartIdeal record.component),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
          HasAffineHilbertDimensionDegree Q n d) →
      ((rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card : ℝ) +
        ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal record.component)).card : ℝ) * C₀ *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q.1) ^
            ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hUniform⟩ :=
    exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
      hPila 13 D ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro p x₀ equations CF Cchart P k hP q record hrecord hcomponents
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF Cchart
  have hrho : record.residue ∈ occupiedIntegralResidues q.1 Z :=
    (mem_occupiedRankSevenNonSurfaceNodeRecords_iff
      p x₀ equations CF Cchart q record).mp hrecord |>.1
  let base := integralResiduePacketBase Z record.residue hrho
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) / q.1
  have hq : 0 < q.1 := reservoirModulus_pos hP q
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have hqreal : (0 : ℝ) < q.1 := by exact_mod_cast hq
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / q.1 :=
      div_pos hside hqreal
    linarith
  exact hUniform hq base
    (realProjectiveAffineChartIdeal record.component) hcomponents
    (rankSevenNonSurfaceNodeRecordPointCell
      p x₀ equations CF Cchart record)
    (fun z hz ↦ intPoint_mem_realProjectiveAffineChartIdeal
      record.component z
        ((mem_rankSevenNonSurfaceNodeRecordPointCell_iff
          p x₀ equations CF Cchart record z).mp hz |>.2.2))
    (fun z hz ↦ intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record hz)
      (integralResiduePacketBase_mem Z record.residue hrho))
    U hU
    (fun z hz i ↦
      depthSevenNormalizedChartResiduePacket_quotientBox_anyModulus
        p x₀ equations CF Cchart hq record.residue hrho z
          (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record hz) i)

/-- One constant controls the nonlinear part of every surviving node record
at the reservoir scale, provided the displayed uniform component-count bound
holds.  The degree-one curve points remain literal. -/
theorem exists_uniform_rankSevenSurvivingNonSurfaceNodeRecord_scale_constant
    (hPila : Pila1995TheoremA) (D E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (denominator : ℤ)
        (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (q : ReservoirModulus P k)
        (record : RankSevenNonSurfaceNodeRecord q.1),
      record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q →
      (∀ Q ∈ finiteMinimalPrimes
          (realProjectiveAffineChartIdeal record.component),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
          HasAffineHilbertDimensionDegree Q n d) →
      (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal record.component)).card ≤ E →
      ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart denominator P k hP hlower q record).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card : ℝ) +
        C₁ * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hUniform⟩ :=
    exists_uniform_rankSevenNonSurfaceNodeRecord_rescaledPila_constant
      hPila D ε hε
  let C₁ : ℝ := (1 + (E : ℝ)) * C₀ *
    (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC₁ : 0 < C₁ := by
    dsimp only [C₁]
    positivity
  refine ⟨C₁, hC₁, ?_⟩
  intro p x₀ equations CF Cchart denominator P k hP hlower q record hrecord
    hcomponents hcount
  have hcoarse : record ∈ occupiedRankSevenNonSurfaceNodeRecords
      p x₀ equations CF Cchart q :=
    (mem_occupiedRankSevenSurvivingNonSurfaceNodeRecords_iff
      p x₀ equations CF Cchart denominator P k hP hlower q record).mp
        hrecord |>.1
  have hsource := hUniform p x₀ equations CF Cchart P k hP q record
    hcoarse hcomponents
  have hsubset : rankSevenSurvivingNonSurfaceNodeRecordPointCell
      p x₀ equations CF Cchart denominator P k hP hlower q record ⊆
      rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record :=
    Finset.filter_subset _ _
  apply (show
    ((rankSevenSurvivingNonSurfaceNodeRecordPointCell
      p x₀ equations CF Cchart denominator P k hP hlower q record).card : ℝ) ≤
      ((rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart record).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsubset).trans
  apply hsource.trans
  have hscale := recordPilaNonlinearTerm_le_reservoirScale
    p (hlower q) hC₀ hε
      (count := (nonlinearAffineComponents
        (realProjectiveAffineChartIdeal record.component)).card)
  have hnonlinear :
      ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal record.component)).card : ℝ) * C₀ *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) / q.1) ^
            ((1 / 2 : ℝ) + ε) ≤
        C₁ * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    apply hscale.trans
    apply mul_le_mul_of_nonneg_right
    · dsimp only [C₁]
      gcongr
    · exact Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _
  linarith

end

end TranslatedDepthSeven
