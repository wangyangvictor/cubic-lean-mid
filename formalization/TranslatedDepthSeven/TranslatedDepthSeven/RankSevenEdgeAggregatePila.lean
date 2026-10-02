import TranslatedDepthSeven.RankSevenRecordOccurrenceScale
import TranslatedDepthSeven.RankSevenRecordPila

/-!
# Uniform Pila estimate over the rank-seven edge frontiers

Pila's constant is selected before the translated point, the two endpoint
moduli, the occupied edge record, and the minimal-prime frontier.  Thus it is
uniform in all polynomial coefficients which occur in the reservoir family.
The aggregate theorem below sums only over the literal directed-edge type.
It retains the points on degree-one curve components as an exact finite sum,
and displays separately the three application-specific cardinality bounds:

* `D`, for each endpoint's list of surface components;
* `F`, for the minimal-prime frontiers of one component intersection;
* `E`, for the nonlinear affine components of one frontier.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 3000000

/-- No surviving edge record exists away from the literal reservoir graph.
This is the exact support statement which permits replacement of a double
sum over all ordered pairs by a sum over directed edges. -/
theorem occupiedRankSevenSurvivingSurfaceEdgeRecords_eq_empty_of_not_adj
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q r : ReservoirModulus P k)
    (hnot : ¬(modulusReservoirGraph P k hP).Adj q r) :
    occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart denominator P k hP hlower q r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro record hrecord
  exact hnot (survivingSurfaceEdgeRecord_adj
    p x₀ equations CF Cchart denominator P k hP hlower q r record hrecord)

/-- An arbitrary real weight on surviving edge records has the same total
whether one first sums over all ordered pairs of reservoir moduli or sums
over the subtype of actual directed edges.  The equality uses no positivity:
the off-edge record sets are literally empty. -/
theorem sum_survivingSurfaceEdgeRecords_allPairs_eq_directedEdges
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (weight : ∀ (q r : ReservoirModulus P k),
      RankSevenEdgeRecord (Nat.lcm q.1 r.1) → ℝ) :
    (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
      ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q r,
        weight q r record) =
      ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart denominator P k hP hlower
              qr.1.1 qr.1.2,
          weight qr.1.1 qr.1.2 record := by
  classical
  let edgeWeight : ReservoirModulus P k × ReservoirModulus P k → ℝ :=
    fun qr ↦ ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart denominator P k hP hlower qr.1 qr.2,
        weight qr.1 qr.2 record
  have hoff : ∀ qr : ReservoirModulus P k × ReservoirModulus P k,
      ¬(modulusReservoirGraph P k hP).Adj qr.1 qr.2 →
        edgeWeight qr = 0 := by
    intro qr hnot
    dsimp only [edgeWeight]
    rw [occupiedRankSevenSurvivingSurfaceEdgeRecords_eq_empty_of_not_adj
      p x₀ equations CF Cchart denominator P k hP hlower qr.1 qr.2 hnot]
    simp
  have hsmallBig :
      (∑ qr ∈ modulusReservoirDirectedEdges P k hP, edgeWeight qr) =
        ∑ qr : ReservoirModulus P k × ReservoirModulus P k,
          edgeWeight qr := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro qr _hqr hnotMem
    apply hoff qr
    intro hadj
    exact hnotMem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩)
  have hsubtype :
      (∑ qr ∈ modulusReservoirDirectedEdges P k hP, edgeWeight qr) =
        ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          edgeWeight qr.1 := by
    exact Finset.sum_subtype (modulusReservoirDirectedEdges P k hP)
      (fun _ ↦ Iff.rfl) edgeWeight
  calc
    (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
      ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q r,
        weight q r record) =
        ∑ qr : ReservoirModulus P k × ReservoirModulus P k,
          edgeWeight qr := by
      simpa [edgeWeight] using
        (Finset.sum_product
          (Finset.univ : Finset (ReservoirModulus P k))
          (Finset.univ : Finset (ReservoirModulus P k)) edgeWeight).symm
    _ = ∑ qr ∈ modulusReservoirDirectedEdges P k hP,
        edgeWeight qr := hsmallBig.symm
    _ = ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        edgeWeight qr.1 := hsubtype
    _ = ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart denominator P k hP hlower
              qr.1.1 qr.1.2,
          weight qr.1.1 qr.1.2 record := by rfl

/-- Specialization of the support equality to the exact edge-frontier term
appearing in the corrected finite-record partition. -/
theorem sum_rankSevenSurfaceEdgeFrontiers_allPairs_eq_directedEdges
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    (∑ q : ReservoirModulus P k, ∑ r : ReservoirModulus P k,
      ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q r,
        ∑ L ∈ finiteMinimalPrimes
            (record.leftComponent ⊔ record.rightComponent),
          ((rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L).card : ℝ)) =
      ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            ((rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF Cchart P k record L).card : ℝ) := by
  exact sum_survivingSurfaceEdgeRecords_allPairs_eq_directedEdges
    p x₀ equations CF Cchart denominator P k hP hlower
      (fun _q _r record ↦
        ∑ L ∈ finiteMinimalPrimes
            (record.leftComponent ⊔ record.rightComponent),
          ((rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L).card : ℝ))

/-- Coefficient-uniform Pila estimate for every minimal-prime frontier of a
surviving edge record.  The record hypothesis implies both occupancy and
adjacency; the estimate itself uses occupancy through the exact lcm residue
packet. -/
theorem exists_uniform_rankSevenSurfaceEdgeFrontier_rescaledPila_constant
    (hPila : Pila1995TheoremA) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (q r : ReservoirModulus P k)
        (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
        (L : Ideal (MvPolynomial (Fin 14) ℚ)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q r →
      (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
          HasAffineHilbertDimensionDegree Q n d) →
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) +
        ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card : ℝ) * C₀ *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
            Nat.lcm q.1 r.1) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hUniform⟩ :=
    exists_uniform_pilaDimZeroOrNonlinearCurveComponents_rescaled_constant
      hPila 13 D ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro p x₀ equations CF Cchart denominator P k hP hlower q r record L
    hrecord hcomponents
  have hcoarse : record ∈ occupiedRankSevenSurfaceEdgeRecords
      p x₀ equations CF Cchart P k q r hP :=
    (Finset.mem_filter.mp hrecord).1
  let Z := depthSevenNormalizedJacobianChartCell
    p x₀ equations CF Cchart
  have hrho : record.residue ∈
      occupiedIntegralResidues (Nat.lcm q.1 r.1) Z :=
    (mem_occupiedRankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF Cchart P k q r hP record).mp hcoarse |>.2
  let base := integralResiduePacketBase Z record.residue hrho
  let U : ℝ := 1 + (4 * surfaceTangentNaturalSide p : ℝ) /
    Nat.lcm q.1 r.1
  have hq : 0 < q.1 := reservoirModulus_pos hP q
  have hr : 0 < r.1 := reservoirModulus_pos hP r
  have hlcm : 0 < Nat.lcm q.1 r.1 := Nat.lcm_pos hq hr
  have hU : 1 < U := by
    dsimp only [U]
    have hside : (0 : ℝ) < 4 * surfaceTangentNaturalSide p := by
      exact_mod_cast (show 0 < 4 * surfaceTangentNaturalSide p by
        have := one_le_surfaceTangentNaturalSide p
        omega)
    have hlcmreal : (0 : ℝ) < Nat.lcm q.1 r.1 := by
      exact_mod_cast hlcm
    have : (0 : ℝ) <
        (4 * surfaceTangentNaturalSide p : ℝ) / Nat.lcm q.1 r.1 :=
      div_pos hside hlcmreal
    linarith
  exact hUniform hlcm base (realProjectiveAffineChartIdeal L) hcomponents
    (rankSevenSurfaceEdgeFrontierPointCell
      p x₀ equations CF Cchart P k record L)
    (fun z hz ↦ intPoint_mem_realProjectiveAffineChartIdeal L z
      ((mem_rankSevenSurfaceEdgeFrontierPointCell_iff
        p x₀ equations CF Cchart P k record L z).mp hz |>.2.2))
    (fun z hz ↦ intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L hz)
      (integralResiduePacketBase_mem Z record.residue hrho))
    U hU
    (fun z hz i ↦
      depthSevenNormalizedChartResiduePacket_quotientBox_anyModulus
        p x₀ equations CF Cchart hlcm record.residue hrho z
          (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L hz) i)

/-- A single constant controls the nonlinear part of every minimal-prime
frontier of a surviving edge record at reservoir scale.  The degree-one
curve points remain literal. -/
theorem exists_uniform_rankSevenSurvivingSurfaceEdgeFrontier_scale_constant
    (hPila : Pila1995TheoremA) (D E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (q r : ReservoirModulus P k)
        (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
        (L : Ideal (MvPolynomial (Fin 14) ℚ)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower q r →
      (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D ∧
          HasAffineHilbertDimensionDegree Q n d) →
      (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ E →
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) +
        C₁ * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨C₀, hC₀, hUniform⟩ :=
    exists_uniform_rankSevenSurfaceEdgeFrontier_rescaledPila_constant
      hPila D ε hε
  let C₁ : ℝ := (1 + (E : ℝ)) * C₀ *
    (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)
  have hC₁ : 0 < C₁ := by
    dsimp only [C₁]
    positivity
  refine ⟨C₁, hC₁, ?_⟩
  intro p x₀ equations CF Cchart denominator P k hP hlower q r record L
    hrecord hcomponents hcount
  have hsource := hUniform p x₀ equations CF Cchart denominator P k hP
    hlower q r record L hrecord hcomponents
  apply hsource.trans
  have hlcmLower :
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
          p.T (5 / 7) ≤ Nat.lcm q.1 r.1 :=
    (hlower q).trans (Nat.le_lcm_left q.1 (reservoirModulus_pos hP r))
  have hscale := recordPilaNonlinearTerm_le_reservoirScale
    p hlcmLower hC₀ hε
      (count := (nonlinearAffineComponents
        (realProjectiveAffineChartIdeal L)).card)
  have hnonlinear :
      ((nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card : ℝ) * C₀ *
          (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
            Nat.lcm q.1 r.1) ^ ((1 / 2 : ℝ) + ε) ≤
        C₁ * (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    apply hscale.trans
    apply mul_le_mul_of_nonneg_right
    · dsimp only [C₁]
      gcongr
    · exact Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _
  linarith

/-- The full nonlinear edge-frontier contribution, summed over the actual
directed reservoir edges, has the occurrence scale `T^(30/7) H^(8δ)` times
the divided-curve scale.  Points on degree-one curve components are not
estimated here: they remain as the literal first sum on the right.

The bounds `Dsource`, `F`, and `E` are deliberately not absorbed into the
Pila constant.  They count, respectively, endpoint surface components,
minimal-prime frontiers of one intersection, and nonlinear affine
components of one frontier. -/
theorem exists_uniform_rankSevenSurvivingSurfaceEdgeFrontier_aggregate_constant
    (hPila : Pila1995TheoremA) (Dgeom : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {M₀ δ Cmod : ℝ}, 0 ≤ M₀ → 0 < δ → 0 ≤ Cmod →
      ∀ (p : Parameters) (x₀ : IntVector 13)
        (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
        (Cchart : IntegralDepthSevenJacobianChartIndex equations)
        (model : FixedFivefoldResidueModel
          (indexedFinsetFamily (rationalizedEquationFinset equations)))
        (P : Finset ℕ) (k Dsource F E : ℕ)
        (hP : ∀ s ∈ P, s.Prime)
        (hlower : ∀ q : ReservoirModulus P k,
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1)
        (hsourceComponents : ∀ (q : ReservoirModulus P k)
            (rho : Fin 13 → ZMod q.1),
          rho ∈ occupiedIntegralResidues q.1
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) →
          (rankSevenSurfaceNodeComponents
            p x₀ equations CF Cchart q.1 rho).card ≤ Dsource)
        (hfactorDepth : 2 * k ≤ reservoirDepth M₀ p.H)
        (hH : reservoirSubpowerThreshold M₀
          (model.localConstant : ℝ) δ ≤ p.H)
        (hfamily : ((((modulusReservoir P k).card +
          (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
            2 * p.H ^ δ))
        (hmoduli : ∀ q : ReservoirModulus P k, Squarefree q.1)
        (hupper : ∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hP).Adj q r →
          (Nat.lcm q.1 r.1 : ℝ) ≤
            Cmod * p.T ^ (5 / 7 : ℝ) * p.H ^ δ)
        (hfrontierCount : ∀
            (qr : ↑(modulusReservoirDirectedEdges P k hP))
            (record : RankSevenEdgeRecord
              (Nat.lcm qr.1.1.1 qr.1.2.1)),
          record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2 →
          (finiteMinimalPrimes
            (record.leftComponent ⊔ record.rightComponent)).card ≤ F)
        (hfrontierGeometry : ∀
            (qr : ↑(modulusReservoirDirectedEdges P k hP))
            (record : RankSevenEdgeRecord
              (Nat.lcm qr.1.1.1 qr.1.2.1)),
          record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2 →
          ∀ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
          ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
            ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ Dgeom ∧
              HasAffineHilbertDimensionDegree Q n d)
        (hnonlinearCount : ∀
            (qr : ↑(modulusReservoirDirectedEdges P k hP))
            (record : RankSevenEdgeRecord
              (Nat.lcm qr.1.1.1 qr.1.2.1)),
          record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2 →
          ∀ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
          (nonlinearAffineComponents
            (realProjectiveAffineChartIdeal L)).card ≤ E),
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            ((rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF Cchart P k record L).card : ℝ)) ≤
        (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              ((finitePointsOnLinearCurveComponents
                (realProjectiveAffineChartIdeal L)
                (rankSevenSurfaceEdgeFrontierPointCell
                  p x₀ equations CF Cchart P k record L)).card : ℝ)) +
        (2 * Cmod ^ 6 * (Dsource * Dsource) *
            p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) * F *
          ((1 + (E : ℝ)) * C₀ *
            (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
          (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C₀, hC₀, hUniform⟩ :=
    exists_uniform_rankSevenSurfaceEdgeFrontier_rescaledPila_constant
      hPila Dgeom ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro M₀ δ Cmod hM₀ hδ hCmod p x₀ equations CF Cchart model P k
    Dsource F E hP hlower hsourceComponents hfactorDepth hH hfamily
    hmoduli hupper hfrontierCount hfrontierGeometry hnonlinearCount
  let B : ℝ := ((1 + (E : ℝ)) * C₀ *
      (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
    (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) hC₀.le)
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _)
  have hfrontier : ∀
      (qr : ↑(modulusReservoirDirectedEdges P k hP))
      (record : RankSevenEdgeRecord (Nat.lcm qr.1.1.1 qr.1.2.1)),
    record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower
          qr.1.1 qr.1.2 →
    ∀ L ∈ finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent),
      ((rankSevenSurfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k record L).card : ℝ) ≤
        ((finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal L)
          (rankSevenSurfaceEdgeFrontierPointCell
            p x₀ equations CF Cchart P k record L)).card : ℝ) + B := by
    intro qr record hrecord L hL
    have hsource := hUniform p x₀ equations CF Cchart model.denominator
      P k hP hlower qr.1.1 qr.1.2 record L hrecord
        (hfrontierGeometry qr record hrecord L hL)
    apply hsource.trans
    have hlcmLower :
        manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ Nat.lcm qr.1.1.1 qr.1.2.1 :=
      (hlower qr.1.1).trans
        (Nat.le_lcm_left qr.1.1.1
          (reservoirModulus_pos hP qr.1.2))
    have hscale := recordPilaNonlinearTerm_le_reservoirScale
      p hlcmLower hC₀ hε
        (count := (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card)
    have hnonlinear :
        ((nonlinearAffineComponents
            (realProjectiveAffineChartIdeal L)).card : ℝ) * C₀ *
            (1 + (4 * surfaceTangentNaturalSide p : ℝ) /
              Nat.lcm qr.1.1.1 qr.1.2.1) ^ ((1 / 2 : ℝ) + ε) ≤ B := by
      apply hscale.trans
      apply mul_le_mul_of_nonneg_right
      · dsimp only [B]
        gcongr
        exact hnonlinearCount qr record hrecord L hL
      · exact Real.rpow_nonneg (Real.rpow_nonneg p.T_pos.le _) _
    linarith
  have hsplit :
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            ((rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF Cchart P k record L).card : ℝ)) ≤
        (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              ((finitePointsOnLinearCurveComponents
                (realProjectiveAffineChartIdeal L)
                (rankSevenSurfaceEdgeFrontierPointCell
                  p x₀ equations CF Cchart P k record L)).card : ℝ)) +
        (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          ((occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2).card : ℝ)) * F * B := by
    calc
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            ((rankSevenSurfaceEdgeFrontierPointCell
              p x₀ equations CF Cchart P k record L).card : ℝ)) ≤
          ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2,
              ∑ L ∈ finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent),
                (((finitePointsOnLinearCurveComponents
                  (realProjectiveAffineChartIdeal L)
                  (rankSevenSurfaceEdgeFrontierPointCell
                    p x₀ equations CF Cchart P k record L)).card : ℝ) +
                  B) := by
        apply Finset.sum_le_sum
        intro qr _hqr
        apply Finset.sum_le_sum
        intro record hrecord
        apply Finset.sum_le_sum
        intro L hL
        exact hfrontier qr record hrecord L hL
      _ = (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              ((finitePointsOnLinearCurveComponents
                (realProjectiveAffineChartIdeal L)
                (rankSevenSurfaceEdgeFrontierPointCell
                  p x₀ equations CF Cchart P k record L)).card : ℝ)) +
          (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2,
              ∑ _L ∈ finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent), B) := by
        simp only [Finset.sum_add_distrib]
      _ ≤ (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              ((finitePointsOnLinearCurveComponents
                (realProjectiveAffineChartIdeal L)
                (rankSevenSurfaceEdgeFrontierPointCell
                  p x₀ equations CF Cchart P k record L)).card : ℝ)) +
          (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            ((occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2).card : ℝ)) * F * B := by
        have hrem :
          (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2,
              ∑ _L ∈ finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent), B) ≤
            (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
              ((occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2).card : ℝ)) * F * B := by
          calc
            (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
              ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                  p x₀ equations CF Cchart model.denominator P k hP hlower
                    qr.1.1 qr.1.2,
                ∑ _L ∈ finiteMinimalPrimes
                    (record.leftComponent ⊔ record.rightComponent), B) ≤
                ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
                  ∑ _record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                      p x₀ equations CF Cchart model.denominator P k hP hlower
                        qr.1.1 qr.1.2,
                    (F : ℝ) * B := by
              apply Finset.sum_le_sum
              intro qr _hqr
              apply Finset.sum_le_sum
              intro record hrecord
              rw [Finset.sum_const, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast hfrontierCount qr record hrecord) hB
            _ = (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
              ((occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2).card : ℝ)) * F * B := by
              calc
                (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
                  ∑ _record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                      p x₀ equations CF Cchart model.denominator P k hP hlower
                        qr.1.1 qr.1.2,
                    (F : ℝ) * B) =
                    ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
                      ((occupiedRankSevenSurvivingSurfaceEdgeRecords
                        p x₀ equations CF Cchart model.denominator P k hP
                          hlower qr.1.1 qr.1.2).card : ℝ) *
                        ((F : ℝ) * B) := by
                  apply Finset.sum_congr rfl
                  intro qr _hqr
                  rw [Finset.sum_const, nsmul_eq_mul]
                _ = (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
                    ((occupiedRankSevenSurvivingSurfaceEdgeRecords
                      p x₀ equations CF Cchart model.denominator P k hP hlower
                        qr.1.1 qr.1.2).card : ℝ)) * ((F : ℝ) * B) := by
                  rw [Finset.sum_mul]
                _ = (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
                    ((occupiedRankSevenSurvivingSurfaceEdgeRecords
                      p x₀ equations CF Cchart model.denominator P k hP hlower
                        qr.1.1 qr.1.2).card : ℝ)) * F * B := by
                  ring
        linarith
  apply hsplit.trans
  have hrecords :=
    sum_occupiedRankSevenSurvivingSurfaceEdgeRecords_over_edges_cast_le_scale
      hM₀ hδ hCmod p x₀ equations CF Cchart model P k hP hlower
        Dsource hsourceComponents hfactorDepth hH hfamily hmoduli hupper
  have hFB : 0 ≤ (F : ℝ) * B := mul_nonneg (Nat.cast_nonneg F) hB
  have hmul := mul_le_mul_of_nonneg_right hrecords hFB
  dsimp only [B] at hmul ⊢
  have hremainder :
    (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ((occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2).card : ℝ)) * F *
      (((1 + (E : ℝ)) * C₀ *
          (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
        (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε)) ≤
      (2 * Cmod ^ 6 * (Dsource * Dsource) *
          p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) * F *
        ((1 + (E : ℝ)) * C₀ *
          (2 : ℝ) ^ ((1 / 2 : ℝ) + ε)) *
        (p.T ^ (2 / 7 : ℝ)) ^ ((1 / 2 : ℝ) + ε) := by
    nlinarith
  linarith

end

end TranslatedDepthSeven
