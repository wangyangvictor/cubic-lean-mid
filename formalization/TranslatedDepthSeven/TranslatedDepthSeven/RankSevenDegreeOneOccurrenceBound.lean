import TranslatedDepthSeven.RankSevenDegreeOneCurveAssembly

/-!
# Local Bezout bounds for the literal line occurrences

The three Salberger--Pila aggregates retain degree-one components rather
than estimating them.  This file counts only their *occurrences*.  The input
is local: a bound for the affine minimal components of each actual record,
and, on an edge, a bound for the displayed minimal-prime frontier.  There is
no hypothesis about the number of affine lines in the union of all records.

The result is the precise reservoir occurrence scale `T^(30/7) H^(8 delta)`.
It is the factor later multiplied by the one-line high-direction estimate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 6000000

/-- A local component bound and the literal frontier bound control the
number of tagged line occurrences.  Equal lines in different records are
correctly counted with multiplicity here; only the subsequent low-direction
sum forgets that multiplicity. -/
theorem card_rankSevenTaggedLinearComponent_le_local_bounds
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount Dline F : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ)
    (hnode : ∀ (q : ReservoirModulus P k)
        (record : RankSevenNonSurfaceNodeRecord q.1),
      record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower q →
      (linearAffineComponents
        (realProjectiveAffineChartIdeal record.component)).card ≤ Dline)
    (hfrontier : ∀
        (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤ F)
    (hedge : ∀
        (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (linearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ Dline)
    (hpersistent : ∀ record ∈
        occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower X
            markCount localEquations selectedVar menu markOf,
      (linearAffineComponents
        (realAffineChartIntersectionIdeal I
          (auxiliaryForm record))).card ≤ Dline) :
    Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm) ≤
      Dline *
        ((∑ q : ReservoirModulus P k,
          (occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q).card) +
        F * (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
          (occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2).card) +
        (occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower X
            markCount localEquations selectedVar menu markOf).card) := by
  classical
  rw [card_rankSevenTaggedLinearComponent_eq_three_sums]
  let nodeMass := ∑ q : ReservoirModulus P k,
    (occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower q).card
  let edgeMass := ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
    (occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower
        qr.1.1 qr.1.2).card
  let persistentRecords :=
    occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower X
        markCount localEquations selectedVar menu markOf
  have hnodeSum :
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q,
          (linearAffineComponents
            (realProjectiveAffineChartIdeal record.component)).card) ≤
        Dline * nodeMass := by
    calc
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q,
          (linearAffineComponents
            (realProjectiveAffineChartIdeal record.component)).card) ≤
          ∑ q : ReservoirModulus P k,
            Dline *
              (occupiedRankSevenSurvivingNonSurfaceNodeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower q).card := by
        apply Finset.sum_le_sum
        intro q _hq
        calc
          (∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower q,
            (linearAffineComponents
              (realProjectiveAffineChartIdeal record.component)).card) ≤
              ∑ _record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
                  p x₀ equations CF Cchart model.denominator P k hP hlower q,
                Dline := by
            apply Finset.sum_le_sum
            intro record hrecord
            exact hnode q record hrecord
          _ = Dline *
              (occupiedRankSevenSurvivingNonSurfaceNodeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower q).card := by
            simp [mul_comm]
      _ = Dline * nodeMass := by
        dsimp only [nodeMass]
        rw [Finset.mul_sum]
  have hedgeSum :
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (linearAffineComponents
              (realProjectiveAffineChartIdeal L)).card) ≤
        Dline * (F * edgeMass) := by
    calc
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (linearAffineComponents
              (realProjectiveAffineChartIdeal L)).card) ≤
          ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
            (Dline * F) *
              (occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2).card := by
        apply Finset.sum_le_sum
        intro qr _hqr
        calc
          (∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
              p x₀ equations CF Cchart model.denominator P k hP hlower
                qr.1.1 qr.1.2,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              (linearAffineComponents
                (realProjectiveAffineChartIdeal L)).card) ≤
              ∑ _record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
                  p x₀ equations CF Cchart model.denominator P k hP hlower
                    qr.1.1 qr.1.2,
                Dline * F := by
            apply Finset.sum_le_sum
            intro record hrecord
            calc
              (∑ L ∈ finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent),
                (linearAffineComponents
                  (realProjectiveAffineChartIdeal L)).card) ≤
                  ∑ _L ∈ finiteMinimalPrimes
                      (record.leftComponent ⊔ record.rightComponent),
                    Dline := by
                apply Finset.sum_le_sum
                intro L hL
                exact hedge qr record hrecord L hL
              _ = Dline * (finiteMinimalPrimes
                  (record.leftComponent ⊔ record.rightComponent)).card := by
                simp [mul_comm]
              _ ≤ Dline * F := Nat.mul_le_mul_left Dline
                (hfrontier qr record hrecord)
          _ = (Dline * F) *
              (occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2).card := by simp [mul_comm, mul_assoc]
      _ = Dline * (F * edgeMass) := by
        dsimp only [edgeMass]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Fintype.sum_congr
        intro qr
        ring
  have hpersistentSum :
      (∑ record ∈ persistentRecords,
        (linearAffineComponents
          (realAffineChartIntersectionIdeal I
            (auxiliaryForm record))).card) ≤
        Dline * persistentRecords.card := by
    calc
      (∑ record ∈ persistentRecords,
        (linearAffineComponents
          (realAffineChartIntersectionIdeal I
            (auxiliaryForm record))).card) ≤
          ∑ _record ∈ persistentRecords, Dline := by
        apply Finset.sum_le_sum
        intro record hrecord
        exact hpersistent record hrecord
      _ = Dline * persistentRecords.card := by simp [mul_comm]
  change _ ≤ Dline * (nodeMass + F * edgeMass + persistentRecords.card)
  calc
    _ ≤ Dline * nodeMass + Dline * (F * edgeMass) +
        Dline * persistentRecords.card :=
      Nat.add_le_add (Nat.add_le_add hnodeSum hedgeSum) hpersistentSum
    _ = Dline * (nodeMass + F * edgeMass + persistentRecords.card) := by
      ring

/-- Reservoir-scale form of the preceding literal occurrence count.  The
only geometric cardinalities are the local Bezout bounds `Dline`, `F`,
`Dnode`, and `Dsurface`; the exponent is inherited from the three already
proved record counts. -/
theorem card_rankSevenTaggedLinearComponent_cast_le_reservoirScale
    {M₀ δ Cres : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hCres : 0 ≤ Cres)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ)
    (k markCount Dnode Dsurface Dline F : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ)
    (hnodeRecords : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) →
      (rankSevenNonSurfaceNodeComponents
        p x₀ equations CF Cchart q.1 rho).card ≤ Dnode)
    (hsurfaceRecords : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF Cchart q.1 rho).card ≤ Dsurface)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hfactorDepth : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hmoduli : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hupper : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ Cres * p.T ^ (5 / 7 : ℝ) * p.H ^ δ)
    (hedgeUpper : ∀ q r : ReservoirModulus P k,
      (modulusReservoirGraph P k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        Cres * p.T ^ (5 / 7 : ℝ) * p.H ^ δ)
    (hnode : ∀ (q : ReservoirModulus P k)
        (record : RankSevenNonSurfaceNodeRecord q.1),
      record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower q →
      (linearAffineComponents
        (realProjectiveAffineChartIdeal record.component)).card ≤ Dline)
    (hfrontier : ∀
        (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤ F)
    (hedge : ∀
        (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (linearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ Dline)
    (hpersistent : ∀ record ∈
        occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower X
            markCount localEquations selectedVar menu markOf,
      (linearAffineComponents
        (realAffineChartIntersectionIdeal I
          (auxiliaryForm record))).card ≤ Dline) :
    (Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm) : ℝ) ≤
      (2 * Cres ^ 6 * Dline *
        (Dnode + F * (Dsurface * Dsurface) + Dsurface * markCount)) *
          p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
  let nodeMass : ℝ := ∑ q : ReservoirModulus P k,
    ((occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower q).card : ℝ)
  let edgeMass : ℝ := ∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
    ((occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower
        qr.1.1 qr.1.2).card : ℝ)
  let persistentRecords :=
    occupiedRankSevenPersistentMultiplicityOneRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower X
        markCount localEquations selectedVar menu markOf
  have hoccNat := card_rankSevenTaggedLinearComponent_le_local_bounds
    p x₀ equations CF Cchart model P k markCount Dline F hP hlower I X
      localEquations selectedVar menu markOf auxiliaryForm hnode hfrontier
      hedge hpersistent
  have hocc :
      (Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
        model P k markCount hP hlower I X localEquations selectedVar menu
          markOf auxiliaryForm) : ℝ) ≤
        Dline * (nodeMass + F * edgeMass + persistentRecords.card) := by
    have hcast :
        (Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
          model P k markCount hP hlower I X localEquations selectedVar menu
            markOf auxiliaryForm) : ℝ) ≤
          ((Dline *
            ((∑ q : ReservoirModulus P k,
              (occupiedRankSevenSurvivingNonSurfaceNodeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower q).card) +
            F * (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
              (occupiedRankSevenSurvivingSurfaceEdgeRecords
                p x₀ equations CF Cchart model.denominator P k hP hlower
                  qr.1.1 qr.1.2).card) +
            persistentRecords.card) : ℕ) : ℝ) := by
      exact_mod_cast hoccNat
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_sum,
      nodeMass, edgeMass] using hcast
  have hnodeMass : nodeMass ≤
      2 * Cres ^ 6 * Dnode * p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
    dsimp only [nodeMass]
    exact sum_occupiedRankSevenSurvivingNonSurfaceNodeRecords_cast_le_scale
      hM₀ hδ hCres p x₀ equations CF Cchart model P k hP hlower Dnode
        hnodeRecords hk hH hfamily hupper
  have hedgeMass : edgeMass ≤
      2 * Cres ^ 6 * (Dsurface * Dsurface) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
    dsimp only [edgeMass]
    exact sum_occupiedRankSevenSurvivingSurfaceEdgeRecords_over_edges_cast_le_scale
      hM₀ hδ hCres p x₀ equations CF Cchart model P k hP hlower
        Dsurface hsurfaceRecords hfactorDepth hH hfamily hmoduli hedgeUpper
  have hpersistentMass : (persistentRecords.card : ℝ) ≤
      2 * Cres ^ 6 * (Dsurface * markCount) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
    dsimp only [persistentRecords]
    exact card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_scale
      hM₀ hδ hCres p x₀ equations CF Cchart model P k markCount
        Dsurface hP hlower X localEquations selectedVar menu markOf
        hsurfaceRecords hk hH hfamily hupper
  apply hocc.trans
  have hinside : nodeMass + (F : ℝ) * edgeMass + persistentRecords.card ≤
      2 * Cres ^ 6 * Dnode * p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) +
      (F : ℝ) * (2 * Cres ^ 6 * (Dsurface * Dsurface) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) +
      2 * Cres ^ 6 * (Dsurface * markCount) *
        p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
    exact add_le_add (add_le_add hnodeMass
      (mul_le_mul_of_nonneg_left hedgeMass (Nat.cast_nonneg F)))
      hpersistentMass
  calc
    (Dline : ℝ) * (nodeMass + (F : ℝ) * edgeMass +
        persistentRecords.card) ≤
      (Dline : ℝ) *
        (2 * Cres ^ 6 * Dnode * p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) +
        (F : ℝ) * (2 * Cres ^ 6 * (Dsurface * Dsurface) *
          p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) +
        2 * Cres ^ 6 * (Dsurface * markCount) *
          p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ)) :=
        mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg Dline)
    _ = (2 * Cres ^ 6 * Dline *
        (Dnode + F * (Dsurface * Dsurface) + Dsurface * markCount)) *
          p.T ^ (30 / 7 : ℝ) * p.H ^ (8 * δ) := by
      ring

end

end TranslatedDepthSeven
