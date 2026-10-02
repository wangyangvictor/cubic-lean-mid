import TranslatedDepthSeven.DegreeOneCurveOccurrenceAssembly
import TranslatedDepthSeven.RankSevenNodeAggregateSum
import TranslatedDepthSeven.RankSevenEdgeAggregatePila
import TranslatedDepthSeven.RankSevenPersistentUniformAggregate

/-!
# The literal rank-seven degree-one curve family

This file puts the three displayed degree-one sums left by the node, edge,
and persistent Salberger--Pila estimates into one finite tagged family.
Every tag is the actual record data used in the preceding decomposition.
Consequently its tagged point cardinality is exactly the sum printed by
those three estimates, not an abstract majorant and not an unproved global
line count.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option maxHeartbeats 6000000

/-- A finite sum over the subtype cut out by `s` is the corresponding
ordinary finite sum.  The summand below is deliberately required to factor
through the underlying element: none of the record contributions depends on
the proof that its record belongs to the occupied set. -/
@[simp]
theorem sum_subtype_mem_eq_sum {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (s : Finset α) [Fintype {x // x ∈ s}]
    (f : α → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  have huniv : (Finset.univ : Finset {x // x ∈ s}) = s.attach := by
    ext x
    simp
  rw [huniv, Finset.sum_attach]

/-- The cardinality analogue of `sum_subtype_mem_eq_sum`, valid for the
particular lawful `Fintype` instance carried by a record family. -/
@[simp]
theorem card_subtype_mem_eq_card {α : Type*} [DecidableEq α]
    (s : Finset α) [Fintype {x // x ∈ s}] :
    Fintype.card {x // x ∈ s} = s.card := by
  have huniv : (Finset.univ : Finset {x // x ∈ s}) = s.attach := by
    ext x
    simp
  change (Finset.univ : Finset {x // x ∈ s}).card = s.card
  rw [huniv, Finset.card_attach]

/-! ## The three literal index types -/

/-- A surviving non-surface node record, retaining its reservoir modulus. -/
def RankSevenNodeDegreeOneIndex
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :=
  Σ q : ReservoirModulus P k,
    {record // record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower q}

instance rankSevenNodeDegreeOneIndexFintype
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    Fintype (RankSevenNodeDegreeOneIndex
      p x₀ equations CF Cchart model P k hP hlower) := by
  classical
  letI (q : ReservoirModulus P k) : Fintype
      {record // record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower q} :=
    Fintype.ofFinset
      (occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower q)
      (fun _ ↦ Iff.rfl)
  unfold RankSevenNodeDegreeOneIndex
  exact inferInstance

/-- A minimal-prime frontier in one actual surviving directed-edge record. -/
def RankSevenEdgeDegreeOneIndex
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :=
  Σ qr : ↑(modulusReservoirDirectedEdges P k hP),
    Σ record : {record //
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower
          qr.1.1 qr.1.2},
      {L // L ∈ finiteMinimalPrimes
        (record.1.leftComponent ⊔ record.1.rightComponent)}

instance rankSevenEdgeDegreeOneIndexFintype
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    Fintype (RankSevenEdgeDegreeOneIndex
      p x₀ equations CF Cchart model P k hP hlower) := by
  classical
  letI (qr : ↑(modulusReservoirDirectedEdges P k hP)) : Fintype
      {record // record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower
          qr.1.1 qr.1.2} :=
    Fintype.ofFinset
      (occupiedRankSevenSurvivingSurfaceEdgeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower
          qr.1.1 qr.1.2) (fun _ ↦ Iff.rfl)
  letI (qr : ↑(modulusReservoirDirectedEdges P k hP))
      (record : {record //
        record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower
            qr.1.1 qr.1.2}) : Fintype
      {L // L ∈ finiteMinimalPrimes
        (record.1.leftComponent ⊔ record.1.rightComponent)} :=
    Fintype.ofFinset
      (finiteMinimalPrimes
        (record.1.leftComponent ⊔ record.1.rightComponent))
      (fun _ ↦ Iff.rfl)
  unfold RankSevenEdgeDegreeOneIndex
  exact inferInstance

/-- A retained persistent multiplicity-one record. -/
def RankSevenPersistentDegreeOneIndex
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :=
  {record // record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
    p x₀ equations CF Cchart model.denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf}

instance rankSevenPersistentDegreeOneIndexFintype
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    Fintype (RankSevenPersistentDegreeOneIndex
      p x₀ equations CF Cchart model P k markCount hP hlower X
        localEquations selectedVar menu markOf) := by
  classical
  unfold RankSevenPersistentDegreeOneIndex
  exact Fintype.ofFinset _ (fun _ ↦ Iff.rfl)

/-! ## The combined literal family -/

/-- The disjoint union of node, edge, and persistent indices. -/
def RankSevenDegreeOneIndex
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :=
  Sum
    (Sum
      (RankSevenNodeDegreeOneIndex
        p x₀ equations CF Cchart model P k hP hlower)
      (RankSevenEdgeDegreeOneIndex
        p x₀ equations CF Cchart model P k hP hlower))
    (RankSevenPersistentDegreeOneIndex
      p x₀ equations CF Cchart model P k markCount hP hlower X
        localEquations selectedVar menu markOf)

instance rankSevenDegreeOneIndexFintype
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    Fintype (RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf) := by
  unfold RankSevenDegreeOneIndex
  infer_instance

/-- The real affine ideal attached to each literal index. -/
def rankSevenDegreeOneIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
      MvPolynomial (Fin 14) ℚ) :
    RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k markCount
      hP hlower X localEquations selectedVar menu markOf →
      Ideal (MvPolynomial (Fin 13) ℝ)
  | Sum.inl (Sum.inl node) =>
      realProjectiveAffineChartIdeal node.2.1.component
  | Sum.inl (Sum.inr edge) =>
      realProjectiveAffineChartIdeal edge.2.2.1
  | Sum.inr persistent =>
      realAffineChartIntersectionIdeal I (auxiliaryForm persistent.1)

/-- The exact finite point set attached to each literal index. -/
def rankSevenDegreeOnePointSet
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k markCount
      hP hlower X localEquations selectedVar menu markOf →
      Finset (IntVector 13)
  | Sum.inl (Sum.inl node) =>
      rankSevenNonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart node.2.1
  | Sum.inl (Sum.inr edge) =>
      rankSevenSurfaceEdgeFrontierPointCell p x₀ equations CF Cchart P k
        edge.2.1.1 edge.2.2.1
  | Sum.inr persistent =>
      rankSevenPacketPointsOnSourceComponent
        (integralResiduePacket
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) persistent.1.residue) I

/-- The literal congruence modulus carried by each node, edge, or persistent
degree-one index.  An edge carries the least common multiple already present
in its actual record; no auxiliary global modulus is introduced. -/
def rankSevenDegreeOneIndexModulus
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k markCount
      hP hlower X localEquations selectedVar menu markOf → ℕ
  | Sum.inl (Sum.inl node) => node.1.1
  | Sum.inl (Sum.inr edge) => Nat.lcm edge.1.1.1.1 edge.1.1.2.1
  | Sum.inr persistent => persistent.1.modulus.1

/-- Every modulus carried by the literal degree-one index is positive. -/
theorem rankSevenDegreeOneIndexModulus_pos
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf) :
    0 < rankSevenDegreeOneIndexModulus p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf i := by
  rcases i with (node | edge) | persistent
  · exact reservoirModulus_pos hP node.1
  · exact Nat.lcm_pos
      (reservoirModulus_pos hP edge.1.1.1)
      (reservoirModulus_pos hP edge.1.1.2)
  · exact reservoirModulus_pos hP persistent.1.modulus

/-- Each literal line modulus is at least the lower endpoint of the
reservoir.  For an edge this is just the divisibility of either endpoint
modulus into their least common multiple. -/
theorem rankSevenDegreeOneIndexModulus_lower
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf) :
    manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤
      rankSevenDegreeOneIndexModulus p x₀ equations CF Cchart model P k
        markCount hP hlower X localEquations selectedVar menu markOf i := by
  rcases i with (node | edge) | persistent
  · exact hlower node.1
  · exact (hlower edge.1.1.1).trans
      (Nat.le_lcm_left edge.1.1.1.1
        (reservoirModulus_pos hP edge.1.1.2))
  · exact hlower persistent.1.modulus

/-- Two points in one literal degree-one index retain the congruence of
that actual node, edge, or persistent record. -/
theorem rankSevenDegreeOnePointSet_pair_congruent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf)
    {z w : IntVector 13}
    (hz : z ∈ rankSevenDegreeOnePointSet p x₀ equations CF Cchart model
      P k markCount hP hlower I X localEquations selectedVar menu markOf i)
    (hw : w ∈ rankSevenDegreeOnePointSet p x₀ equations CF Cchart model
      P k markCount hP hlower I X localEquations selectedVar menu markOf i) :
    IntVectorCongruent
      (rankSevenDegreeOneIndexModulus p x₀ equations CF Cchart model P k
        markCount hP hlower X localEquations selectedVar menu markOf i) z w := by
  rcases i with (node | edge) | persistent
  · exact intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart node.2.1 hz)
      (mem_integralResiduePacket_of_mem_nonSurfaceNodeRecordPointCell
        p x₀ equations CF Cchart node.2.1 hw)
  · exact intVectorCongruent_of_mem_same_integralResiduePacket
      (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k
          (q := edge.1.1.1) (r := edge.1.1.2)
          edge.2.1.1 edge.2.2.1 hz)
      (mem_integralResiduePacket_of_mem_surfaceEdgeFrontierPointCell
        p x₀ equations CF Cchart P k
          (q := edge.1.1.1) (r := edge.1.1.2)
          edge.2.1.1 edge.2.2.1 hw)
  · exact intVectorCongruent_of_mem_same_integralResiduePacket
      ((mem_rankSevenPacketPointsOnSourceComponent_iff _ _ _).1 hz |>.1)
      ((mem_rankSevenPacketPointsOnSourceComponent_iff _ _ _).1 hw |>.1)

/-- Every point of a literal degree-one index lies in the original
normalized displacement box. -/
theorem rankSevenDegreeOnePointSet_coordinate_bound
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf)
    {z : IntVector 13}
    (hz : z ∈ rankSevenDegreeOnePointSet p x₀ equations CF Cchart model
      P k markCount hP hlower I X localEquations selectedVar menu markOf i) :
    ∀ j, (z j).natAbs ≤ 2 * surfaceTangentNaturalSide p := by
  have hzChart : z ∈
      depthSevenNormalizedJacobianChartCell p x₀ equations CF Cchart := by
    rcases i with (node | edge) | persistent
    · exact (mem_rankSevenNonSurfaceNodeRecordPointCell_iff
        p x₀ equations CF Cchart node.2.1 z).1 hz |>.1
    · exact (mem_rankSevenSurfaceEdgeFrontierPointCell_iff
        p x₀ equations CF Cchart P k edge.2.1.1 edge.2.2.1 z).1 hz |>.1
    · exact (mem_integralResiduePacket_iff.1
        ((mem_rankSevenPacketPointsOnSourceComponent_iff _ _ _).1 hz |>.1)).1
  exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
    p x₀ equations CF
      ((mem_depthSevenNormalizedJacobianChartCell_iff
        p x₀ equations CF Cchart z).1 hzChart |>.1)

/-- The tagged point type associated to the combined literal family. -/
abbrev RankSevenTaggedDegreeOnePoint
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
      MvPolynomial (Fin 14) ℚ) :=
  TaggedLinearContributionPoint
    (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k markCount
      hP hlower I X localEquations selectedVar menu markOf auxiliaryForm)
    (rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k markCount
      hP hlower I X localEquations selectedVar menu markOf)

/-- The corresponding tagged degree-one component occurrences.  Equal
geometric lines produced by different records remain different occurrences. -/
abbrev RankSevenTaggedLinearComponent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
      MvPolynomial (Fin 14) ℚ) :=
  TaggedLinearComponent
    (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k markCount
      hP hlower I X localEquations selectedVar menu markOf auxiliaryForm)

/-! ## Exact reindexing of the three displayed sums -/

/-- The combined tagged cardinality is exactly the sum of the node, actual
directed-edge, and persistent degree-one contributions. -/
theorem card_rankSevenTaggedDegreeOnePoint_eq_three_sums
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
      MvPolynomial (Fin 14) ℚ) :
    Fintype.card (RankSevenTaggedDegreeOnePoint p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm) =
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q,
          (finitePointsOnLinearCurveComponents
            (realProjectiveAffineChartIdeal record.component)
            (rankSevenNonSurfaceNodeRecordPointCell
              p x₀ equations CF Cchart record)).card) +
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (finitePointsOnLinearCurveComponents
              (realProjectiveAffineChartIdeal L)
              (rankSevenSurfaceEdgeFrontierPointCell
                p x₀ equations CF Cchart P k record L)).card) +
      ∑ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower X
            markCount localEquations selectedVar menu markOf,
        (finitePointsOnLinearCurveComponents
          (realAffineChartIntersectionIdeal I (auxiliaryForm record))
          (rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I)).card := by
  classical
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
      auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
  rw [card_taggedLinearContributionPoint J Y]
  simp only [RankSevenDegreeOneIndex, RankSevenNodeDegreeOneIndex,
    RankSevenEdgeDegreeOneIndex, RankSevenPersistentDegreeOneIndex,
    Fintype.sum_sum_type, Fintype.sum_sigma,
    J, Y, rankSevenDegreeOneIdeal,
    rankSevenDegreeOnePointSet]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Fintype.sum_congr
    intro q
    exact sum_subtype_mem_eq_sum
      (occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower q)
      (fun record ↦
        (finitePointsOnLinearCurveComponents
          (realProjectiveAffineChartIdeal record.component)
          (rankSevenNonSurfaceNodeRecordPointCell
            p x₀ equations CF Cchart record)).card)
  · apply Fintype.sum_congr
    intro qr
    let records := occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower
        qr.1.1 qr.1.2
    let term := fun (record : RankSevenEdgeRecord
        (Nat.lcm qr.1.1.1 qr.1.2.1)) (L : Ideal (MvPolynomial (Fin 14) ℚ)) ↦
      (finitePointsOnLinearCurveComponents
        (realProjectiveAffineChartIdeal L)
        (rankSevenSurfaceEdgeFrontierPointCell
          p x₀ equations CF Cchart P k record L)).card
    calc
      (∑ record : {record // record ∈ records},
          ∑ L : {L // L ∈ finiteMinimalPrimes
              (record.1.leftComponent ⊔ record.1.rightComponent)},
            term record.1 L.1) =
          ∑ record : {record // record ∈ records},
            ∑ L ∈ finiteMinimalPrimes
                (record.1.leftComponent ⊔ record.1.rightComponent),
              term record.1 L := by
        apply Fintype.sum_congr
        intro record
        exact sum_subtype_mem_eq_sum
          (finiteMinimalPrimes
            (record.1.leftComponent ⊔ record.1.rightComponent))
          (term record.1)
      _ = ∑ record ∈ records,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              term record L := by
        exact sum_subtype_mem_eq_sum records (fun record ↦
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            term record L)
  · exact sum_subtype_mem_eq_sum
      (occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower X
          markCount localEquations selectedVar menu markOf)
      (fun record ↦
        (finitePointsOnLinearCurveComponents
          (realAffineChartIntersectionIdeal I (auxiliaryForm record))
          (rankSevenPacketPointsOnSourceComponent
            (integralResiduePacket
              (depthSevenNormalizedJacobianChartCell
                p x₀ equations CF Cchart) record.residue) I)).card)

/-- The same exact reindexing for the line occurrences themselves.  In the
edge term the minimal-prime frontier `L` is retained as part of the tag. -/
theorem card_rankSevenTaggedLinearComponent_eq_three_sums
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
      MvPolynomial (Fin 14) ℚ) :
    Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm) =
      (∑ q : ReservoirModulus P k,
        ∑ record ∈ occupiedRankSevenSurvivingNonSurfaceNodeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower q,
          (linearAffineComponents
            (realProjectiveAffineChartIdeal record.component)).card) +
      (∑ qr : ↑(modulusReservoirDirectedEdges P k hP),
        ∑ record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
            p x₀ equations CF Cchart model.denominator P k hP hlower
              qr.1.1 qr.1.2,
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            (linearAffineComponents
              (realProjectiveAffineChartIdeal L)).card) +
      ∑ record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF Cchart model.denominator P k hP hlower X
            markCount localEquations selectedVar menu markOf,
        (linearAffineComponents
          (realAffineChartIntersectionIdeal I
            (auxiliaryForm record))).card := by
  classical
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
      auxiliaryForm
  rw [card_taggedLinearComponent J]
  simp only [RankSevenDegreeOneIndex, RankSevenNodeDegreeOneIndex,
    RankSevenEdgeDegreeOneIndex, RankSevenPersistentDegreeOneIndex,
    Fintype.sum_sum_type, Fintype.sum_sigma,
    J, rankSevenDegreeOneIdeal]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · apply Fintype.sum_congr
    intro q
    exact sum_subtype_mem_eq_sum
      (occupiedRankSevenSurvivingNonSurfaceNodeRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower q)
      (fun record ↦ (linearAffineComponents
        (realProjectiveAffineChartIdeal record.component)).card)
  · apply Fintype.sum_congr
    intro qr
    let records := occupiedRankSevenSurvivingSurfaceEdgeRecords
      p x₀ equations CF Cchart model.denominator P k hP hlower
        qr.1.1 qr.1.2
    let term := fun (record : RankSevenEdgeRecord
        (Nat.lcm qr.1.1.1 qr.1.2.1)) (L : Ideal (MvPolynomial (Fin 14) ℚ)) ↦
      (linearAffineComponents (realProjectiveAffineChartIdeal L)).card
    calc
      (∑ record : {record // record ∈ records},
          ∑ L : {L // L ∈ finiteMinimalPrimes
              (record.1.leftComponent ⊔ record.1.rightComponent)},
            term record.1 L.1) =
          ∑ record : {record // record ∈ records},
            ∑ L ∈ finiteMinimalPrimes
                (record.1.leftComponent ⊔ record.1.rightComponent),
              term record.1 L := by
        apply Fintype.sum_congr
        intro record
        exact sum_subtype_mem_eq_sum
          (finiteMinimalPrimes
            (record.1.leftComponent ⊔ record.1.rightComponent))
          (term record.1)
      _ = ∑ record ∈ records,
            ∑ L ∈ finiteMinimalPrimes
                (record.leftComponent ⊔ record.rightComponent),
              term record L := by
        exact sum_subtype_mem_eq_sum records (fun record ↦
          ∑ L ∈ finiteMinimalPrimes
              (record.leftComponent ⊔ record.rightComponent),
            term record L)
  · exact sum_subtype_mem_eq_sum
      (occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF Cchart model.denominator P k hP hlower X
          markCount localEquations selectedVar menu markOf)
      (fun record ↦ (linearAffineComponents
        (realAffineChartIntersectionIdeal I (auxiliaryForm record))).card)

/-! ## Literal high--low regrouping -/

/-- The active high--low ledger specialized to the exact node, edge, and
persistent tagged family above.  Its left side is definitionally the tagged
version of the three sums in
`card_rankSevenTaggedDegreeOnePoint_eq_three_sums`; no new set of points is
introduced. -/
theorem card_rankSevenTaggedDegreeOnePoint_le_active_high_low_ledger
    {Direction : Type*} [DecidableEq Direction]
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
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
    (lowDirections : Finset Direction)
    (direction : RankSevenTaggedDegreeOnePoint p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm → Direction)
    (highFibreBound lowFibreBound : ℕ)
    (hHighFibre : ∀ o : RankSevenTaggedLinearComponent p x₀ equations CF
        Cchart model P k markCount hP hlower I X localEquations selectedVar
          menu markOf auxiliaryForm,
      (activeHighTaggedLinearComponentFibre
        (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
          markCount hP hlower I X localEquations selectedVar menu markOf
            auxiliaryForm)
        (rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
          markCount hP hlower I X localEquations selectedVar menu markOf)
        lowDirections direction o).card ≤ highFibreBound)
    (hLowFibre : ∀ h ∈ lowDirections,
      ((activeTaggedLinearContributionPoints
        (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
          markCount hP hlower I X localEquations selectedVar menu markOf
            auxiliaryForm)
        (rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
          markCount hP hlower I X localEquations selectedVar menu markOf)).filter
        fun x ↦ direction x = h).card ≤ lowFibreBound) :
    Fintype.card (RankSevenTaggedDegreeOnePoint p x₀ equations CF Cchart
      model P k markCount hP hlower I X localEquations selectedVar menu
        markOf auxiliaryForm) ≤
      Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
        model P k markCount hP hlower I X localEquations selectedVar menu
          markOf auxiliaryForm) +
      Fintype.card (RankSevenTaggedLinearComponent p x₀ equations CF Cchart
        model P k markCount hP hlower I X localEquations selectedVar menu
          markOf auxiliaryForm) * highFibreBound +
        lowDirections.card * lowFibreBound := by
  exact taggedLinearContribution_card_le_active_high_low_ledger
    (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k markCount
      hP hlower I X localEquations selectedVar menu markOf auxiliaryForm)
    (rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k markCount
      hP hlower I X localEquations selectedVar menu markOf)
    lowDirections direction highFibreBound lowFibreBound hHighFibre hLowFibre

end

end TranslatedDepthSeven
