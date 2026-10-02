import TranslatedDepthSeven.RankSevenPersistentMultiplicityOneRecordCover
import TranslatedDepthSeven.RankSevenRecordOccurrenceScale
import TranslatedDepthSeven.RankSevenRecordPila
import TranslatedDepthSeven.IntegralPacketSpanBasis
import TranslatedDepthSeven.NormalizedReservoirQuotientSide
import TranslatedDepthSeven.RankSevenEdgeFrontierGeometry

/-!
# Literal persistent degree-one surface records

The persistent branch already carries an actual reservoir modulus, residue,
projective component, mark, and finite point cell.  This file takes the
literal subfamily for which the recorded component is a projective surface
of degree one.  Nothing is replaced by an abstract plane count: every
definition below is a filter of the existing record family.

For each such record we choose a point of its nonempty cell and define the
rational rank of all differences from that point.  The record modulus is
kept visible.  Hence the integral divided differences are also available,
with their exact congruence identity and the canonical `T^(2/7)` coordinate
bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance persistentPlanePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

set_option maxHeartbeats 4000000

/-- The retained persistent records whose actual projective component has
projective dimension two and degree one. -/
def occupiedRankSevenPersistentPlaneRecords
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    Finset (RankSevenPersistentRecord P k markCount) :=
  (occupiedRankSevenPersistentMultiplicityOneRecords
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf).filter fun record ↦
        HasProjectiveDimensionDegree record.component 2 1

@[simp]
theorem mem_occupiedRankSevenPersistentPlaneRecords_iff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (record : RankSevenPersistentRecord P k markCount) :
    record ∈ occupiedRankSevenPersistentPlaneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf ↔
      record ∈ occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf ∧
      HasProjectiveDimensionDegree record.component 2 1 := by
  classical
  simp [occupiedRankSevenPersistentPlaneRecords]

/-- A literal plane occurrence is a member of the preceding finite set.
The subtype retains the complete record, in particular its modulus and
residue. -/
def RankSevenPersistentPlaneOccurrence
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :=
  {record // record ∈ occupiedRankSevenPersistentPlaneRecords
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf}

instance rankSevenPersistentPlaneOccurrenceFintype
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    Fintype (RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) := by
  classical
  unfold RankSevenPersistentPlaneOccurrence
  exact Fintype.ofFinset _ (fun _ ↦ Iff.rfl)

/-- The exact old point cell attached to a plane occurrence. -/
def rankSevenPersistentPlanePointCell
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) : Finset (IntVector 13) :=
  rankSevenPersistentRecordPointCell p x₀ equations CF C markOf o.1

/-- Every retained plane occurrence has a nonempty literal point cell. -/
theorem rankSevenPersistentPlanePointCell_nonempty
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    (rankSevenPersistentPlanePointCell p x₀ equations CF C denominator
      P k hP hlower X markCount localEquations selectedVar menu markOf o).Nonempty := by
  have hrecord :=
    (mem_occupiedRankSevenPersistentPlaneRecords_iff
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf o.1).mp o.2 |>.1
  obtain ⟨z, hz⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf o.1 hrecord
  exact ⟨z,
    (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
      p x₀ equations CF C denominator P k hP hlower X
        localEquations selectedVar menu markOf o.1 z).mp hz |>.1⟩

/-- The representative is selected from the occurrence's actual cell. -/
def rankSevenPersistentPlaneRepresentative
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) : IntVector 13 :=
  Classical.choose (rankSevenPersistentPlanePointCell_nonempty
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o)

theorem rankSevenPersistentPlaneRepresentative_mem
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf o ∈
      rankSevenPersistentPlanePointCell p x₀ equations CF C denominator P k
        hP hlower X markCount localEquations selectedVar menu markOf o :=
  Classical.choose_spec (rankSevenPersistentPlanePointCell_nonempty
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o)

/-- The actual modulus retained by a plane occurrence. -/
def rankSevenPersistentPlaneModulus
    {p : Parameters} {x₀ : IntVector 13}
    {equations : Finset (MvPolynomial (Fin 13) ℤ)} {CF : ℕ}
    {C : IntegralDepthSevenJacobianChartIndex equations}
    {denominator : ℤ} {P : Finset ℕ} {k : ℕ}
    {hP : ∀ s ∈ P, s.Prime}
    {hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1}
    {X : Finset (IntVector 13)} {markCount : ℕ}
    {localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ}
    {selectedVar : Fin 11 → Fin 13}
    {menu : Fin markCount → MvPolynomial (Fin 13) ℤ}
    {markOf : IntVector 13 → Fin markCount}
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) : ℕ :=
  o.1.modulus.1

theorem rankSevenPersistentPlaneModulus_pos
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    0 < rankSevenPersistentPlaneModulus o :=
  reservoirModulus_pos hP o.1.modulus

theorem rankSevenPersistentPlaneModulus_lower
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ rankSevenPersistentPlaneModulus o :=
  hlower o.1.modulus

/-- All points in one plane occurrence are congruent modulo its retained
modulus. -/
theorem rankSevenPersistentPlanePointCell_pair_congruent
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    {z w : IntVector 13}
    (hz : z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o)
    (hw : w ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o) :
    IntVectorCongruent (rankSevenPersistentPlaneModulus o) z w := by
  intro i
  have hzres := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf o.1 z).mp hz |>.2.1
  have hwres := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf o.1 w).mp hw |>.2.1
  exact congrFun (hzres.trans hwres.symm) i

/-- The integral divided difference from the selected representative. -/
def rankSevenPersistentPlaneDividedDifference
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    (z : IntVector 13) : IntVector 13 :=
  congruenceDisplacementOrZero (rankSevenPersistentPlaneModulus o)
    (rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
      P k hP hlower X markCount localEquations selectedVar menu markOf o) z

/-- Exact reconstruction from the retained modulus and divided difference. -/
theorem rankSevenPersistentPlaneDividedDifference_spec
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    {z : IntVector 13}
    (hz : z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o) (i : Fin 13) :
    z i =
      rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
          P k hP hlower X markCount localEquations selectedVar menu markOf o i +
        rankSevenPersistentPlaneModulus o *
          rankSevenPersistentPlaneDividedDifference p x₀ equations CF C
            denominator P k hP hlower X markCount localEquations selectedVar
              menu markOf o z i := by
  apply congruenceDisplacementOrZero_spec
  exact rankSevenPersistentPlanePointCell_pair_congruent
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o hz
      (rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf o)

/-- The divided differences have the canonical residual side
`2*T^(2/7)`. -/
theorem rankSevenPersistentPlaneDividedDifference_bound
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    {z : IntVector 13}
    (hz : z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o) (i : Fin 13) :
    |(rankSevenPersistentPlaneDividedDifference p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o z i : ℝ)| < 2 * p.T ^ (2 / 7 : ℝ) := by
  let Z := depthSevenNormalizedJacobianChartCell p x₀ equations CF C
  let rho := o.1.residue
  have hrho : rho ∈ occupiedIntegralResidues o.1.modulus.1 Z :=
    (mem_occupiedRankSevenPersistentRecords_iff
      p x₀ equations CF C P k markCount o.1).mp
        ((mem_occupiedRankSevenPersistentPlaneRecords_iff
          p x₀ equations CF C denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf o.1).mp o.2 |>.1 |>
          (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
            p x₀ equations CF C denominator P k markCount hP hlower X
              localEquations selectedVar menu markOf o.1).mp |>.1) |>.1
  have hzPacket : z ∈ integralResiduePacket Z rho :=
    (mem_integralResiduePacket_iff).2 ⟨
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf o.1 z).mp hz |>.1,
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf o.1 z).mp hz |>.2.1⟩
  have hbasePacket :
      rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
          P k hP hlower X markCount localEquations selectedVar menu markOf o ∈
        integralResiduePacket Z rho :=
    (mem_integralResiduePacket_iff).2 ⟨
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf o.1 _).mp
          (rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
            denominator P k hP hlower X markCount localEquations selectedVar menu
              markOf o) |>.1,
      (mem_rankSevenPersistentRecordPointCell_iff
        p x₀ equations CF C markOf o.1 _).mp
          (rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
            denominator P k hP hlower X markCount localEquations selectedVar menu
              markOf o) |>.2.1⟩
  have hqpos := rankSevenPersistentPlaneModulus_pos
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o
  have hraw := congruenceDisplacementOrZero_coordinate_bound hqpos
    (rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
      P k hP hlower X markCount localEquations selectedVar menu markOf o) z
    (rankSevenPersistentPlanePointCell_pair_congruent
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf o hz
        (rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf o))
    (center := fun _ ↦ 0) (R := 2 * surfaceTangentNaturalSide p)
    (by
      intro j
      simpa using depthSevenNormalizedChartResiduePacket_realBox_anyModulus
        p x₀ equations CF C o.1.modulus.1 rho z hzPacket j)
    (by
      intro j
      simpa using depthSevenNormalizedChartResiduePacket_realBox_anyModulus
        p x₀ equations CF C o.1.modulus.1 rho _ hbasePacket j) i
  have hside :
      2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) /
          rankSevenPersistentPlaneModulus o <
        1 + (4 * surfaceTangentNaturalSide p : ℝ) /
          rankSevenPersistentPlaneModulus o := by
    have heq :
        2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) /
            rankSevenPersistentPlaneModulus o =
          (4 * surfaceTangentNaturalSide p : ℝ) /
            rankSevenPersistentPlaneModulus o := by
      push_cast
      ring
    rw [heq]
    linarith
  have hcanonical := normalizedReservoirQuotientSide_le_two_rpow p
    (rankSevenPersistentPlaneModulus o)
    (rankSevenPersistentPlaneModulus_lower p x₀ equations CF C denominator
      P k hP hlower X markCount localEquations selectedVar menu markOf o)
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (by
      simpa [rankSevenPersistentPlaneDividedDifference] using hraw) hside)
    hcanonical

/-- The rational rank of the occurrence is the rank of the literal family
of differences from its selected point. -/
def rankSevenPersistentPlaneDifferenceRank
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ (Set.range fun
      z : {z // z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf o} ↦
        rationalIntegralDifference
          (rankSevenPersistentPlaneRepresentative p x₀ equations CF C
            denominator P k hP hlower X markCount localEquations selectedVar
              menu markOf o) z.1))

namespace StandardAG

/-- The only degree-one classification used by the packet-rank argument.
An integral projective surface of degree one is a projective plane; consequently the
rational differences of any finite set in its standard affine chart span a
space of dimension at most two.  This statement contains no arithmetic or
point-count estimate. -/
def DegreeOneProjectiveSurfaceDifferenceRank : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree I 2 1 →
    ∀ (S : Finset (IntVector N)) (base : IntVector N), base ∈ S →
      (∀ z ∈ S,
        (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
          affineIdealZeroLocus I) →
      Module.finrank ℚ
        (Submodule.span ℚ
          (Set.range fun z : {z // z ∈ S} ↦
            rationalIntegralDifference base z.1)) ≤ 2

end StandardAG

/-- The literal difference rank is at most two. -/
theorem rankSevenPersistentPlaneDifferenceRank_le_two
    (hplane : StandardAG.DegreeOneProjectiveSurfaceDifferenceRank)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf) :
    rankSevenPersistentPlaneDifferenceRank p x₀ equations CF C denominator
      P k hP hlower X markCount localEquations selectedVar menu markOf o ≤ 2 := by
  have hplaneRecord := (mem_occupiedRankSevenPersistentPlaneRecords_iff
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf o.1).mp o.2
  have hretained := (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf o.1).mp hplaneRecord.1 |>.1
  have hsurface := (mem_occupiedRankSevenPersistentRecords_iff
    p x₀ equations CF C P k markCount o.1).mp hretained |>.2
  have hnode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C o.1.modulus.1 o.1.residue o.1.component).mp hsurface |>.1
  apply hplane 13 o.1.component
  · exact rankSevenNodeComponent_isPrime p x₀ equations CF C
      o.1.modulus.1 o.1.residue o.1.component hnode
  · exact rankSevenNodeComponent_isHomogeneous p x₀ equations CF hhomogeneous C
      o.1.modulus.1 o.1.residue o.1.component hnode
  · exact hplaneRecord.2
  · exact rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o
  · intro z hz
    exact (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf o.1 z).mp hz |>.2.2.1

/-- Rank zero gives at most one integral point in the literal occurrence
cell. -/
theorem rankSevenPersistentPlanePointCell_card_le_one_of_rank_zero
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    (hrank : rankSevenPersistentPlaneDifferenceRank p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o = 0) :
    (rankSevenPersistentPlanePointCell p x₀ equations CF C denominator P k
      hP hlower X markCount localEquations selectedVar menu markOf o).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro z hz w hw
  let S := rankSevenPersistentPlanePointCell p x₀ equations CF C denominator
    P k hP hlower X markCount localEquations selectedVar menu markOf o
  let base := rankSevenPersistentPlaneRepresentative p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf o
  let V : Submodule ℚ (Fin 13 → ℚ) :=
    Submodule.span ℚ (Set.range fun u : {u // u ∈ S} ↦
      rationalIntegralDifference base u.1)
  have hV : V = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    simpa only [rankSevenPersistentPlaneDifferenceRank, S, base, V] using hrank
  change z ∈ S at hz
  change w ∈ S at hw
  have hzV : rationalIntegralDifference base z ∈ V := by
    apply Submodule.subset_span
    exact ⟨⟨z, hz⟩, rfl⟩
  have hwV : rationalIntegralDifference base w ∈ V := by
    apply Submodule.subset_span
    exact ⟨⟨w, hw⟩, rfl⟩
  have hzZero : rationalIntegralDifference base z = 0 := by
    rw [hV] at hzV
    simpa using hzV
  have hwZero : rationalIntegralDifference base w = 0 := by
    rw [hV] at hwV
    simpa using hwV
  funext i
  have hzi := congrFun hzZero i
  have hwi := congrFun hwZero i
  simp only [rationalIntegralDifference, Pi.zero_apply, Int.cast_eq_zero] at hzi hwi
  omega

/-- Rank two supplies two actual points and two coordinates on which their
difference vectors have nonzero determinant.  This is the explicit
independence datum used by the bounded smooth-direction selection. -/
theorem exists_rankSevenPersistentPlane_independent_differences_of_rank_two
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (o : RankSevenPersistentPlaneOccurrence
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf)
    (hrank : rankSevenPersistentPlaneDifferenceRank p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o = 2) :
    ∃ rows : Fin 2 →
        {z // z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf o},
      ∃ cols : Fin 2 → Fin 13,
        Function.Injective rows ∧ Function.Injective cols ∧
          Matrix.det (Matrix.of fun i j ↦
            rationalIntegralDifference
              (rankSevenPersistentPlaneRepresentative p x₀ equations CF C
                denominator P k hP hlower X markCount localEquations selectedVar
                  menu markOf o) (rows i).1 (cols j)) ≠ 0 := by
  let v := fun z :
      {z // z ∈ rankSevenPersistentPlanePointCell p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf o} ↦
    rationalIntegralDifference
      (rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf o) z.1
  apply TangentPacketSpan.exists_nonzero_minor_of_finrank_span_ge v
  simpa only [rankSevenPersistentPlaneDifferenceRank, v] using hrank.ge

/-- The plane subfamily has no more occurrences than the retained record
family from which it was literally filtered. -/
theorem card_occupiedRankSevenPersistentPlaneRecords_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13)) (markCount : ℕ)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    (occupiedRankSevenPersistentPlaneRecords
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf).card ≤
      (occupiedRankSevenPersistentMultiplicityOneRecords
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf).card :=
  Finset.card_filter_le _ _

/-- The literal plane-occurrence count inherits the exact reservoir scale
of the retained records. -/
theorem card_occupiedRankSevenPersistentPlaneRecords_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount D : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (hcomponents : ∀ (q : ReservoirModulus P k)
        (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell p x₀ equations CF C) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF C q.1 rho).card ≤ D)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir P k).card +
      (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupper : ∀ q : ReservoirModulus P k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (5 / 7 : ℝ) * p.H ^ δ) :
    ((occupiedRankSevenPersistentPlaneRecords
      p x₀ equations CF C model.denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf).card : ℝ) ≤
      2 * C₀ ^ 6 * (D * markCount) * p.T ^ (30 / 7 : ℝ) *
        p.H ^ (8 * δ) := by
  have hsub := card_occupiedRankSevenPersistentPlaneRecords_le
    p x₀ equations CF C model.denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf
  have hsubReal :
      ((occupiedRankSevenPersistentPlaneRecords
        p x₀ equations CF C model.denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf).card : ℝ) ≤
        ((occupiedRankSevenPersistentMultiplicityOneRecords
          p x₀ equations CF C model.denominator P k hP hlower X markCount
            localEquations selectedVar menu markOf).card : ℝ) := by
    exact_mod_cast hsub
  exact hsubReal.trans
    (card_occupiedRankSevenPersistentMultiplicityOneRecords_cast_le_scale
      hM₀ hδ hC₀ p x₀ equations CF C model P k markCount D hP hlower X
        localEquations selectedVar menu markOf hcomponents hk hH hfamily hupper)

end

end TranslatedDepthSeven
