import TranslatedDepthSeven.RankSevenPersistentPlaneRecords
import TranslatedDepthSeven.ExplicitLineContribution
import TranslatedDepthSeven.PrimitiveTerminalLedger

/-!
# Disjoint assigned cells for persistent plane occurrences

The broad cell attached to a persistent record need not be disjoint from the
broad cell attached to another record.  Counting the same point once for
each compatible record would destroy the rank-two regrouping by direction.
This file therefore fixes the literal point set under study and one actual
record occurrence for each of its points.  The assigned cell of an
occurrence is the corresponding fibre.  These cells are disjoint by
definition, while the hypothesis `hrecordOf` certifies that each is a subset
of its old record cell and hence retains the record's modulus and residue.

Ranks are taken from differences in these assigned cells. Rank zero gives
at most one point. The primitive rank-one line and its full incidence are
proved separately in `RankSevenPersistentPlaneRankOne`; no primitive-
parametrization assumption is introduced here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

local instance assignedPlanePropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

set_option maxHeartbeats 6000000

section LiteralFamily

variable (p : Parameters) (x₀ : IntVector 13)
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

local notation "PlaneOccurrence" =>
  RankSevenPersistentPlaneOccurrence p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "oldCell" =>
  rankSevenPersistentPlanePointCell p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "oldBase" =>
  rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
    P k hP hlower X markCount localEquations selectedVar menu markOf

/-- The disjoint fibre of a pointwise choice of literal plane occurrence. -/
def rankSevenPersistentPlaneAssignedCell
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (o : PlaneOccurrence) : Finset (IntVector 13) :=
  planePoints.filter fun z ↦ recordOf z = o

@[simp]
theorem mem_rankSevenPersistentPlaneAssignedCell_iff
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (o : PlaneOccurrence) (z : IntVector 13) :
    z ∈ rankSevenPersistentPlaneAssignedCell p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf o ↔
      z ∈ planePoints ∧ recordOf z = o := by
  classical
  simp [rankSevenPersistentPlaneAssignedCell]

/-- The fibres of `recordOf` are pairwise disjoint. -/
theorem rankSevenPersistentPlaneAssignedCell_disjoint
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    {o₁ o₂ : PlaneOccurrence} (hne : o₁ ≠ o₂) :
    Disjoint
      (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf
          planePoints recordOf o₁)
      (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf
          planePoints recordOf o₂) := by
  classical
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  have h₁ := (mem_rankSevenPersistentPlaneAssignedCell_iff p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf
      planePoints recordOf o₁ z).mp hz₁ |>.2
  have h₂ := (mem_rankSevenPersistentPlaneAssignedCell_iff p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf
      planePoints recordOf o₂ z).mp hz₂ |>.2
  exact hne (h₁.symm.trans h₂)

/-- The assigned cells cover the literal point set exactly. -/
theorem rankSevenPersistentPlaneAssignedCell_biUnion_eq
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence) :
    (Finset.univ : Finset PlaneOccurrence).biUnion
        (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
          P k hP hlower X markCount localEquations selectedVar menu markOf
            planePoints recordOf) = planePoints := by
  classical
  ext z
  simp [rankSevenPersistentPlaneAssignedCell]

/-- An assignment is genuine when every selected occurrence's old cell
contains the point.  This is the only compatibility condition imposed on
the pointwise choice. -/
def IsLiteralPersistentPlaneAssignment
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence) : Prop :=
  ∀ z ∈ planePoints, z ∈ oldCell (recordOf z)

theorem rankSevenPersistentPlaneAssignedCell_subset_oldCell
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence) :
    rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator P k
        hP hlower X markCount localEquations selectedVar menu markOf planePoints
          recordOf o ⊆ oldCell o := by
  intro z hz
  have hz' := (mem_rankSevenPersistentPlaneAssignedCell_iff p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf
      planePoints recordOf o z).mp hz
  simpa [hz'.2] using hrecordOf z hz'.1

/-- Rational rank of the differences in one disjoint assigned cell, measured
from the integral representative already attached to the actual record. -/
def rankSevenPersistentPlaneAssignedDifferenceRank
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (o : PlaneOccurrence) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ (Set.range fun
      z : {z // z ∈ rankSevenPersistentPlaneAssignedCell p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf o} ↦
        rationalIntegralDifference (oldBase o) z.1))

/-- Restricting the old cell to a disjoint assigned fibre cannot increase
the difference rank. -/
theorem rankSevenPersistentPlaneAssignedDifferenceRank_le_old
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence) :
    rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf o ≤
      rankSevenPersistentPlaneDifferenceRank p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf o := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro v ⟨z, rfl⟩
  refine ⟨⟨z.1, ?_⟩, rfl⟩
  exact rankSevenPersistentPlaneAssignedCell_subset_oldCell p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf
      planePoints recordOf hrecordOf o z.2

/-- Every disjoint assigned plane cell has rank zero, one, or two. -/
theorem rankSevenPersistentPlaneAssignedDifferenceRank_le_two
    (hplane : StandardAG.DegreeOneProjectiveSurfaceDifferenceRank)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence) :
    rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf o ≤ 2 :=
  (rankSevenPersistentPlaneAssignedDifferenceRank_le_old p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu markOf
      planePoints recordOf hrecordOf o).trans
    (rankSevenPersistentPlaneDifferenceRank_le_two hplane p x₀ equations CF
      hhomogeneous C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o)

/-- The rank-zero, rank-one, and rank-two occurrence sets are literal
filters of the actual plane occurrences. -/
def rankSevenPersistentPlaneOccurrencesOfRank
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence) (r : ℕ) :
    Finset PlaneOccurrence :=
  Finset.univ.filter fun o ↦
    rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf o = r

@[simp]
theorem mem_rankSevenPersistentPlaneOccurrencesOfRank_iff
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence) (r : ℕ)
    (o : PlaneOccurrence) :
    o ∈ rankSevenPersistentPlaneOccurrencesOfRank p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf r ↔
      rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf o = r := by
  classical
  simp [rankSevenPersistentPlaneOccurrencesOfRank]

/-- Rank zero contains at most one assigned point. -/
theorem rankSevenPersistentPlaneAssignedCell_card_le_one_of_rank_zero
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (o : PlaneOccurrence)
    (hrank : rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf o = 0) :
    (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator P k
      hP hlower X markCount localEquations selectedVar menu markOf planePoints
        recordOf o).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro z hz w hw
  let S := rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
    P k hP hlower X markCount localEquations selectedVar menu markOf planePoints
      recordOf o
  let base := oldBase o
  let V : Submodule ℚ (Fin 13 → ℚ) :=
    Submodule.span ℚ (Set.range fun u : {u // u ∈ S} ↦
      rationalIntegralDifference base u.1)
  have hV : V = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    simpa only [rankSevenPersistentPlaneAssignedDifferenceRank, S, base, V]
      using hrank
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

/-- The total rank-zero contribution is at most the number of actual plane
occurrences.  There is no multiplicity from overlapping broad cells because
the assigned cells are fibres of `recordOf`. -/
theorem sum_rankZero_rankSevenPersistentPlaneAssignedCells_le_occurrences
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence) :
    ∑ o ∈ rankSevenPersistentPlaneOccurrencesOfRank p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf 0,
      (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
        P k hP hlower X markCount localEquations selectedVar menu markOf
          planePoints recordOf o).card ≤
      Fintype.card PlaneOccurrence := by
  classical
  calc
    ∑ o ∈ rankSevenPersistentPlaneOccurrencesOfRank p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf planePoints recordOf 0,
        (rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator
          P k hP hlower X markCount localEquations selectedVar menu markOf
            planePoints recordOf o).card ≤
        ∑ _o ∈ rankSevenPersistentPlaneOccurrencesOfRank p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf planePoints recordOf 0, 1 := by
      apply Finset.sum_le_sum
      intro o ho
      apply rankSevenPersistentPlaneAssignedCell_card_le_one_of_rank_zero
        p x₀ equations CF C denominator P k hP hlower X markCount
          localEquations selectedVar menu markOf planePoints recordOf o
      exact (mem_rankSevenPersistentPlaneOccurrencesOfRank_iff p x₀ equations CF C
        denominator P k hP hlower X markCount localEquations selectedVar menu
          markOf planePoints recordOf 0 o).mp ho
    _ = (rankSevenPersistentPlaneOccurrencesOfRank p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf planePoints recordOf 0).card := by simp
    _ ≤ (Finset.univ : Finset PlaneOccurrence).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card PlaneOccurrence := Finset.card_univ

end LiteralFamily

end

end TranslatedDepthSeven
