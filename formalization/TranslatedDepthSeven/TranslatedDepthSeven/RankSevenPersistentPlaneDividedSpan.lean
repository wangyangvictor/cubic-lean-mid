import TranslatedDepthSeven.RankSevenPersistentPlaneAssignedCells
import TranslatedDepthSeven.RankTwoIntegralSpan

/-!
# The rational span of the actual divided differences

The divisor is the positive modulus of the retained occurrence. Thus the
rational span is exactly the span used to define the assigned difference
rank, not a replacement plane supplied as a hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

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

local notation "assignedCell" =>
  rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "planeBase" =>
  rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "dividedDifference" =>
  rankSevenPersistentPlaneDividedDifference p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

theorem rankSevenPersistentPlaneDividedDifference_span_eq
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence) :
    Submodule.span ℚ (Set.range fun
        z : {z // z ∈ assignedCell planePoints recordOf o} ↦
          fun i ↦ (dividedDifference o z.1 i : ℚ)) =
      Submodule.span ℚ (Set.range fun
        z : {z // z ∈ assignedCell planePoints recordOf o} ↦
          rationalIntegralDifference (planeBase o) z.1) := by
  let v := fun z : {z // z ∈ assignedCell planePoints recordOf o} ↦
    fun i ↦ (dividedDifference o z.1 i : ℚ)
  have hq : (rankSevenPersistentPlaneModulus o : ℚ) ≠ 0 := by
    exact_mod_cast (rankSevenPersistentPlaneModulus_pos p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf o).ne'
  have hfamily :
      (fun z : {z // z ∈ assignedCell planePoints recordOf o} ↦
        rationalIntegralDifference (planeBase o) z.1) =
      (fun z ↦ (rankSevenPersistentPlaneModulus o : ℚ) • v z) := by
    funext z i
    have hz := rankSevenPersistentPlaneAssignedCell_subset_oldCell
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf planePoints recordOf hrecordOf o z.2
    have hspec := rankSevenPersistentPlaneDividedDifference_spec
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf o hz i
    have hdiff : z.1 i - planeBase o i =
        (rankSevenPersistentPlaneModulus o : ℤ) * dividedDifference o z.1 i := by
      linarith
    simp only [rationalIntegralDifference, Pi.smul_apply, smul_eq_mul, v]
    exact_mod_cast hdiff
  rw [hfamily]
  exact (span_range_smul_eq_of_ne_zero v _ hq).symm

end LiteralFamily

end

end TranslatedDepthSeven
