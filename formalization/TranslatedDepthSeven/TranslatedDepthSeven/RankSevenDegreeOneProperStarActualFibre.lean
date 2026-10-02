import TranslatedDepthSeven.RankSevenDegreeOneSelectedUnion
import TranslatedDepthSeven.RankSevenDegreeOneProperStarNonvertex

/-!
# The explicit star attached to an actual selected record fibre

This file specializes the selected-union correction to the literal
node--edge--persistent family.  A point is first counted only once in the
finite union and is then assigned one actual record tag.  For a fixed
projective direction, the resulting finite set maps injectively to its
underlying integral points and lies on one explicit projective star.

The statements here do not assume a grouped-fibre cardinality estimate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 16000000

/-- The star incidence for tagged points descends to the selected untagged
direction fibre. -/
theorem activeSelectedUnderlyingDirectionImage_subset_one_explicitStar
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (direction : TaggedLinearComponent J → IntVector 13)
    (hsource : ∀ o₀ ∈ activeTaggedLinearComponents J Y,
      ∀ x ∈ activeTaggedLinearContributionPoints J Y,
        taggedLinearPointProjectiveDirection J Y direction x =
            integralProjectiveClassOrFirstRankSeven (direction o₀) →
          ∃ hxne : integralAffineMap x₀ x.2.1 p.m ≠ 0,
            integralProjectiveClass
                (integralAffineMap x₀ x.2.1 p.m) hxne ∈
              integralProjectiveStarLocus equations degree (direction o₀))
    (o₀ : TaggedLinearComponent J)
    (ho₀ : o₀ ∈ activeTaggedLinearComponents J Y) :
    ∀ z ∈ activeSelectedUnderlyingDirectionImage J Y direction
        (integralProjectiveClassOrFirstRankSeven (direction o₀)),
      ∃ hz : integralAffineMap x₀ z p.m ≠ 0,
        integralProjectiveClass (integralAffineMap x₀ z p.m) hz ∈
          integralProjectiveStarLocus equations degree (direction o₀) := by
  classical
  intro z hz
  obtain ⟨hzUnion, hzActive, hzDirection⟩ :=
    (mem_activeSelectedUnderlyingDirectionImage_iff J Y direction
      (integralProjectiveClassOrFirstRankSeven (direction o₀)) z).1 hz
  let z' : {w // w ∈ underlyingLinearContributionPoints J Y} :=
    ⟨z, hzUnion⟩
  have htagActive : selectedTaggedLinearContributionPoint J Y z' ∈
      activeTaggedLinearContributionPoints J Y :=
    selectedTaggedLinearContributionPoint_mem_active J Y z' hzActive
  have htagDirection :
      taggedLinearPointProjectiveDirection J Y direction
          (selectedTaggedLinearContributionPoint J Y z') =
        integralProjectiveClassOrFirstRankSeven (direction o₀) := by
    simpa only [selectedUnderlyingProjectiveDirection, z'] using hzDirection
  obtain ⟨hne, hstar⟩ := hsource o₀ ho₀
    (selectedTaggedLinearContributionPoint J Y z') htagActive htagDirection
  have hvalue : (selectedTaggedLinearContributionPoint J Y z').2.1 = z :=
    selectedTaggedLinearContributionPoint_value J Y z'
  rw [← hvalue]
  exact ⟨hne, hstar⟩

/-- Literal specialization to the actual node, edge, and persistent record
cells.  Every fibre point is normalized, is in the original translated box,
and is a zero of the rational ideal of the displayed star. -/
theorem exists_rankSevenDegreeOne_actual_selected_fibres_in_one_star
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF Cchart model.denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ) :
    let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
      markCount hP hlower I X localEquations selectedVar menu markOf
        auxiliaryForm
    let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
      markCount hP hlower I X localEquations selectedVar menu markOf
    ∃ (base direction : TaggedLinearComponent J → IntVector 13)
      (parameter : TaggedLinearComponent J → IntVector 13 → ℤ),
      (∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1),
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ ↦
            fun i ↦ (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        (∀ t : ℤ, IntegralCommonZero equations
          (integralAffineMap x₀
            (fun i ↦ base o i + t * direction o i) p.m)) ∧
        IntegralCommonZero equations (direction o)) ∧
      ∀ o₀ ∈ activeTaggedLinearComponents J Y,
        let h := integralProjectiveClassOrFirstRankSeven (direction o₀)
        let Z := activeSelectedUnderlyingDirectionImage J Y direction h
        Z.card =
            (activeSelectedUnderlyingDirectionFibre J Y direction h).card ∧
          Z ⊆ depthSevenNormalizedDisplacementFinset
            p x₀ equations CF ∧
          (∀ z ∈ Z, ∀ i,
            (z i).natAbs ≤ 2 * surfaceTangentNaturalSide p) ∧
          ∀ z ∈ Z,
            (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
              affineIdealZeroLocus
                (rationalProjectiveStarIdeal equations degree
                  (direction o₀)) := by
  classical
  dsimp only
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
  obtain ⟨base, direction, parameter, hfull, hsource⟩ :=
    exists_rankSevenDegreeOne_actual_fibres_in_one_explicitStar
      hline p x₀ equations CF degree hdegree Cchart model P k markCount hP
        hlower I X hX localEquations selectedVar menu markOf auxiliaryForm
  refine ⟨base, direction, parameter, hfull, ?_⟩
  intro o₀ ho₀
  let h := integralProjectiveClassOrFirstRankSeven (direction o₀)
  let Z := activeSelectedUnderlyingDirectionImage J Y direction h
  have hstarProjective : ∀ z ∈ Z,
      ∃ hz : integralAffineMap x₀ z p.m ≠ 0,
        integralProjectiveClass (integralAffineMap x₀ z p.m) hz ∈
          integralProjectiveStarLocus equations degree (direction o₀) :=
    activeSelectedUnderlyingDirectionImage_subset_one_explicitStar
      p x₀ equations degree J Y direction hsource o₀ ho₀
  refine ⟨card_activeSelectedUnderlyingDirectionImage J Y direction h,
    ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzUnion, hzActive, _hzDirection⟩ :=
      (mem_activeSelectedUnderlyingDirectionImage_iff J Y direction h z).1 hz
    let z' : {w // w ∈ underlyingLinearContributionPoints J Y} :=
      ⟨z, hzUnion⟩
    let x := selectedTaggedLinearContributionPoint J Y z'
    have hxActive : x ∈ activeTaggedLinearContributionPoints J Y :=
      selectedTaggedLinearContributionPoint_mem_active J Y z' hzActive
    have hxY : x.2.1 ∈ Y x.1 :=
      finitePointsOnLinearCurveComponents_subset (J x.1) (Y x.1) x.2.2
    have hxNormalized := rankSevenDegreeOnePointSet_mem_normalizedDisplacement
      p x₀ equations CF Cchart model P k markCount hP hlower I X
        localEquations selectedVar menu markOf x.1 hxY
    have hvalue : x.2.1 = z :=
      selectedTaggedLinearContributionPoint_value J Y z'
    simpa only [hvalue] using hxNormalized
  · intro z hz i
    have hzNormalized : z ∈ depthSevenNormalizedDisplacementFinset
        p x₀ equations CF := by
      exact (show Z ⊆ depthSevenNormalizedDisplacementFinset
        p x₀ equations CF from by
          intro w hw
          obtain ⟨hwUnion, hwActive, _⟩ :=
            (mem_activeSelectedUnderlyingDirectionImage_iff
              J Y direction h w).1 hw
          let w' : {u // u ∈ underlyingLinearContributionPoints J Y} :=
            ⟨w, hwUnion⟩
          let x := selectedTaggedLinearContributionPoint J Y w'
          have hxY : x.2.1 ∈ Y x.1 :=
            finitePointsOnLinearCurveComponents_subset
              (J x.1) (Y x.1) x.2.2
          have hxNormalized :=
            rankSevenDegreeOnePointSet_mem_normalizedDisplacement
              p x₀ equations CF Cchart model P k markCount hP hlower I X
                localEquations selectedVar menu markOf x.1 hxY
          have hvalue : x.2.1 = w :=
            selectedTaggedLinearContributionPoint_value J Y w'
          simpa only [hvalue] using hxNormalized) hz
    exact depthSevenNormalized_coordinate_le_two_surfaceTangentNaturalSide
      p x₀ equations CF hzNormalized i
  · intro z hz
    obtain ⟨hne, hstar⟩ := hstarProjective z hz
    exact rationalVector_mem_rationalProjectiveStarIdeal_zeroLocus
      equations degree hdegree (direction o₀)
        (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ))
        (intCast_ne_zero hne) (by
          simpa only [integralProjectiveClass] using hstar)

end

end TranslatedDepthSeven
