import TranslatedDepthSeven.QuantitativePrefixPersistentCellAggregation
import TranslatedDepthSeven.RankSevenDegreeOneSelectedUnionLedger

/-!
# The literal line ledger for quantitative persistent prefix cells

The persistent prefix partition is indexed by geometric component labels over
`Qbar`, but its terminal cuts and all affine intersection ideals are rational.
This file connects its literal affine-progression line union to the existing
multiplicity-free selected-union ledger.  The number of tagged line
occurrences is derived from the rational surface--hypersurface Bezout theorem;
it is not an additional family-count hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

local instance quantitativePrefixLineLedgerPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The literal line union left by quantitative prefix aggregation is the
standard multiplicity-free underlying union on the subtype of active geometric
labels.  Although the labels are over `Qbar`, the ideals in this union remain
the rational terminal intersection ideals. -/
theorem quantitativePrefixPersistentLinearPointUnion_eq_underlying
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) :
    quantitativePrefixPersistentLinearPointUnion I active terminalCut
        u m cell =
      underlyingLinearContributionPoints
        (fun o : {o // o ∈ active} =>
          realAffineChartIntersectionIdeal I (terminalCut o.1))
        (fun o : {o // o ∈ active} =>
          quantitativePrefixPersistentAffineCell u m cell o.1) := by
  classical
  rw [underlyingLinearContributionPoints_eq_biUnion]
  ext z
  simp [quantitativePrefixPersistentLinearPointUnion]

/-- Bezout bounds the tagged degree-one occurrences attached to Qbar-labelled
persistent cells.  Only the label type changed: each terminal cut and affine
component list is still rational. -/
theorem card_quantitativePrefixPersistent_taggedLines_le
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {d K : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : X (0 : Fin 4) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ I ∧ terminalDegree o ≤ K) :
    Fintype.card (TaggedLinearComponent
      (fun o : {o // o ∈ active} =>
        realAffineChartIntersectionIdeal I (terminalCut o.1))) ≤
      active.card * (d * K) := by
  classical
  rw [card_taggedLinearComponent]
  calc
    (∑ o : {o // o ∈ active},
        (linearAffineComponents
          (realAffineChartIntersectionIdeal I (terminalCut o.1))).card) ≤
      ∑ _o : {o // o ∈ active}, d * K := by
        apply Finset.sum_le_sum
        intro o _ho
        have hdata := hterminal o.1 o.2
        exact (Finset.card_filter_le _ _).trans
          ((projectiveSurfaceAffineHypersurface_componentCount_le
            hBezout I (terminalCut o.1) hprime hhom hchart hdegree
              hdata.1 hdata.2.1).trans
            (Nat.mul_le_mul_left d hdata.2.2))
    _ = active.card * (d * K) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        smul_eq_mul]

/-- Simultaneous primitive full-line data for the progression-image cells.
Every complete line is contained in the rational terminal intersection that
created its occurrence. -/
theorem exists_quantitativePrefixPersistent_fullIntegralLines
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) :
    let J := fun o : {o // o ∈ active} =>
      realAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} =>
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : TaggedLinearComponent J → IntVector 3)
      (parameter : TaggedLinearComponent J → IntVector 3 → ℤ),
      ∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1)) : Set (IntVector 3)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1),
          z = fun i => base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ =>
            fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        Set.range (fun t : ℝ =>
          fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ⊆
            affineIdealZeroLocus (J o.1) := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} =>
    realAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} =>
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hdata⟩ :=
    exists_activeTaggedLinearComponent_fullIntegralLines hline J Y
  refine ⟨base, direction, parameter, ?_⟩
  intro o ho
  have hoData := hdata o ho
  refine ⟨hoData.1, hoData.2.1, hoData.2.2.1,
    hoData.2.2.2, ?_⟩
  intro y hy
  have hyQ : y ∈ affineIdealZeroLocus o.2.1 := by
    rw [hoData.2.2.2]
    exact hy
  have hQmin : o.2.1 ∈ finiteMinimalPrimes (J o.1) :=
    ((mem_linearAffineComponents_iff (J o.1) o.2.1).mp o.2.2).1
  have hJQ : J o.1 ≤ o.2.1 := le_of_mem_finiteMinimalPrimes hQmin
  intro f hf
  exact hyQ f (hJQ hf)

/-- The exact selected low part for an arbitrary finite direction catalogue.
It counts underlying points once, even when the same point occurs in several
terminal cells or on several displayed components. -/
def activeSelectedUnderlyingExactLowUnion
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (Y : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J Y → Direction) :
    Finset {z // z ∈ underlyingLinearContributionPoints J Y} := by
  classical
  exact (activeSelectedUnderlyingLinearPoints J Y).filter fun z =>
    taggedDirection (selectedTaggedLinearContributionPoint J Y z) ∈
      lowDirections

/-- The strongest multiplicity-free high/low ledger needed here: inactive
points cost one per occurrence, high points cost the high-fibre bound per
occurrence, and the low part remains one exact finite union. -/
theorem underlyingLinearContribution_card_le_high_add_exactLow
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (Y : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J Y → Direction)
    (highBound : ℕ)
    (hHigh : ∀ o : TaggedLinearComponent J,
      (activeHighTaggedLinearComponentFibre J Y lowDirections
        taggedDirection o).card ≤ highBound) :
    (underlyingLinearContributionPoints J Y).card ≤
      Fintype.card (TaggedLinearComponent J) +
      Fintype.card (TaggedLinearComponent J) * highBound +
        (activeSelectedUnderlyingExactLowUnion
          J Y lowDirections taggedDirection).card := by
  classical
  let pointDirection := fun z :
      {z // z ∈ underlyingLinearContributionPoints J Y} =>
    taggedDirection (selectedTaggedLinearContributionPoint J Y z)
  let high := (activeSelectedUnderlyingLinearPoints J Y).filter fun z =>
    pointDirection z ∉ lowDirections
  have hcover : high ⊆
      (Finset.univ : Finset (TaggedLinearComponent J)).biUnion
        (activeHighSelectedUnderlyingComponentFibre
          J Y lowDirections pointDirection) := by
    intro z hz
    have hs := Finset.mem_filter.mp hz
    exact Finset.mem_biUnion.mpr
      ⟨selectedUnderlyingLinearComponent J Y z, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hs.1, hs.2, rfl⟩⟩
  have hhigh : high.card ≤
      Fintype.card (TaggedLinearComponent J) * highBound := by
    calc
      high.card ≤
          ((Finset.univ : Finset (TaggedLinearComponent J)).biUnion
            (activeHighSelectedUnderlyingComponentFibre
              J Y lowDirections pointDirection)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ o : TaggedLinearComponent J,
          (activeHighSelectedUnderlyingComponentFibre
            J Y lowDirections pointDirection o).card := Finset.card_biUnion_le
      _ ≤ ∑ _o : TaggedLinearComponent J, highBound := by
        apply Finset.sum_le_sum
        intro o _ho
        exact (activeHighSelectedUnderlyingComponentFibre_card_le_tagged
          J Y lowDirections taggedDirection o).trans (hHigh o)
      _ = Fintype.card (TaggedLinearComponent J) * highBound := by simp
  have hpartition :
      (activeSelectedUnderlyingExactLowUnion
          J Y lowDirections taggedDirection).card + high.card =
        (activeSelectedUnderlyingLinearPoints J Y).card := by
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (s := activeSelectedUnderlyingLinearPoints J Y)
      (fun z => pointDirection z ∈ lowDirections)
  have hinactive :=
    card_inactiveSelectedUnderlyingLinearPoints_le_components J Y
  have htotal :=
    card_underlyingLinearContributionPoints_eq_inactive_add_active J Y
  change (underlyingLinearContributionPoints J Y).card ≤
    Fintype.card (TaggedLinearComponent J) +
      Fintype.card (TaggedLinearComponent J) * highBound +
        ((activeSelectedUnderlyingLinearPoints J Y).filter fun z =>
          taggedDirection (selectedTaggedLinearContributionPoint J Y z) ∈
            lowDirections).card
  dsimp only [activeSelectedUnderlyingExactLowUnion, pointDirection] at hpartition
  omega

/-- End-to-end line-ledger interface for the literal quantitative prefix
union.  The full-line classifier supplies primitive directions, every high
fibre inherits the common progression residue `u (mod m)`, and Bezout supplies
the occurrence budget `active.card * (d*K)`.  The low part is kept as one
exact multiplicity-free finite union for whichever geometric direction
catalogue is used downstream. -/
theorem exists_quantitativePrefixPersistent_fullLine_exactLowLedger
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {d K : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : X (0 : Fin 4) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ I ∧ terminalDegree o ≤ K)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (B : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ)| ≤ B) :
    let J := fun o : {o // o ∈ active} =>
      realAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} =>
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : TaggedLinearComponent J → IntVector 3)
      (parameter : TaggedLinearComponent J → IntVector 3 → ℤ),
      (∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1)) : Set (IntVector 3)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1),
          z = fun i => base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ =>
            fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        Set.range (fun t : ℝ =>
          fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (TaggedLinearComponent J) ≤ active.card * (d * K) ∧
      ∀ (Direction : Type*) (_inst : DecidableEq Direction)
        (lowDirections : Finset Direction)
        (taggedDirection : TaggedLinearContributionPoint J Y → Direction)
        (highBound : ℕ),
      (∀ o ∈ activeTaggedLinearComponents J Y,
        (activeHighTaggedLinearComponentFibre
          J Y lowDirections taggedDirection o).Nonempty →
        1 + ⌈2 * B⌉₊ /
          (m * directionHeight (direction o)) ≤ highBound) →
      (quantitativePrefixPersistentLinearPointUnion
          I active terminalCut u m cell).card ≤
        active.card * (d * K) +
          active.card * (d * K) * highBound +
          (activeSelectedUnderlyingExactLowUnion
            J Y lowDirections taggedDirection).card := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} =>
    realAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} =>
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull⟩ :=
    exists_quantitativePrefixPersistent_fullIntegralLines
      hline I active terminalCut u m cell
  have hoccurrence : Fintype.card (TaggedLinearComponent J) ≤
      active.card * (d * K) :=
    card_quantitativePrefixPersistent_taggedLines_le
      hBezout I hprime hhom hchart hdegree active terminalDegree
        terminalCut hterminal
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  intro Direction inst lowDirections taggedDirection highBound hNumerical
  letI : DecidableEq Direction := inst
  have hparam : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑((assignedLinearComponentFibre J Y o).image
          (fun x => x.2.1)) : Set (IntVector 3)) ∧
      ∀ z ∈ (assignedLinearComponentFibre J Y o).image
          (fun x => x.2.1),
        z = fun i => base o i + parameter o z * direction o i := by
    intro o ho
    exact ⟨(hfull o ho).1, (hfull o ho).2.1,
      (hfull o ho).2.2.1⟩
  have hHigh : ∀ o : TaggedLinearComponent J,
      (activeHighTaggedLinearComponentFibre
        J Y lowDirections taggedDirection o).card ≤ highBound := by
    intro o
    by_cases ho : o ∈ activeTaggedLinearComponents J Y
    · by_cases hempty : activeHighTaggedLinearComponentFibre
          J Y lowDirections taggedDirection o = ∅
      · simp [hempty]
      · have hnonempty : (activeHighTaggedLinearComponentFibre
            J Y lowDirections taggedDirection o).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hempty
        have hraw := activeHighTaggedLinearComponentFibre_card_le_tagged
          J Y lowDirections taggedDirection base direction parameter hparam
          o ho (fun _i => 0) B m hm u
          (by
            intro x hx i
            have hxY : x.2.1 ∈ Y x.1 :=
              finitePointsOnLinearCurveComponents_subset
                (J x.1) (Y x.1) x.2.2
            change x.2.1 ∈ (cell x.1.1).image
              (fun z => integralAffineMap u z m) at hxY
            obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxY
            rw [← hzx]
            simpa using hbox x.1.1 x.1.2 z hz i)
          (by
            intro x hx i
            have hxY : x.2.1 ∈ Y x.1 :=
              finitePointsOnLinearCurveComponents_subset
                (J x.1) (Y x.1) x.2.2
            change x.2.1 ∈ (cell x.1.1).image
              (fun z => integralAffineMap u z m) at hxY
            obtain ⟨z, _hz, hzx⟩ := Finset.mem_image.mp hxY
            rw [← hzx]
            exact (ZMod.intCast_eq_intCast_iff _ _ _).1
              (integralAffineMap_congruent u z i))
        exact hraw.trans (hNumerical o ho hnonempty)
    · have hempty : activeHighTaggedLinearComponentFibre
          J Y lowDirections taggedDirection o = ∅ := by
        ext x
        simp only [activeHighTaggedLinearComponentFibre, Finset.mem_filter,
          Finset.notMem_empty, iff_false]
        intro hx
        have hxactive :=
          (mem_activeTaggedLinearContributionPoints_iff J Y x).1 hx.1
        exact ho (by simpa only [hx.2.2] using hxactive)
      simp [hempty]
  have hledger := underlyingLinearContribution_card_le_high_add_exactLow
    J Y lowDirections taggedDirection highBound hHigh
  have hunion := quantitativePrefixPersistentLinearPointUnion_eq_underlying
    I active terminalCut u m cell
  calc
    (quantitativePrefixPersistentLinearPointUnion
        I active terminalCut u m cell).card =
        (underlyingLinearContributionPoints J Y).card :=
      congrArg Finset.card hunion
    _ ≤ Fintype.card (TaggedLinearComponent J) +
        Fintype.card (TaggedLinearComponent J) * highBound +
          (activeSelectedUnderlyingExactLowUnion
            J Y lowDirections taggedDirection).card := hledger
    _ ≤ active.card * (d * K) +
        active.card * (d * K) * highBound +
          (activeSelectedUnderlyingExactLowUnion
            J Y lowDirections taggedDirection).card := by
      exact Nat.add_le_add
        (Nat.add_le_add hoccurrence
          (Nat.mul_le_mul_right highBound hoccurrence)) (le_refl _)

/-! ## The intrinsic projective directions in the three affine coordinates -/

/-- A fixed nonzero direction used only to totalize projectivization on
inactive occurrences. -/
def quantitativePrefixFirstCoordinateDirection : IntVector 3 :=
  fun i => if i = 0 then 1 else 0

theorem quantitativePrefixFirstCoordinateDirection_ne_zero :
    quantitativePrefixFirstCoordinateDirection ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin 3)
  simp [quantitativePrefixFirstCoordinateDirection] at hzero

/-- Projectivize a three-dimensional integral direction, with the fixed first
coordinate direction as an irrelevant fallback on inactive occurrences. -/
def quantitativePrefixIntegralProjectiveClassOrFirst (h : IntVector 3) :
    Projectivization ℚ (Fin 3 → ℚ) :=
  if hh : h ≠ 0 then integralProjectiveClass h hh
  else integralProjectiveClass quantitativePrefixFirstCoordinateDirection
    quantitativePrefixFirstCoordinateDirection_ne_zero

/-- Projective direction of one tagged prefix-line point. -/
def quantitativePrefixTaggedLinearPointProjectiveDirection
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℝ))
    (Y : ι → Finset (IntVector 3))
    (direction : TaggedLinearComponent J → IntVector 3)
    (x : TaggedLinearContributionPoint J Y) :
    Projectivization ℚ (Fin 3 → ℚ) :=
  quantitativePrefixIntegralProjectiveClassOrFirst
    (direction (linearComponentOccurrenceOfPoint J Y x))

/-- Distinct projective directions of the active prefix-line occurrences
whose primitive height is at most the chosen cutoff. -/
def quantitativePrefixActiveLowProjectiveDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℝ))
    (Y : ι → Finset (IntVector 3))
    (direction : TaggedLinearComponent J → IntVector 3)
    (cutoff : ℕ) : Finset (Projectivization ℚ (Fin 3 → ℚ)) := by
  classical
  exact ((activeTaggedLinearComponents J Y).filter fun o =>
    directionHeight (direction o) ≤ cutoff).image fun o =>
      quantitativePrefixIntegralProjectiveClassOrFirst (direction o)

/-- Membership in a high fibre for the preceding literal projective split
forces the strict primitive-height inequality. -/
theorem directionHeight_gt_quantitativePrefixCutoff_of_mem_activeHigh
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℝ))
    (Y : ι → Finset (IntVector 3))
    (direction : TaggedLinearComponent J → IntVector 3)
    (cutoff : ℕ)
    (o : TaggedLinearComponent J)
    (ho : o ∈ activeTaggedLinearComponents J Y)
    (x : TaggedLinearContributionPoint J Y)
    (hx : x ∈ activeHighTaggedLinearComponentFibre J Y
      (quantitativePrefixActiveLowProjectiveDirections
        J Y direction cutoff)
      (quantitativePrefixTaggedLinearPointProjectiveDirection
        J Y direction) o) :
    cutoff < directionHeight (direction o) := by
  classical
  by_contra hnot
  have hle : directionHeight (direction o) ≤ cutoff := Nat.le_of_not_gt hnot
  have hoFilter : o ∈ (activeTaggedLinearComponents J Y).filter fun c =>
      directionHeight (direction c) ≤ cutoff :=
    Finset.mem_filter.mpr ⟨ho, hle⟩
  have hoLow : quantitativePrefixIntegralProjectiveClassOrFirst
      (direction o) ∈
      quantitativePrefixActiveLowProjectiveDirections
        J Y direction cutoff :=
    Finset.mem_image.mpr ⟨o, hoFilter, rfl⟩
  have hoccurrence : linearComponentOccurrenceOfPoint J Y x = o :=
    (Finset.mem_filter.mp hx).2.2
  exact (Finset.mem_filter.mp hx).2.1 (by
    simpa [quantitativePrefixTaggedLinearPointProjectiveDirection,
      hoccurrence] using hoLow)

/-- Concrete projective high/low ledger for the prefix union.  High fibres
are bounded directly from the common progression congruence and the strict
height cutoff.  Repeated low directions are identified projectively and the
remaining low term is the exact selected underlying union. -/
theorem exists_quantitativePrefixPersistent_projectiveLineLedger
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {d K : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hchart : X (0 : Fin 4) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ I ∧ terminalDegree o ≤ K)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (B : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ)| ≤ B)
    (cutoff : ℕ) :
    let J := fun o : {o // o ∈ active} =>
      realAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} =>
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : TaggedLinearComponent J → IntVector 3)
      (parameter : TaggedLinearComponent J → IntVector 3 → ℤ),
      (∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1)) : Set (IntVector 3)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1),
          z = fun i => base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ =>
            fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        Set.range (fun t : ℝ =>
          fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (TaggedLinearComponent J) ≤ active.card * (d * K) ∧
      (quantitativePrefixPersistentLinearPointUnion
          I active terminalCut u m cell).card ≤
        active.card * (d * K) +
          active.card * (d * K) *
            (1 + ⌈2 * B⌉₊ / (m * (cutoff + 1))) +
          (activeSelectedUnderlyingExactLowUnion J Y
            (quantitativePrefixActiveLowProjectiveDirections
              J Y direction cutoff)
            (quantitativePrefixTaggedLinearPointProjectiveDirection
              J Y direction)).card := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} =>
    realAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} =>
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull, hoccurrence, hledger⟩ :=
    exists_quantitativePrefixPersistent_fullLine_exactLowLedger
      hline hBezout I hprime hhom hchart hdegree active terminalDegree
        terminalCut hterminal u m hm cell B hbox
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  let lowDirections := quantitativePrefixActiveLowProjectiveDirections
    J Y direction cutoff
  let taggedDirection :=
    quantitativePrefixTaggedLinearPointProjectiveDirection J Y direction
  let highBound := 1 + ⌈2 * B⌉₊ / (m * (cutoff + 1))
  have hNumerical : ∀ o ∈ activeTaggedLinearComponents J Y,
      (activeHighTaggedLinearComponentFibre
        J Y lowDirections taggedDirection o).Nonempty →
      1 + ⌈2 * B⌉₊ / (m * directionHeight (direction o)) ≤
        highBound := by
    intro o ho hnonempty
    obtain ⟨x, hx⟩ := hnonempty
    have hheight : cutoff < directionHeight (direction o) :=
      directionHeight_gt_quantitativePrefixCutoff_of_mem_activeHigh
        J Y direction cutoff o ho x hx
    have hheight' : cutoff + 1 ≤ directionHeight (direction o) := by omega
    have hdenpos : 0 < m * (cutoff + 1) :=
      Nat.mul_pos hm (Nat.zero_lt_succ cutoff)
    apply Nat.add_le_add_left
    exact Nat.div_le_div_left (Nat.mul_le_mul_left m hheight') hdenpos
  simpa only [lowDirections, taggedDirection, highBound] using
    hledger (Projectivization ℚ (Fin 3 → ℚ)) (Classical.decEq _)
      lowDirections taggedDirection highBound hNumerical

end

end TranslatedDepthSeven
