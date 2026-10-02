import TranslatedDepthSeven.RankSevenDegreeOneProperStarSource

/-!
# Removing record multiplicity before the low-direction count

The literal node, edge, and persistent record cells are covers, not
pairwise-disjoint point sets.  Consequently the projection from the tagged
record sum to its underlying integral points need not be injective.  This
file makes the required correction explicitly: take the finite union of the
underlying degree-one points and choose one actual record tag above each
point.  All subsequent component and direction data are read from that
chosen tag.

The projection from this selected finite set back to integral points is
injective by construction.  No bound for record multiplicities is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- The finite union of the underlying points in all displayed degree-one
contributions.  Equal points in different record cells occur once. -/
def underlyingLinearContributionPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (Finset.univ : Finset (TaggedLinearContributionPoint J X)).image
    (fun x ↦ x.2.1)

@[simp]
theorem mem_underlyingLinearContributionPoints_iff
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) (z : IntVector N) :
    z ∈ underlyingLinearContributionPoints J X ↔
      ∃ x : TaggedLinearContributionPoint J X, x.2.1 = z := by
  classical
  simp [underlyingLinearContributionPoints]

/-- One actual record-tagged point above an element of the finite union. -/
def selectedTaggedLinearContributionPoint
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ underlyingLinearContributionPoints J X}) :
    TaggedLinearContributionPoint J X :=
  Classical.choose
    ((mem_underlyingLinearContributionPoints_iff J X z.1).1 z.2)

@[simp]
theorem selectedTaggedLinearContributionPoint_value
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ underlyingLinearContributionPoints J X}) :
    (selectedTaggedLinearContributionPoint J X z).2.1 = z.1 :=
  Classical.choose_spec
    ((mem_underlyingLinearContributionPoints_iff J X z.1).1 z.2)

/-- The component occurrence selected above an underlying point. -/
def selectedUnderlyingLinearComponent
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ underlyingLinearContributionPoints J X}) :
    TaggedLinearComponent J :=
  linearComponentOccurrenceOfPoint J X
    (selectedTaggedLinearContributionPoint J X z)

/-- Selected union points whose chosen component occurrence has at least two
assigned tagged points.  The inactive selected points cost at most one per
tagged component, exactly as in the tagged ledger. -/
def activeSelectedUnderlyingLinearPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Finset {z // z ∈ underlyingLinearContributionPoints J X} := by
  classical
  exact (underlyingLinearContributionPoints J X).attach.filter fun z ↦
    selectedUnderlyingLinearComponent J X z ∈
      activeTaggedLinearComponents J X

@[simp]
theorem mem_activeSelectedUnderlyingLinearPoints_iff
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ underlyingLinearContributionPoints J X}) :
    z ∈ activeSelectedUnderlyingLinearPoints J X ↔
      selectedUnderlyingLinearComponent J X z ∈
        activeTaggedLinearComponents J X := by
  classical
  simp [activeSelectedUnderlyingLinearPoints]

/-- The selected tag above an active underlying point is an actual active
tagged point, so all literal line and star incidence theorems apply to it. -/
theorem selectedTaggedLinearContributionPoint_mem_active
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ underlyingLinearContributionPoints J X})
    (hz : z ∈ activeSelectedUnderlyingLinearPoints J X) :
    selectedTaggedLinearContributionPoint J X z ∈
      activeTaggedLinearContributionPoints J X := by
  rw [mem_activeTaggedLinearContributionPoints_iff]
  exact (mem_activeSelectedUnderlyingLinearPoints_iff J X z).1 hz

/-- Projective direction of a selected underlying point. -/
def selectedUnderlyingProjectiveDirection
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (z : {z // z ∈ underlyingLinearContributionPoints J X}) :
    Projectivization ℚ (Fin 13 → ℚ) :=
  taggedLinearPointProjectiveDirection J X lineDirection
    (selectedTaggedLinearContributionPoint J X z)

/-- The selected active points of one projective direction. -/
def activeSelectedUnderlyingDirectionFibre
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (h : Projectivization ℚ (Fin 13 → ℚ)) :
    Finset {z // z ∈ underlyingLinearContributionPoints J X} := by
  classical
  exact (activeSelectedUnderlyingLinearPoints J X).filter fun z ↦
    selectedUnderlyingProjectiveDirection J X lineDirection z = h

/-- The literal untagged integral point set in one selected direction
fibre. -/
def activeSelectedUnderlyingDirectionImage
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (h : Projectivization ℚ (Fin 13 → ℚ)) : Finset (IntVector 13) :=
  (activeSelectedUnderlyingDirectionFibre J X lineDirection h).image
    Subtype.val

/-- Forgetting the selected-union subtype is injective on every direction
fibre.  This is the precise injectivity which fails for the original tagged
record sum. -/
theorem activeSelectedUnderlyingDirectionFibre_value_injective
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (h : Projectivization ℚ (Fin 13 → ℚ)) :
    Set.InjOn Subtype.val
      (↑(activeSelectedUnderlyingDirectionFibre J X lineDirection h) :
        Set {z // z ∈ underlyingLinearContributionPoints J X}) := by
  intro z _hz w _hw hzw
  exact Subtype.ext hzw

/-- Hence the selected subtype fibre and its literal integral image have
exactly the same cardinality. -/
theorem card_activeSelectedUnderlyingDirectionImage
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (h : Projectivization ℚ (Fin 13 → ℚ)) :
    (activeSelectedUnderlyingDirectionImage J X lineDirection h).card =
      (activeSelectedUnderlyingDirectionFibre J X lineDirection h).card := by
  exact Finset.card_image_iff.mpr
    (activeSelectedUnderlyingDirectionFibre_value_injective
      J X lineDirection h)

@[simp]
theorem mem_activeSelectedUnderlyingDirectionImage_iff
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (h : Projectivization ℚ (Fin 13 → ℚ)) (z : IntVector 13) :
    z ∈ activeSelectedUnderlyingDirectionImage J X lineDirection h ↔
      ∃ hz : z ∈ underlyingLinearContributionPoints J X,
        let z' : {w // w ∈ underlyingLinearContributionPoints J X} := ⟨z, hz⟩
        z' ∈ activeSelectedUnderlyingLinearPoints J X ∧
          selectedUnderlyingProjectiveDirection J X lineDirection z' = h := by
  classical
  simp only [activeSelectedUnderlyingDirectionImage,
    activeSelectedUnderlyingDirectionFibre, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨z', ⟨hzactive, hdir⟩, rfl⟩
    exact ⟨z'.2, hzactive, hdir⟩
  · rintro ⟨hz, hzactive, hdir⟩
    exact ⟨⟨z, hz⟩, ⟨hzactive, hdir⟩, rfl⟩

end

end TranslatedDepthSeven
