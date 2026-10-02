import TranslatedDepthSeven.RankSevenDegreeOneLowDirectionPartition

/-!
# High--low ledger for the selected underlying line union

This is the multiplicity-corrected version of the line ledger.  The points
are the finite union of the underlying degree-one record contributions, and
one actual tag is selected above each point.  Hence the low-direction term
counts geometric points, not record occurrences.  The high-direction term
still uses the literal selected component and its congruence modulus.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- The selected union points whose chosen component occurrence is
inactive. -/
def inactiveSelectedUnderlyingLinearPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Finset {z // z ∈ underlyingLinearContributionPoints J X} := by
  classical
  exact (underlyingLinearContributionPoints J X).attach.filter fun z ↦
    selectedUnderlyingLinearComponent J X z ∉
      activeTaggedLinearComponents J X

/-- The chosen tag is injective on the selected underlying union. -/
theorem selectedTaggedLinearContributionPoint_injective
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Function.Injective (selectedTaggedLinearContributionPoint J X) := by
  intro z w hzw
  apply Subtype.ext
  calc
    z.1 = (selectedTaggedLinearContributionPoint J X z).2.1 :=
      (selectedTaggedLinearContributionPoint_value J X z).symm
    _ = (selectedTaggedLinearContributionPoint J X w).2.1 := by rw [hzw]
    _ = w.1 := selectedTaggedLinearContributionPoint_value J X w

/-- An inactive chosen component receives at most one selected underlying
point.  Therefore all inactive selected points cost at most one point per
tagged component occurrence. -/
theorem card_inactiveSelectedUnderlyingLinearPoints_le_components
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    (inactiveSelectedUnderlyingLinearPoints J X).card ≤
      Fintype.card (TaggedLinearComponent J) := by
  classical
  have hinj : Set.InjOn (selectedUnderlyingLinearComponent J X)
      (↑(inactiveSelectedUnderlyingLinearPoints J X) :
        Set {z // z ∈ underlyingLinearContributionPoints J X}) := by
    intro z hz w hw hcomponent
    have hzInactive : selectedUnderlyingLinearComponent J X z ∉
        activeTaggedLinearComponents J X :=
      (Finset.mem_filter.mp hz).2
    let o := selectedUnderlyingLinearComponent J X z
    have hoCard : (assignedLinearComponentFibre J X o).card ≤ 1 := by
      have hnotTwo : ¬ 2 ≤ (assignedLinearComponentFibre J X o).card := by
        intro htwo
        apply hzInactive
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
      omega
    let x := selectedTaggedLinearContributionPoint J X z
    let y := selectedTaggedLinearContributionPoint J X w
    have hx : x ∈ assignedLinearComponentFibre J X o := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rfl
    have hy : y ∈ assignedLinearComponentFibre J X o := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact hcomponent.symm
    have hxy : x = y := (Finset.card_le_one_iff.mp hoCard) hx hy
    exact selectedTaggedLinearContributionPoint_injective J X hxy
  have himage := Finset.card_image_iff.mpr hinj
  calc
    (inactiveSelectedUnderlyingLinearPoints J X).card =
        ((inactiveSelectedUnderlyingLinearPoints J X).image
          (selectedUnderlyingLinearComponent J X)).card := himage.symm
    _ ≤ (Finset.univ : Finset (TaggedLinearComponent J)).card := by
      apply Finset.card_le_card
      intro o ho
      simp
    _ = Fintype.card (TaggedLinearComponent J) := Finset.card_univ

/-- Exact active/inactive cardinal partition of the selected underlying
union. -/
theorem card_underlyingLinearContributionPoints_eq_inactive_add_active
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    (underlyingLinearContributionPoints J X).card =
      (inactiveSelectedUnderlyingLinearPoints J X).card +
        (activeSelectedUnderlyingLinearPoints J X).card := by
  classical
  have hpartition := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (underlyingLinearContributionPoints J X).attach)
    (fun z ↦ selectedUnderlyingLinearComponent J X z ∈
      activeTaggedLinearComponents J X)
  simpa only [activeSelectedUnderlyingLinearPoints,
    inactiveSelectedUnderlyingLinearPoints, Finset.card_attach,
    not_not, Nat.add_comm] using hpartition.symm

/-- Active selected points of one high component occurrence. -/
def activeHighSelectedUnderlyingComponentFibre
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (pointDirection :
      {z // z ∈ underlyingLinearContributionPoints J X} → Direction)
    (o : TaggedLinearComponent J) :
    Finset {z // z ∈ underlyingLinearContributionPoints J X} := by
  classical
  exact (activeSelectedUnderlyingLinearPoints J X).filter fun z ↦
    pointDirection z ∉ lowDirections ∧
      selectedUnderlyingLinearComponent J X z = o

/-- The actual chosen record tags above one selected high fibre. -/
def selectedTagImageOfActiveHighFibre
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J X → Direction)
    (o : TaggedLinearComponent J) :
    Finset (TaggedLinearContributionPoint J X) := by
  classical
  exact (activeHighSelectedUnderlyingComponentFibre J X lowDirections
    (fun z ↦ taggedDirection
      (selectedTaggedLinearContributionPoint J X z)) o).image
        (selectedTaggedLinearContributionPoint J X)

/-- The chosen tags of a selected high fibre form a subset of the original
tagged high fibre. -/
theorem selectedTag_image_activeHigh_subset_taggedHigh
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J X → Direction)
    (o : TaggedLinearComponent J) :
    selectedTagImageOfActiveHighFibre
        J X lowDirections taggedDirection o ⊆
      activeHighTaggedLinearComponentFibre
        J X lowDirections taggedDirection o := by
  classical
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  have hzdata := Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨selectedTaggedLinearContributionPoint_mem_active
      J X z hzdata.1, hzdata.2.1, ?_⟩
  exact hzdata.2.2

/-- Any bound for the original tagged high occurrence fibre therefore
bounds the multiplicity-free selected high fibre. -/
theorem activeHighSelectedUnderlyingComponentFibre_card_le_tagged
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J X → Direction)
    (o : TaggedLinearComponent J) :
    (activeHighSelectedUnderlyingComponentFibre J X lowDirections
      (fun z ↦ taggedDirection
        (selectedTaggedLinearContributionPoint J X z)) o).card ≤
      (activeHighTaggedLinearComponentFibre
        J X lowDirections taggedDirection o).card := by
  classical
  let S := activeHighSelectedUnderlyingComponentFibre J X lowDirections
    (fun z ↦ taggedDirection
      (selectedTaggedLinearContributionPoint J X z)) o
  have hcard : S.card =
      (selectedTagImageOfActiveHighFibre
        J X lowDirections taggedDirection o).card :=
    (Finset.card_image_iff.mpr
      (selectedTaggedLinearContributionPoint_injective J X).injOn).symm
  rw [hcard]
  exact Finset.card_le_card
    (selectedTag_image_activeHigh_subset_taggedHigh
      J X lowDirections taggedDirection o)

/-- Multiplicity-corrected high--low ledger for the finite union of
underlying line points. -/
theorem underlyingLinearContribution_card_le_active_high_low
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (taggedDirection : TaggedLinearContributionPoint J X → Direction)
    (highFibreBound lowFibreBound : ℕ)
    (hHigh : ∀ o : TaggedLinearComponent J,
      (activeHighTaggedLinearComponentFibre
        J X lowDirections taggedDirection o).card ≤ highFibreBound)
    (hLow : ∀ h ∈ lowDirections,
      ((activeSelectedUnderlyingLinearPoints J X).filter fun z ↦
        taggedDirection (selectedTaggedLinearContributionPoint J X z) = h).card ≤
          lowFibreBound) :
    (underlyingLinearContributionPoints J X).card ≤
      Fintype.card (TaggedLinearComponent J) +
      Fintype.card (TaggedLinearComponent J) * highFibreBound +
        lowDirections.card * lowFibreBound := by
  classical
  let selectedPoints := activeSelectedUnderlyingLinearPoints J X
  let occurrences : Finset (TaggedLinearComponent J) := Finset.univ
  let occurrence := selectedUnderlyingLinearComponent J X
  let direction := fun z ↦
    taggedDirection (selectedTaggedLinearContributionPoint J X z)
  have hSelected : selectedPoints.card ≤
      occurrences.card * highFibreBound +
        lowDirections.card * lowFibreBound := by
    apply linePoints_card_le_occurrences_mul_add_directions_mul
      selectedPoints occurrences lowDirections occurrence direction
        highFibreBound lowFibreBound
    · intro z hz _hhigh
      simp [occurrences]
    · intro o _ho
      change (activeHighSelectedUnderlyingComponentFibre
        J X lowDirections direction o).card ≤ highFibreBound
      exact (activeHighSelectedUnderlyingComponentFibre_card_le_tagged
        J X lowDirections taggedDirection o).trans (hHigh o)
    · intro h hh
      simpa only [selectedPoints, direction] using hLow h hh
  rw [card_underlyingLinearContributionPoints_eq_inactive_add_active]
  calc
    (inactiveSelectedUnderlyingLinearPoints J X).card +
        (activeSelectedUnderlyingLinearPoints J X).card ≤
      Fintype.card (TaggedLinearComponent J) +
        (occurrences.card * highFibreBound +
          lowDirections.card * lowFibreBound) :=
      Nat.add_le_add
        (card_inactiveSelectedUnderlyingLinearPoints_le_components J X)
        hSelected
    _ = Fintype.card (TaggedLinearComponent J) +
        Fintype.card (TaggedLinearComponent J) * highFibreBound +
          lowDirections.card * lowFibreBound := by
      simp only [occurrences, Finset.card_univ]
      omega

end

end TranslatedDepthSeven
