import TranslatedDepthSeven.AffineChartPilaComponentCount
import TranslatedDepthSeven.ExplicitLineContribution
import TranslatedDepthSeven.TaggedLineCount

/-!
# Literal occurrences of degree-one affine components

The Pila decompositions leave a finite union of points on degree-one affine
components for every node, edge, or persistent record.  This file converts an
arbitrary finite family of those displayed unions into a single tagged point
type and a single tagged component type.  Tags are retained, so no accidental
identification of equal points coming from different records is possible.

Components which receive at most one tagged point cost at most one point per
component.  Every remaining component has two integral points and hence admits
the elementary primitive integral parametrization of a rational affine line.
The latter classification is isolated as a narrow standard fact; it contains
no point-counting assertion.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

/-- The actual minimal components certified to be affine curves of degree
one. -/
def linearAffineComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ)) :
    Finset (Ideal (MvPolynomial (Fin N) ℝ)) := by
  classical
  exact (finiteMinimalPrimes J).filter fun Q ↦
    HasAffineHilbertDimensionDegree Q 1 1

@[simp]
theorem mem_linearAffineComponents_iff {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (Q : Ideal (MvPolynomial (Fin N) ℝ)) :
    Q ∈ linearAffineComponents J ↔
      Q ∈ finiteMinimalPrimes J ∧
        HasAffineHilbertDimensionDegree Q 1 1 := by
  classical
  simp [linearAffineComponents]

/-- Membership in the displayed degree-one contribution has the expected
literal component witness. -/
theorem mem_finitePointsOnLinearCurveComponents_iff {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (X : Finset (IntVector N)) (z : IntVector N) :
    z ∈ finitePointsOnLinearCurveComponents J X ↔
      ∃ Q ∈ linearAffineComponents J,
        z ∈ finitePointsOnAffineIdeal X Q := by
  classical
  simp only [finitePointsOnLinearCurveComponents, Finset.mem_biUnion]
  constructor
  · rintro ⟨Q, hQ, hz⟩
    by_cases hdegree : HasAffineHilbertDimensionDegree Q 1 1
    · exact ⟨Q, (mem_linearAffineComponents_iff J Q).2 ⟨hQ, hdegree⟩,
        by simpa [hdegree] using hz⟩
    · simp [hdegree] at hz
  · rintro ⟨Q, hQ, hz⟩
    have hspec := (mem_linearAffineComponents_iff J Q).1 hQ
    exact ⟨Q, hspec.1, by simpa [hspec.2] using hz⟩

/-- Forgetting the chosen degree-one component returns a point of the
original finite set.  This elementary inclusion is the bridge by which a
tagged line point inherits the box and residue conditions of its actual
node, edge, or persistent record cell. -/
theorem finitePointsOnLinearCurveComponents_subset {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℝ))
    (X : Finset (IntVector N)) :
    finitePointsOnLinearCurveComponents J X ⊆ X := by
  intro z hz
  obtain ⟨Q, _hQ, hzQ⟩ :=
    (mem_finitePointsOnLinearCurveComponents_iff J X z).1 hz
  exact (mem_finitePointsOnAffineIdeal_iff X Q z).1 hzQ |>.1

/-- A point in one member of a finite family of displayed degree-one
contributions, with its family label retained. -/
def TaggedLinearContributionPoint {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :=
  Σ i : ι, {z // z ∈ finitePointsOnLinearCurveComponents (J i) (X i)}

/-- A degree-one component together with the family member in which it
occurs. -/
def TaggedLinearComponent {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ)) :=
  Σ i : ι, {Q // Q ∈ linearAffineComponents (J i)}

instance taggedLinearContributionPointFintype
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Fintype (TaggedLinearContributionPoint J X) := by
  classical
  letI (i : ι) : Fintype
      {z // z ∈ finitePointsOnLinearCurveComponents (J i) (X i)} :=
    Fintype.ofFinset (finitePointsOnLinearCurveComponents (J i) (X i))
      (fun _ ↦ Iff.rfl)
  unfold TaggedLinearContributionPoint
  exact inferInstance

instance taggedLinearComponentFintype
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ)) :
    Fintype (TaggedLinearComponent J) := by
  classical
  letI (i : ι) : Fintype {Q // Q ∈ linearAffineComponents (J i)} :=
    Fintype.ofFinset (linearAffineComponents (J i)) (fun _ ↦ Iff.rfl)
  unfold TaggedLinearComponent
  exact inferInstance

/-- Tagging converts the displayed sum of point cardinalities into an exact
finite-type cardinality. -/
theorem card_taggedLinearContributionPoint {ι : Type*} [Fintype ι]
    {N : ℕ} (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Fintype.card (TaggedLinearContributionPoint J X) =
      ∑ i : ι, (finitePointsOnLinearCurveComponents (J i) (X i)).card := by
  classical
  letI (i : ι) : Fintype
      {z // z ∈ finitePointsOnLinearCurveComponents (J i) (X i)} :=
    Fintype.ofFinset (finitePointsOnLinearCurveComponents (J i) (X i))
      (fun _ ↦ Iff.rfl)
  change Fintype.card
    (Σ i : ι,
      {z // z ∈ finitePointsOnLinearCurveComponents (J i) (X i)}) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Fintype.card_ofFinset _ (fun _ ↦ Iff.rfl)

/-- The analogous exact formula for tagged degree-one components. -/
theorem card_taggedLinearComponent {ι : Type*} [Fintype ι]
    {N : ℕ} (J : ι → Ideal (MvPolynomial (Fin N) ℝ)) :
    Fintype.card (TaggedLinearComponent J) =
      ∑ i : ι, (linearAffineComponents (J i)).card := by
  classical
  letI (i : ι) : Fintype {Q // Q ∈ linearAffineComponents (J i)} :=
    Fintype.ofFinset (linearAffineComponents (J i)) (fun _ ↦ Iff.rfl)
  change Fintype.card
    (Σ i : ι, {Q // Q ∈ linearAffineComponents (J i)}) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Fintype.card_ofFinset _ (fun _ ↦ Iff.rfl)

/-- Choose one actual degree-one component containing a displayed point.
The choice is made only inside the same family member. -/
def selectedLinearComponent {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (x : TaggedLinearContributionPoint J X) :
    {Q // Q ∈ linearAffineComponents (J x.1)} :=
  ⟨Classical.choose
      ((mem_finitePointsOnLinearCurveComponents_iff
        (J x.1) (X x.1) x.2.1).1 x.2.2),
    (Classical.choose_spec
      ((mem_finitePointsOnLinearCurveComponents_iff
        (J x.1) (X x.1) x.2.1).1 x.2.2)).1⟩

/-- The tagged component assigned to a tagged point. -/
def linearComponentOccurrenceOfPoint
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (x : TaggedLinearContributionPoint J X) :
    TaggedLinearComponent J := ⟨x.1, selectedLinearComponent J X x⟩

/-- The selected component really contains the underlying integral point. -/
theorem taggedLinearPoint_mem_selectedComponent
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (x : TaggedLinearContributionPoint J X) :
    x.2.1 ∈ finitePointsOnAffineIdeal (X x.1)
      (selectedLinearComponent J X x).1 := by
  exact (Classical.choose_spec
    ((mem_finitePointsOnLinearCurveComponents_iff
      (J x.1) (X x.1) x.2.1).1 x.2.2)).2

/-- The literal fibre assigned to one tagged component. -/
def assignedLinearComponentFibre
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (o : TaggedLinearComponent J) :
    Finset (TaggedLinearContributionPoint J X) := by
  classical
  exact Finset.univ.filter fun x ↦
    linearComponentOccurrenceOfPoint J X x = o

/-- An underlying integral point chosen from a nonempty assigned fibre.
The zero vector is used only to make the definition total on empty fibres;
all later uses carry an explicit nonemptiness proof. -/
def assignedLinearComponentRepresentative
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (o : TaggedLinearComponent J) : IntVector N := by
  classical
  exact if h : (assignedLinearComponentFibre J X o).Nonempty then
    (Classical.choose h).2.1
  else 0

/-- The representative of a nonempty assigned fibre belongs to the
original finite set attached to the same occurrence index. -/
theorem assignedLinearComponentRepresentative_mem
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (o : TaggedLinearComponent J)
    (ho : (assignedLinearComponentFibre J X o).Nonempty) :
    assignedLinearComponentRepresentative J X o ∈ X o.1 := by
  classical
  let x : TaggedLinearContributionPoint J X := Classical.choose ho
  have hx : x ∈ assignedLinearComponentFibre J X o := Classical.choose_spec ho
  have hoccurrence : linearComponentOccurrenceOfPoint J X x = o :=
    (Finset.mem_filter.mp hx).2
  have hindex : x.1 = o.1 := congrArg
    (fun c : TaggedLinearComponent J ↦ c.1) hoccurrence
  have hxX : x.2.1 ∈ X x.1 :=
    finitePointsOnLinearCurveComponents_subset (J x.1) (X x.1) x.2.2
  rw [assignedLinearComponentRepresentative, dif_pos ho]
  simpa only [x] using hindex ▸ hxX

/-- Every assigned point lies on the tagged component and comes from the
same family member. -/
theorem mem_assignedLinearComponentFibre_ideal
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (o : TaggedLinearComponent J)
    (x : TaggedLinearContributionPoint J X)
    (hx : x ∈ assignedLinearComponentFibre J X o) :
    x.1 = o.1 ∧
      x.2.1 ∈ finitePointsOnAffineIdeal (X o.1) o.2.1 := by
  classical
  have heq := (Finset.mem_filter.mp hx).2
  cases heq
  exact ⟨rfl, taggedLinearPoint_mem_selectedComponent J X x⟩

/-- Tagged points are partitioned exactly by their selected tagged
components. -/
theorem sum_card_assignedLinearComponentFibre
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    ∑ o : TaggedLinearComponent J,
        (assignedLinearComponentFibre J X o).card =
      Fintype.card (TaggedLinearContributionPoint J X) := by
  classical
  let points : Finset (TaggedLinearContributionPoint J X) := Finset.univ
  have h := Finset.card_eq_sum_card_fiberwise
    (s := points) (t := (Finset.univ : Finset (TaggedLinearComponent J)))
    (f := linearComponentOccurrenceOfPoint J X)
    (by intro x hx; simp)
  simpa [points, assignedLinearComponentFibre] using h.symm

/-- Components receiving at least two selected points. -/
def activeTaggedLinearComponents
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Finset (TaggedLinearComponent J) := by
  classical
  exact Finset.univ.filter fun o ↦
    2 ≤ (assignedLinearComponentFibre J X o).card

/-- The actual tagged points assigned to active components.  This is a
literal filter of the tagged point set, not a union in which equal underlying
integral points could be identified. -/
def activeTaggedLinearContributionPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Finset (TaggedLinearContributionPoint J X) := by
  classical
  exact Finset.univ.filter fun x ↦
    linearComponentOccurrenceOfPoint J X x ∈
      activeTaggedLinearComponents J X

@[simp]
theorem mem_activeTaggedLinearContributionPoints_iff
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (x : TaggedLinearContributionPoint J X) :
    x ∈ activeTaggedLinearContributionPoints J X ↔
      linearComponentOccurrenceOfPoint J X x ∈
        activeTaggedLinearComponents J X := by
  classical
  simp [activeTaggedLinearContributionPoints]

/-- The active point set is partitioned exactly by active component
occurrences. -/
theorem card_activeTaggedLinearContributionPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    (activeTaggedLinearContributionPoints J X).card =
      ∑ o ∈ activeTaggedLinearComponents J X,
        (assignedLinearComponentFibre J X o).card := by
  classical
  let activePoints := activeTaggedLinearContributionPoints J X
  let activeComponents := activeTaggedLinearComponents J X
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := activePoints) (t := activeComponents)
    (f := linearComponentOccurrenceOfPoint J X)
    (by
      intro x hx
      exact (mem_activeTaggedLinearContributionPoints_iff J X x).1 hx)
  apply hpartition.trans
  apply Finset.sum_congr rfl
  intro o ho
  congr 1
  ext x
  simp only [activePoints,
    activeTaggedLinearContributionPoints, assignedLinearComponentFibre,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_hxactive, hxo⟩
    exact hxo
  · intro hxo
    refine ⟨?_, hxo⟩
    simpa only [hxo] using ho

/-- All singleton and empty component fibres together cost at most one point
per tagged component.  Thus only the active components need enter the line
ledger. -/
theorem taggedLinearContribution_card_le_components_add_activeFibres
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Fintype.card (TaggedLinearContributionPoint J X) ≤
      Fintype.card (TaggedLinearComponent J) +
        ∑ o ∈ activeTaggedLinearComponents J X,
          (assignedLinearComponentFibre J X o).card := by
  classical
  rw [← sum_card_assignedLinearComponentFibre J X]
  let active := activeTaggedLinearComponents J X
  let inactive := (Finset.univ : Finset (TaggedLinearComponent J)).filter
    fun o ↦ ¬ 2 ≤ (assignedLinearComponentFibre J X o).card
  have hsplit :
      (∑ o : TaggedLinearComponent J,
          (assignedLinearComponentFibre J X o).card) =
        (∑ o ∈ active,
          (assignedLinearComponentFibre J X o).card) +
        ∑ o ∈ inactive,
          (assignedLinearComponentFibre J X o).card := by
    simpa [active, inactive] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (TaggedLinearComponent J)))
        (p := fun o ↦ 2 ≤ (assignedLinearComponentFibre J X o).card)
        (f := fun o ↦ (assignedLinearComponentFibre J X o).card)).symm
  have hinactive :
      (∑ o ∈ inactive,
          (assignedLinearComponentFibre J X o).card) ≤ inactive.card := by
    calc
      (∑ o ∈ inactive,
          (assignedLinearComponentFibre J X o).card) ≤
          ∑ _o ∈ inactive, 1 := by
        apply Finset.sum_le_sum
        intro o ho
        have hnot : ¬ 2 ≤
            (assignedLinearComponentFibre J X o).card :=
          (Finset.mem_filter.mp ho).2
        omega
      _ = inactive.card := by simp
  have hcard : inactive.card ≤
      Fintype.card (TaggedLinearComponent J) := by
    calc
      inactive.card ≤ (Finset.univ : Finset (TaggedLinearComponent J)).card :=
        Finset.card_filter_le _ _
      _ = Fintype.card (TaggedLinearComponent J) := Finset.card_univ
  calc
    (∑ o : TaggedLinearComponent J,
        (assignedLinearComponentFibre J X o).card) =
        (∑ o ∈ active,
          (assignedLinearComponentFibre J X o).card) +
        ∑ o ∈ inactive,
          (assignedLinearComponentFibre J X o).card := hsplit
    _ ≤ (∑ o ∈ active,
          (assignedLinearComponentFibre J X o).card) + inactive.card :=
      Nat.add_le_add_left hinactive _
    _ ≤ (∑ o ∈ active,
          (assignedLinearComponentFibre J X o).card) +
          Fintype.card (TaggedLinearComponent J) :=
      Nat.add_le_add_left hcard _
    _ = Fintype.card (TaggedLinearComponent J) +
        ∑ o ∈ activeTaggedLinearComponents J X,
          (assignedLinearComponentFibre J X o).card := by
      simp only [active]
      omega

/-- Equivalent active-set form of the singleton/empty overhead estimate. -/
theorem taggedLinearContribution_card_le_components_add_activePoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    Fintype.card (TaggedLinearContributionPoint J X) ≤
      Fintype.card (TaggedLinearComponent J) +
        (activeTaggedLinearContributionPoints J X).card := by
  rw [card_activeTaggedLinearContributionPoints]
  exact taggedLinearContribution_card_le_components_add_activeFibres J X

/-- The active high-direction fibre of one actual component occurrence. -/
def activeHighTaggedLinearComponentFibre
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (direction : TaggedLinearContributionPoint J X → Direction)
    (o : TaggedLinearComponent J) :
    Finset (TaggedLinearContributionPoint J X) := by
  classical
  exact (activeTaggedLinearContributionPoints J X).filter fun x ↦
    direction x ∉ lowDirections ∧
      linearComponentOccurrenceOfPoint J X x = o

/-- The high fibre of one active component is bounded by the proved
one-line congruence estimate.  The hypotheses are only its primitive
parametrization and the literal box and residue properties of its points. -/
theorem activeHighTaggedLinearComponentFibre_card_le_tagged
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (pointDirection : TaggedLinearContributionPoint J X → Direction)
    (base lineDirection : TaggedLinearComponent J → IntVector N)
    (parameter : TaggedLinearComponent J → IntVector N → ℤ)
    (hdata : ∀ o ∈ activeTaggedLinearComponents J X,
      PrimitiveDirection (lineDirection o) ∧
      Set.InjOn (parameter o)
        (↑((assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
      ∀ z ∈ (assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1),
        z = fun i ↦ base o i + parameter o z * lineDirection o i)
    (o : TaggedLinearComponent J)
    (ho : o ∈ activeTaggedLinearComponents J X)
    (center : RealVector N) (R : ℝ) (r : ℕ) (hr : 0 < r)
    (residue : IntVector N)
    (hBox : ∀ x ∈ activeHighTaggedLinearComponentFibre
        J X lowDirections pointDirection o, ∀ i,
      |(x.2.1 i : ℝ) - center i| ≤ R)
    (hResidue : ∀ x ∈ activeHighTaggedLinearComponentFibre
        J X lowDirections pointDirection o, ∀ i,
      x.2.1 i ≡ residue i [ZMOD (r : ℤ)]) :
    (activeHighTaggedLinearComponentFibre
      J X lowDirections pointDirection o).card ≤
        1 + ⌈2 * R⌉₊ / (r * directionHeight (lineDirection o)) := by
  classical
  let S := activeHighTaggedLinearComponentFibre
    J X lowDirections pointDirection o
  have hassigned : ∀ x ∈ S,
      x ∈ assignedLinearComponentFibre J X o := by
    intro x hx
    have hxo : linearComponentOccurrenceOfPoint J X x = o :=
      (Finset.mem_filter.mp hx).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxo⟩
  have himage : ∀ x ∈ S,
      x.2.1 ∈ (assignedLinearComponentFibre J X o).image
        (fun y ↦ y.2.1) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hassigned x hx, rfl⟩
  have hParameter : Set.InjOn (fun x : TaggedLinearContributionPoint J X ↦
      parameter o x.2.1) (↑S : Set (TaggedLinearContributionPoint J X)) := by
    intro x hx y hy hxy
    have hz : x.2.1 = y.2.1 :=
      (hdata o ho).2.1 (himage x hx) (himage y hy) hxy
    have hxo : linearComponentOccurrenceOfPoint J X x = o :=
      (Finset.mem_filter.mp hx).2.2
    have hyo : linearComponentOccurrenceOfPoint J X y = o :=
      (Finset.mem_filter.mp hy).2.2
    have hi : x.1 = y.1 := congrArg
      (fun z : TaggedLinearComponent J ↦ z.1) (hxo.trans hyo.symm)
    cases x with
    | mk xi xz =>
      cases y with
      | mk yi yz =>
        dsimp only at hi hz ⊢
        subst yi
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext hz))
  have hRepresentation : ∀ x ∈ S,
      x.2.1 = fun i ↦
        base o i + parameter o x.2.1 * lineDirection o i := by
    intro x hx
    exact (hdata o ho).2.2 x.2.1 (himage x hx)
  apply highLineFibre_card_le_tagged
    S (fun x ↦ parameter o x.2.1) hParameter
    (lineDirection o) (base o) residue center hr (hdata o ho).1
  · intro x hx i
    rw [← congrFun (hRepresentation x hx) i]
    exact hBox x hx i
  · intro x hx i
    rw [← congrFun (hRepresentation x hx) i]
    exact hResidue x hx i

/-- High fibres in the active ledger are therefore discharged by literal
line data and a numerical comparison with a common majorant.  Only the
low-direction fibre bound remains to be supplied by the star/proper-piece
argument. -/
theorem taggedLinearContribution_card_le_active_high_low_of_line_data
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (pointDirection : TaggedLinearContributionPoint J X → Direction)
    (base lineDirection : TaggedLinearComponent J → IntVector N)
    (parameter : TaggedLinearComponent J → IntVector N → ℤ)
    (hdata : ∀ o ∈ activeTaggedLinearComponents J X,
      PrimitiveDirection (lineDirection o) ∧
      Set.InjOn (parameter o)
        (↑((assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
      ∀ z ∈ (assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1),
        z = fun i ↦ base o i + parameter o z * lineDirection o i)
    (center : TaggedLinearComponent J → RealVector N)
    (radius : TaggedLinearComponent J → ℝ)
    (modulus : TaggedLinearComponent J → ℕ)
    (residue : TaggedLinearComponent J → IntVector N)
    (highFibreBound lowFibreBound : ℕ)
    (hModulus : ∀ o ∈ activeTaggedLinearComponents J X,
      0 < modulus o)
    (hBox : ∀ o ∈ activeTaggedLinearComponents J X,
      ∀ x ∈ activeHighTaggedLinearComponentFibre
          J X lowDirections pointDirection o, ∀ i,
        |(x.2.1 i : ℝ) - center o i| ≤ radius o)
    (hResidue : ∀ o ∈ activeTaggedLinearComponents J X,
      ∀ x ∈ activeHighTaggedLinearComponentFibre
          J X lowDirections pointDirection o, ∀ i,
        x.2.1 i ≡ residue o i [ZMOD (modulus o : ℤ)])
    (hNumerical : ∀ o ∈ activeTaggedLinearComponents J X,
      (activeHighTaggedLinearComponentFibre
        J X lowDirections pointDirection o).Nonempty →
      1 + ⌈2 * radius o⌉₊ /
        (modulus o * directionHeight (lineDirection o)) ≤ highFibreBound)
    (hLowFibre : ∀ h ∈ lowDirections,
      ((activeTaggedLinearContributionPoints J X).filter fun x ↦
        pointDirection x = h).card ≤ lowFibreBound) :
    Fintype.card (TaggedLinearContributionPoint J X) ≤
      Fintype.card (TaggedLinearComponent J) +
      Fintype.card (TaggedLinearComponent J) * highFibreBound +
        lowDirections.card * lowFibreBound := by
  classical
  have hHighFibre : ∀ o : TaggedLinearComponent J,
      (activeHighTaggedLinearComponentFibre
        J X lowDirections pointDirection o).card ≤ highFibreBound := by
    intro o
    by_cases ho : o ∈ activeTaggedLinearComponents J X
    · by_cases hempty : activeHighTaggedLinearComponentFibre
          J X lowDirections pointDirection o = ∅
      · simp [hempty]
      · exact (activeHighTaggedLinearComponentFibre_card_le_tagged
          J X lowDirections pointDirection base lineDirection parameter hdata
          o ho (center o) (radius o) (modulus o) (hModulus o ho) (residue o)
          (hBox o ho) (hResidue o ho)).trans
            (hNumerical o ho (Finset.nonempty_iff_ne_empty.mpr hempty))
    · have hempty : activeHighTaggedLinearComponentFibre
          J X lowDirections pointDirection o = ∅ := by
        ext x
        simp only [activeHighTaggedLinearComponentFibre, Finset.mem_filter,
          Finset.notMem_empty, iff_false]
        intro hx
        have hxactive :=
          (mem_activeTaggedLinearContributionPoints_iff J X x).1 hx.1
        exact ho (by simpa only [hx.2.2] using hxactive)
      simp [hempty]
  let points := activeTaggedLinearContributionPoints J X
  let occurrences : Finset (TaggedLinearComponent J) := Finset.univ
  have hactive := linePoints_card_le_occurrences_mul_add_directions_mul
    points occurrences lowDirections
    (linearComponentOccurrenceOfPoint J X) pointDirection
    highFibreBound lowFibreBound
    (by intro x hx _hhigh; simp [occurrences])
    (by
      intro o _ho
      simpa only [points, activeHighTaggedLinearComponentFibre] using
        hHighFibre o)
    hLowFibre
  have hall := taggedLinearContribution_card_le_components_add_activePoints J X
  calc
    Fintype.card (TaggedLinearContributionPoint J X) ≤
        Fintype.card (TaggedLinearComponent J) + points.card := hall
    _ ≤ Fintype.card (TaggedLinearComponent J) +
        (occurrences.card * highFibreBound +
          lowDirections.card * lowFibreBound) :=
      Nat.add_le_add_left hactive _
    _ = Fintype.card (TaggedLinearComponent J) +
        Fintype.card (TaggedLinearComponent J) * highFibreBound +
          lowDirections.card * lowFibreBound := by
      simp only [occurrences, Finset.card_univ]
      omega

/-- The literal high--low ledger for the active degree-one contributions.
High points retain their component occurrence tag; low points are regrouped
only by their common direction.  The extra first term is precisely the
empty/singleton component overhead. -/
theorem taggedLinearContribution_card_le_active_high_low_ledger
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (direction : TaggedLinearContributionPoint J X → Direction)
    (highFibreBound lowFibreBound : ℕ)
    (hHighFibre : ∀ o : TaggedLinearComponent J,
      (activeHighTaggedLinearComponentFibre J X lowDirections direction o).card ≤
        highFibreBound)
    (hLowFibre : ∀ h ∈ lowDirections,
      ((activeTaggedLinearContributionPoints J X).filter fun x ↦
        direction x = h).card ≤ lowFibreBound) :
    Fintype.card (TaggedLinearContributionPoint J X) ≤
      Fintype.card (TaggedLinearComponent J) +
      Fintype.card (TaggedLinearComponent J) * highFibreBound +
        lowDirections.card * lowFibreBound := by
  classical
  let points := activeTaggedLinearContributionPoints J X
  let occurrences : Finset (TaggedLinearComponent J) := Finset.univ
  have hactive := linePoints_card_le_occurrences_mul_add_directions_mul
    points occurrences lowDirections
    (linearComponentOccurrenceOfPoint J X) direction
    highFibreBound lowFibreBound
    (by intro x hx _hhigh; simp [occurrences])
    (by
      intro o _ho
      simpa only [points, activeHighTaggedLinearComponentFibre] using
        hHighFibre o)
    hLowFibre
  have hall := taggedLinearContribution_card_le_components_add_activePoints J X
  calc
    Fintype.card (TaggedLinearContributionPoint J X) ≤
        Fintype.card (TaggedLinearComponent J) + points.card := hall
    _ ≤ Fintype.card (TaggedLinearComponent J) +
        (occurrences.card * highFibreBound +
          lowDirections.card * lowFibreBound) :=
      Nat.add_le_add_left hactive _
    _ = Fintype.card (TaggedLinearComponent J) +
        Fintype.card (TaggedLinearComponent J) * highFibreBound +
          lowDirections.card * lowFibreBound := by
      simp only [occurrences, Finset.card_univ]
      omega

/-- The number of tagged line occurrences is bounded by the sum of the
literal minimal-component counts. -/
theorem card_taggedLinearComponent_le_sum_minimalPrimes
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ)) :
    Fintype.card (TaggedLinearComponent J) ≤
      ∑ i : ι, (finiteMinimalPrimes (J i)).card := by
  classical
  rw [card_taggedLinearComponent]
  apply Finset.sum_le_sum
  intro i _hi
  exact Finset.card_filter_le _ _

namespace StandardAG

/-- Classification of the integral points on a degree-one affine curve once
two of them are present.  This is the usual statement that a degree-one
affine curve is a line, followed by extraction of the primitive generator of
the rank-one lattice of integral differences.  It contains no cardinality
bound. -/
def DegreeOneAffineCurvePrimitiveParametrization : Prop :=
  ∀ (N : ℕ) (Q : Ideal (MvPolynomial (Fin N) ℝ)),
    HasAffineHilbertDimensionDegree Q 1 1 →
    ∀ (S : Finset (IntVector N)), 2 ≤ S.card →
      (∀ z ∈ S,
        (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q) →
      ∃ (y₀ h : IntVector N) (parameter : IntVector N → ℤ),
        PrimitiveDirection h ∧
          Set.InjOn parameter (↑S : Set (IntVector N)) ∧
          ∀ z ∈ S, z = fun i ↦ y₀ i + parameter z * h i

end StandardAG

/-- The narrow degree-one classification supplies simultaneous primitive
line data for every active tagged component. -/
theorem exists_activeTaggedLinearComponent_primitiveParametrizations
    (hline : StandardAG.DegreeOneAffineCurvePrimitiveParametrization)
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    ∃ (base direction : TaggedLinearComponent J → IntVector N)
      (parameter : TaggedLinearComponent J → IntVector N → ℤ),
      ∀ o ∈ activeTaggedLinearComponents J X,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J X o).image
            (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
        ∀ z ∈ (assignedLinearComponentFibre J X o).image
            (fun x ↦ x.2.1),
          z = fun i ↦ base o i + parameter o z * direction o i := by
  classical
  have hdata : ∀ o : TaggedLinearComponent J,
      ∃ (y₀ h : IntVector N) (a : IntVector N → ℤ),
        o ∈ activeTaggedLinearComponents J X →
          PrimitiveDirection h ∧
          Set.InjOn a
            (↑((assignedLinearComponentFibre J X o).image
              (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
          ∀ z ∈ (assignedLinearComponentFibre J X o).image
              (fun x ↦ x.2.1),
            z = fun i ↦ y₀ i + a z * h i := by
    intro o
    by_cases ho : o ∈ activeTaggedLinearComponents J X
    · let S := (assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1)
      have hinjective : Set.InjOn (fun x : TaggedLinearContributionPoint J X ↦
          x.2.1) (↑(assignedLinearComponentFibre J X o) :
            Set (TaggedLinearContributionPoint J X)) := by
        intro x hx y hy hxy
        have hxo := (Finset.mem_filter.mp hx).2
        have hyo := (Finset.mem_filter.mp hy).2
        have hi : x.1 = y.1 := congrArg
          (fun z : TaggedLinearComponent J ↦ z.1) (hxo.trans hyo.symm)
        cases x with
        | mk xi xz =>
          cases y with
          | mk yi yz =>
            dsimp only at hi hxy ⊢
            subst yi
            exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy))
      have hScard : 2 ≤ S.card := by
        have himage := Finset.card_image_iff.mpr hinjective
        rw [himage]
        exact (Finset.mem_filter.mp ho).2
      have hSzero : ∀ z ∈ S,
          (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus o.2.1 := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact (mem_finitePointsOnAffineIdeal_iff (X o.1) o.2.1 x.2.1).1
          (mem_assignedLinearComponentFibre_ideal J X o x hx).2 |>.2
      have hdegree : HasAffineHilbertDimensionDegree o.2.1 1 1 :=
        ((mem_linearAffineComponents_iff (J o.1) o.2.1).1 o.2.2).2
      obtain ⟨y₀, h, a, hp, ha, hparam⟩ :=
        hline N o.2.1 hdegree S hScard hSzero
      exact ⟨y₀, h, a, fun _ ↦ ⟨hp, ha, hparam⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ (ho h).elim⟩
  choose base direction parameter hspec using hdata
  exact ⟨base, direction, parameter, hspec⟩

end

end TranslatedDepthSeven
