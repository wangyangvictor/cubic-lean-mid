import TranslatedDepthSeven.EffectiveRationalSurfaceSectionCount
import TranslatedDepthSeven.AffineDegreeOneLineEqualityInternal
import TranslatedDepthSeven.PrimitiveDirectionNormalization
import TranslatedDepthSeven.QuantitativePrefixPersistentLineLedger

/-!
# A rational degree-one line ledger for quantitative prefix cells

The degree-effective surface-section estimate leaves the literal rational
degree-one minimal components.  This file counts precisely that remainder.
It does not pass through real minimal components: a rational component and
its integral points are retained as one tagged occurrence.

Occurrences carrying at most one selected point cost one point each.  For
every remaining occurrence, the internally proved degree-one theorem gives
the complete rational affine line through its points.  Primitive integral
normalization then permits the existing one-line congruence count.  Equal
integral points belonging to several cells or components are selected only
once before the high/low split.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

local instance rationalLineLedgerProjectiveDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 3 → ℚ)) := Classical.decEq _

/-! ## Literal rational component occurrences -/

/-- The actual rational minimal components certified to be affine curves of
dimension one and degree one. -/
def rationalLinearAffineComponents {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℚ)) :
    Finset (Ideal (MvPolynomial (Fin N) ℚ)) := by
  classical
  exact (finiteMinimalPrimes J).filter fun Q ↦
    HasAffineHilbertDimensionDegree Q 1 1

@[simp]
theorem mem_rationalLinearAffineComponents_iff {N : ℕ}
    (J Q : Ideal (MvPolynomial (Fin N) ℚ)) :
    Q ∈ rationalLinearAffineComponents J ↔
      Q ∈ finiteMinimalPrimes J ∧
        HasAffineHilbertDimensionDegree Q 1 1 := by
  classical
  simp [rationalLinearAffineComponents]

/-- The effective count's literal degree-one point set is the union over
the filtered component list. -/
theorem finitePointsOnRationalLinearCurveComponents_eq_biUnion {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) ℚ))
    (X : Finset (IntVector N)) :
    finitePointsOnRationalLinearCurveComponents J X =
      (rationalLinearAffineComponents J).biUnion fun Q ↦
        finitePointsOnRationalAffineIdeal X Q := by
  classical
  ext z
  simp only [finitePointsOnRationalLinearCurveComponents,
    rationalLinearAffineComponents, Finset.mem_biUnion,
    Finset.mem_filter]
  constructor
  · rintro ⟨Q, hQ, hz⟩
    by_cases hdegree : HasAffineHilbertDimensionDegree Q 1 1
    · exact ⟨Q, ⟨hQ, hdegree⟩, by simpa [hdegree] using hz⟩
    · simp [hdegree] at hz
  · rintro ⟨Q, ⟨hQ, hdegree⟩, hz⟩
    exact ⟨Q, hQ, by simpa [hdegree] using hz⟩

/-- A cell label together with one of its actual rational degree-one
minimal components. -/
def RationalLinearOccurrence {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ)) :=
  Σ i : ι, {Q // Q ∈ rationalLinearAffineComponents (J i)}

instance rationalLinearOccurrenceFintype
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ)) :
    Fintype (RationalLinearOccurrence J) := by
  classical
  letI (i : ι) : Fintype
      {Q // Q ∈ rationalLinearAffineComponents (J i)} :=
    Fintype.ofFinset (rationalLinearAffineComponents (J i))
      (fun _ ↦ Iff.rfl)
  unfold RationalLinearOccurrence
  exact inferInstance

/-- The selected integral points on one literal rational line occurrence. -/
def rationalLinearOccurrencePoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (o : RationalLinearOccurrence J) : Finset (IntVector N) :=
  finitePointsOnRationalAffineIdeal (X o.1) o.2.1

/-- The multiplicity-free union of all rational degree-one component
points in the family. -/
def underlyingRationalLinearContributionPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (Finset.univ : Finset (RationalLinearOccurrence J)).biUnion
    (rationalLinearOccurrencePoints J X)

/-- The rational occurrence union is exactly the union of the literal
degree-one contributions in each family member. -/
theorem underlyingRationalLinearContributionPoints_eq_biUnion
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) :
    underlyingRationalLinearContributionPoints J X =
      (Finset.univ : Finset ι).biUnion fun i ↦
        finitePointsOnRationalLinearCurveComponents (J i) (X i) := by
  classical
  rw [underlyingRationalLinearContributionPoints]
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    finitePointsOnRationalLinearCurveComponents_eq_biUnion]
  constructor
  · rintro ⟨o, hz⟩
    exact ⟨o.1, o.2.1, o.2.2, hz⟩
  · rintro ⟨i, Q, hQ, hz⟩
    exact ⟨⟨i, ⟨Q, hQ⟩⟩, hz⟩

/-- The exact number of tagged rational degree-one occurrences. -/
theorem card_rationalLinearOccurrence
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ)) :
    Fintype.card (RationalLinearOccurrence J) =
      ∑ i : ι, (rationalLinearAffineComponents (J i)).card := by
  classical
  letI (i : ι) : Fintype
      {Q // Q ∈ rationalLinearAffineComponents (J i)} :=
    Fintype.ofFinset (rationalLinearAffineComponents (J i))
      (fun _ ↦ Iff.rfl)
  change Fintype.card
      (Σ i : ι, {Q // Q ∈ rationalLinearAffineComponents (J i)}) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Fintype.card_ofFinset _ (fun _ ↦ Iff.rfl)

/-- Occurrences containing at least two of the selected integral points. -/
def activeRationalLinearOccurrences
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) :
    Finset (RationalLinearOccurrence J) := by
  classical
  exact Finset.univ.filter fun o ↦
    2 ≤ (rationalLinearOccurrencePoints J X o).card

/-- The multiplicity-free union of points belonging to active rational
line occurrences. -/
def activeUnderlyingRationalLinearPoints
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) : Finset (IntVector N) := by
  classical
  exact (activeRationalLinearOccurrences J X).biUnion
    (rationalLinearOccurrencePoints J X)

/-- After discarding the active union, at most one point remains for each
tagged occurrence. -/
theorem underlyingRationalLinearContribution_card_le_occurrences_add_active
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) :
    (underlyingRationalLinearContributionPoints J X).card ≤
      Fintype.card (RationalLinearOccurrence J) +
        (activeUnderlyingRationalLinearPoints J X).card := by
  classical
  let inactive := (Finset.univ : Finset (RationalLinearOccurrence J)).filter
    fun o ↦ ¬ 2 ≤ (rationalLinearOccurrencePoints J X o).card
  let inactiveUnion := inactive.biUnion (rationalLinearOccurrencePoints J X)
  have hcover : underlyingRationalLinearContributionPoints J X ⊆
      inactiveUnion ∪ activeUnderlyingRationalLinearPoints J X := by
    intro z hz
    obtain ⟨o, _ho, hzo⟩ := Finset.mem_biUnion.mp hz
    by_cases ho : 2 ≤ (rationalLinearOccurrencePoints J X o).card
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr
        ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, hzo⟩
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, hzo⟩
  have hinactive : inactiveUnion.card ≤ inactive.card := by
    calc
      inactiveUnion.card ≤ ∑ o ∈ inactive,
          (rationalLinearOccurrencePoints J X o).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _o ∈ inactive, 1 := by
        apply Finset.sum_le_sum
        intro o ho
        have hnot : ¬ 2 ≤ (rationalLinearOccurrencePoints J X o).card :=
          (Finset.mem_filter.mp ho).2
        omega
      _ = inactive.card := by simp
  calc
    (underlyingRationalLinearContributionPoints J X).card ≤
        (inactiveUnion ∪ activeUnderlyingRationalLinearPoints J X).card :=
      Finset.card_le_card hcover
    _ ≤ inactiveUnion.card +
        (activeUnderlyingRationalLinearPoints J X).card :=
      Finset.card_union_le _ _
    _ ≤ inactive.card +
        (activeUnderlyingRationalLinearPoints J X).card :=
      Nat.add_le_add_right hinactive _
    _ ≤ Fintype.card (RationalLinearOccurrence J) +
        (activeUnderlyingRationalLinearPoints J X).card := by
      exact Nat.add_le_add_right
        ((Finset.card_filter_le _ _).trans_eq Finset.card_univ) _

/-! ## Internal full rational-line classification -/

/-- A rational affine Hilbert-degree-one prime curve carrying two integral
points is its complete rational affine line, with primitive integral
coordinates on all displayed integral points. -/
theorem degreeOneRationalPrimeCurve_is_fullIntegralLine
    {N : ℕ} (Q : Ideal (MvPolynomial (Fin N) ℚ))
    (hHilbert : HasAffineHilbertDimensionDegree Q 1 1)
    (S : Finset (IntVector N)) (hcard : 2 ≤ S.card)
    (hS : ∀ z ∈ S,
      (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus Q) :
    ∃ (base direction : IntVector N) (parameter : IntVector N → ℤ),
      PrimitiveDirection direction ∧
      Set.InjOn parameter (↑S : Set (IntVector N)) ∧
      (∀ z ∈ S,
        z = fun i ↦ base i + parameter z * direction i) ∧
      affineIdealZeroLocus Q =
        Set.range (fun t : ℚ ↦
          fun i ↦ (base i : ℚ) + t * (direction i : ℚ)) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hxyQ : (fun i ↦ (x i : ℚ)) ≠ (fun i ↦ (y i : ℚ)) := by
    intro h
    apply hxy
    funext i
    exact_mod_cast congrFun h i
  have hcanonical := affineIdealZeroLocus_eq_line_of_affineHilbert_degree_one
    Q hHilbert (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))
      (hS x hx) (hS y hy) hxyQ
  let w : IntVector N := fun i ↦ y i - x i
  have hw : w ≠ 0 := by
    intro hzero
    apply hxy
    funext i
    have h := congrFun hzero i
    change y i - x i = 0 at h
    exact (sub_eq_zero.mp h).symm
  obtain ⟨direction, r, hp, hr, hscale, _hbound⟩ :=
    exists_bounded_primitiveDirection_of_ne_zero w hw
  have hscale' (i : Fin N) :
      (direction i : ℚ) = r * ((y i : ℚ) - (x i : ℚ)) := by
    simpa only [w, Int.cast_sub] using hscale i
  have hline : affineIdealZeroLocus Q =
      Set.range (fun t : ℚ ↦
        fun i ↦ (x i : ℚ) + t * (direction i : ℚ)) := by
    rw [hcanonical]
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨s / r, ?_⟩
      funext i
      change (x i : ℚ) + (s / r) * (direction i : ℚ) =
        (x i : ℚ) + s * ((y i : ℚ) - (x i : ℚ))
      rw [hscale' i]
      field_simp [hr]
    · rintro ⟨t, rfl⟩
      refine ⟨t * r, ?_⟩
      funext i
      change (x i : ℚ) + (t * r) * ((y i : ℚ) - (x i : ℚ)) =
        (x i : ℚ) + t * (direction i : ℚ)
      rw [hscale' i]
      ring
  have hparameters : ∀ z ∈ S, ∃ k : ℤ,
      ∀ i, z i = x i + k * direction i := by
    intro z hz
    have hzline := hS z hz
    rw [hline] at hzline
    obtain ⟨t, ht⟩ := hzline
    apply hp.exists_integral_parameter_of_rational_line
    refine ⟨t, ?_⟩
    intro i
    have hti := congrFun ht i
    push_cast
    linarith
  let parameter : IntVector N → ℤ := fun z ↦
    if hz : z ∈ S then (hparameters z hz).choose else 0
  have hparam : ∀ z ∈ S,
      z = fun i ↦ x i + parameter z * direction i := by
    intro z hz
    funext i
    simpa only [parameter, dif_pos hz] using
      (hparameters z hz).choose_spec i
  refine ⟨x, direction, parameter, hp, ?_, hparam, hline⟩
  intro z hz z' hz' heq
  rw [hparam z hz, hparam z' hz', heq]

/-- Simultaneous full-line data for every active rational occurrence.  The
entire line lies on both its minimal component and the parent cell ideal. -/
theorem exists_activeRationalLinearOccurrence_fullIntegralLines
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N)) :
    ∃ (base direction : RationalLinearOccurrence J → IntVector N)
      (parameter : RationalLinearOccurrence J → IntVector N → ℤ),
      ∀ o ∈ activeRationalLinearOccurrences J X,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J X o) : Set (IntVector N)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J X o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1) := by
  classical
  have hdata : ∀ o : RationalLinearOccurrence J,
      ∃ (b h : IntVector N) (a : IntVector N → ℤ),
        o ∈ activeRationalLinearOccurrences J X →
          PrimitiveDirection h ∧
          Set.InjOn a
            (↑(rationalLinearOccurrencePoints J X o) : Set (IntVector N)) ∧
          (∀ z ∈ rationalLinearOccurrencePoints J X o,
            z = fun i ↦ b i + a z * h i) ∧
          affineIdealZeroLocus o.2.1 =
            Set.range (fun t : ℚ ↦
              fun i ↦ (b i : ℚ) + t * (h i : ℚ)) := by
    intro o
    by_cases ho : o ∈ activeRationalLinearOccurrences J X
    · have hcard : 2 ≤ (rationalLinearOccurrencePoints J X o).card :=
        (Finset.mem_filter.mp ho).2
      have hzero : ∀ z ∈ rationalLinearOccurrencePoints J X o,
          (fun i ↦ (z i : ℚ)) ∈ affineIdealZeroLocus o.2.1 := by
        intro z hz
        exact (mem_finitePointsOnRationalAffineIdeal_iff
          (X o.1) o.2.1 z).mp hz |>.2
      have hdegree : HasAffineHilbertDimensionDegree o.2.1 1 1 :=
        ((mem_rationalLinearAffineComponents_iff
          (J o.1) o.2.1).mp o.2.2).2
      obtain ⟨b, h, a, hp, ha, hparam, hwhole⟩ :=
        degreeOneRationalPrimeCurve_is_fullIntegralLine
          o.2.1 hdegree (rationalLinearOccurrencePoints J X o)
            hcard hzero
      exact ⟨b, h, a, fun _ ↦ ⟨hp, ha, hparam, hwhole⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ (ho h).elim⟩
  choose base direction parameter hspec using hdata
  refine ⟨base, direction, parameter, ?_⟩
  intro o ho
  have hs := hspec o ho
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro y hy
  have hyQ : y ∈ affineIdealZeroLocus o.2.1 := by
    rw [hs.2.2.2]
    exact hy
  have hQmin : o.2.1 ∈ finiteMinimalPrimes (J o.1) :=
    ((mem_rationalLinearAffineComponents_iff
      (J o.1) o.2.1).mp o.2.2).1
  have hJQ : J o.1 ≤ o.2.1 := le_of_mem_finiteMinimalPrimes hQmin
  intro f hf
  exact hyQ f (hJQ hf)

/-! ## Multiplicity-free high/low selection -/

/-- One actual active occurrence above a point in the active union. -/
def selectedActiveRationalLinearOccurrence
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ activeUnderlyingRationalLinearPoints J X}) :
    RationalLinearOccurrence J :=
  Classical.choose (Finset.mem_biUnion.mp z.2)

theorem selectedActiveRationalLinearOccurrence_mem_active
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ activeUnderlyingRationalLinearPoints J X}) :
    selectedActiveRationalLinearOccurrence J X z ∈
      activeRationalLinearOccurrences J X :=
  (Classical.choose_spec (Finset.mem_biUnion.mp z.2)).1

theorem selectedActiveRationalLinearOccurrence_point_mem
    {ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (z : {z // z ∈ activeUnderlyingRationalLinearPoints J X}) :
    z.1 ∈ rationalLinearOccurrencePoints J X
      (selectedActiveRationalLinearOccurrence J X z) :=
  (Classical.choose_spec (Finset.mem_biUnion.mp z.2)).2

/-- Exact selected low union for an arbitrary direction catalogue. -/
def activeRationalExactLowUnion
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (occurrenceDirection : RationalLinearOccurrence J → Direction) :
    Finset {z // z ∈ activeUnderlyingRationalLinearPoints J X} := by
  classical
  exact (activeUnderlyingRationalLinearPoints J X).attach.filter fun z ↦
    occurrenceDirection (selectedActiveRationalLinearOccurrence J X z) ∈
      lowDirections

/-- The selected high fibre belonging to one active occurrence. -/
def activeRationalSelectedHighFibre
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (occurrenceDirection : RationalLinearOccurrence J → Direction)
    (o : RationalLinearOccurrence J) :
    Finset {z // z ∈ activeUnderlyingRationalLinearPoints J X} := by
  classical
  exact (activeUnderlyingRationalLinearPoints J X).attach.filter fun z ↦
    occurrenceDirection (selectedActiveRationalLinearOccurrence J X z) ∉
        lowDirections ∧
      selectedActiveRationalLinearOccurrence J X z = o

/-- A selected high fibre inherits the one-line congruence bound. -/
theorem activeRationalSelectedHighFibre_card_le
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (occurrenceDirection : RationalLinearOccurrence J → Direction)
    (base direction : RationalLinearOccurrence J → IntVector N)
    (parameter : RationalLinearOccurrence J → IntVector N → ℤ)
    (hdata : ∀ o ∈ activeRationalLinearOccurrences J X,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑(rationalLinearOccurrencePoints J X o) : Set (IntVector N)) ∧
      ∀ z ∈ rationalLinearOccurrencePoints J X o,
        z = fun i ↦ base o i + parameter o z * direction o i)
    (o : RationalLinearOccurrence J)
    (ho : o ∈ activeRationalLinearOccurrences J X)
    (center : RealVector N) (R : ℝ) (m : ℕ) (hm : 0 < m)
    (residue : IntVector N)
    (hBox : ∀ z ∈ activeRationalSelectedHighFibre
        J X lowDirections occurrenceDirection o, ∀ i,
      |(z.1 i : ℝ) - center i| ≤ R)
    (hResidue : ∀ z ∈ activeRationalSelectedHighFibre
        J X lowDirections occurrenceDirection o, ∀ i,
      z.1 i ≡ residue i [ZMOD (m : ℤ)]) :
    (activeRationalSelectedHighFibre
      J X lowDirections occurrenceDirection o).card ≤
        1 + ⌈2 * R⌉₊ / (m * directionHeight (direction o)) := by
  classical
  let S := activeRationalSelectedHighFibre
    J X lowDirections occurrenceDirection o
  have hmem : ∀ z ∈ S,
      z.1 ∈ rationalLinearOccurrencePoints J X o := by
    intro z hz
    have hselected := (Finset.mem_filter.mp hz).2.2
    simpa only [hselected] using
      selectedActiveRationalLinearOccurrence_point_mem J X z
  have hParameter : Set.InjOn
      (fun z : {z // z ∈ activeUnderlyingRationalLinearPoints J X} ↦
        parameter o z.1) (↑S : Set _) := by
    intro z hz w hw hzw
    apply Subtype.ext
    exact (hdata o ho).2.1 (hmem z hz) (hmem w hw) hzw
  have hRepresentation : ∀ z ∈ S,
      z.1 = fun i ↦ base o i + parameter o z.1 * direction o i := by
    intro z hz
    exact (hdata o ho).2.2 z.1 (hmem z hz)
  apply highLineFibre_card_le_tagged S
    (fun z ↦ parameter o z.1) hParameter
      (direction o) (base o) residue center hm (hdata o ho).1
  · intro z hz i
    rw [← congrFun (hRepresentation z hz) i]
    exact hBox z hz i
  · intro z hz i
    rw [← congrFun (hRepresentation z hz) i]
    exact hResidue z hz i

/-- Multiplicity-free ledger for the rational degree-one union.  Inactive
occurrences cost one each, high points cost the stated common bound per
occurrence, and low points remain one exact finite union. -/
theorem underlyingRationalLinear_card_le_high_add_exactLow
    {ι Direction : Type*} [Fintype ι] {N : ℕ}
    [DecidableEq Direction]
    (J : ι → Ideal (MvPolynomial (Fin N) ℚ))
    (X : ι → Finset (IntVector N))
    (lowDirections : Finset Direction)
    (occurrenceDirection : RationalLinearOccurrence J → Direction)
    (highBound : ℕ)
    (hHigh : ∀ o : RationalLinearOccurrence J,
      (activeRationalSelectedHighFibre
        J X lowDirections occurrenceDirection o).card ≤ highBound) :
    (underlyingRationalLinearContributionPoints J X).card ≤
      Fintype.card (RationalLinearOccurrence J) +
      Fintype.card (RationalLinearOccurrence J) * highBound +
        (activeRationalExactLowUnion
          J X lowDirections occurrenceDirection).card := by
  classical
  let high := (activeUnderlyingRationalLinearPoints J X).attach.filter fun z ↦
    occurrenceDirection (selectedActiveRationalLinearOccurrence J X z) ∉
      lowDirections
  have hcover : high ⊆
      (Finset.univ : Finset (RationalLinearOccurrence J)).biUnion
        (activeRationalSelectedHighFibre
          J X lowDirections occurrenceDirection) := by
    intro z hz
    have hzdata := Finset.mem_filter.mp hz
    refine Finset.mem_biUnion.mpr
      ⟨selectedActiveRationalLinearOccurrence J X z,
        Finset.mem_univ _, Finset.mem_filter.mpr ⟨hzdata.1, hzdata.2, rfl⟩⟩
  have hhigh : high.card ≤
      Fintype.card (RationalLinearOccurrence J) * highBound := by
    calc
      high.card ≤
          ((Finset.univ : Finset (RationalLinearOccurrence J)).biUnion
            (activeRationalSelectedHighFibre
              J X lowDirections occurrenceDirection)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ o : RationalLinearOccurrence J,
          (activeRationalSelectedHighFibre
            J X lowDirections occurrenceDirection o).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _o : RationalLinearOccurrence J, highBound := by
        apply Finset.sum_le_sum
        intro o _ho
        exact hHigh o
      _ = Fintype.card (RationalLinearOccurrence J) * highBound := by simp
  have hpartition :
      (activeRationalExactLowUnion
          J X lowDirections occurrenceDirection).card + high.card =
        (activeUnderlyingRationalLinearPoints J X).card := by
    simpa only [activeRationalExactLowUnion, high, Finset.card_attach] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := (activeUnderlyingRationalLinearPoints J X).attach)
        (fun z ↦ occurrenceDirection
          (selectedActiveRationalLinearOccurrence J X z) ∈ lowDirections))
  have hall :=
    underlyingRationalLinearContribution_card_le_occurrences_add_active J X
  omega

/-! ## Quantitative-prefix specialization -/

/-- Literal rational degree-one union left by the degree-effective count in
all active quantitative prefix cells. -/
def quantitativePrefixPersistentRationalLinearPointUnion
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) : Finset (IntVector 3) := by
  classical
  exact active.biUnion fun o ↦
    finitePointsOnRationalLinearCurveComponents
      (rationalAffineChartIntersectionIdeal I (terminalCut o))
      (quantitativePrefixPersistentAffineCell u m cell o)

/-- The preceding union is the generic multiplicity-free rational
occurrence union on the subtype of active labels. -/
theorem quantitativePrefixPersistentRationalLinearPointUnion_eq_underlying
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) :
    quantitativePrefixPersistentRationalLinearPointUnion
        I active terminalCut u m cell =
      underlyingRationalLinearContributionPoints
        (fun o : {o // o ∈ active} ↦
          rationalAffineChartIntersectionIdeal I (terminalCut o.1))
        (fun o : {o // o ∈ active} ↦
          quantitativePrefixPersistentAffineCell u m cell o.1) := by
  classical
  rw [underlyingRationalLinearContributionPoints_eq_biUnion]
  ext z
  simp [quantitativePrefixPersistentRationalLinearPointUnion]

/-- The rational Bézout degree mass bounds all tagged degree-one
occurrences by the sum of the current cutting-degree products.  No fixed
upper bound for the cutting degrees is used. -/
theorem card_quantitativePrefixPersistent_rationalOccurrences_le_degreeSum
    {d : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I) :
    Fintype.card (RationalLinearOccurrence
      (fun o : {o // o ∈ active} ↦
        rationalAffineChartIntersectionIdeal I (terminalCut o.1))) ≤
      ∑ o ∈ active, d * terminalDegree o := by
  classical
  rw [card_rationalLinearOccurrence]
  calc
    (∑ o : {o // o ∈ active},
        (rationalLinearAffineComponents
          (rationalAffineChartIntersectionIdeal
            I (terminalCut o.1))).card) ≤
      ∑ o : {o // o ∈ active}, d * terminalDegree o.1 := by
        apply Finset.sum_le_sum
        intro o _ho
        obtain ⟨componentDegree, hcomponents, hmass⟩ :=
          projectiveSurface_rationalAffineSection_degreeMass
            I (terminalCut o.1) hprime hhom hdegree
              (hterminal o.1 o.2).1 (hterminal o.1 o.2).2
        calc
          (rationalLinearAffineComponents
              (rationalAffineChartIntersectionIdeal
                I (terminalCut o.1))).card =
              ∑ _Q ∈ rationalLinearAffineComponents
                (rationalAffineChartIntersectionIdeal
                  I (terminalCut o.1)), 1 := by simp
          _ ≤ ∑ Q ∈ rationalLinearAffineComponents
                (rationalAffineChartIntersectionIdeal
                  I (terminalCut o.1)), componentDegree Q := by
            apply Finset.sum_le_sum
            intro Q hQ
            have hQmin := (mem_rationalLinearAffineComponents_iff
              (rationalAffineChartIntersectionIdeal I (terminalCut o.1))
                Q).mp hQ |>.1
            exact (hcomponents Q hQmin).2.1
          _ ≤ ∑ Q ∈ finiteMinimalPrimes
                (rationalAffineChartIntersectionIdeal
                  I (terminalCut o.1)), componentDegree Q :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ ≤ d * terminalDegree o.1 := hmass
    _ = ∑ o ∈ active, d * terminalDegree o := by
      exact (Finset.sum_subtype active (fun _ ↦ Iff.rfl)
        (fun o ↦ d * terminalDegree o)).symm

/-- Projectivized direction of a rational line occurrence, with the same
irrelevant nonzero fallback used by the real ledger. -/
def rationalOccurrenceProjectiveDirection
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℚ))
    (direction : RationalLinearOccurrence J → IntVector 3)
    (o : RationalLinearOccurrence J) :
    Projectivization ℚ (Fin 3 → ℚ) :=
  quantitativePrefixIntegralProjectiveClassOrFirst (direction o)

/-- Distinct projective directions of active rational occurrences whose
primitive height is at most the cutoff. -/
def activeRationalLowProjectiveDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℚ))
    (X : ι → Finset (IntVector 3))
    (direction : RationalLinearOccurrence J → IntVector 3)
    (cutoff : ℕ) : Finset (Projectivization ℚ (Fin 3 → ℚ)) := by
  classical
  exact ((activeRationalLinearOccurrences J X).filter fun o ↦
    directionHeight (direction o) ≤ cutoff).image fun o ↦
      rationalOccurrenceProjectiveDirection J direction o

/-- A selected point outside the low catalogue has strict primitive height
above the cutoff. -/
theorem directionHeight_gt_cutoff_of_mem_activeRationalSelectedHigh
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 3) ℚ))
    (X : ι → Finset (IntVector 3))
    (direction : RationalLinearOccurrence J → IntVector 3)
    (cutoff : ℕ) (o : RationalLinearOccurrence J)
    (z : {z // z ∈ activeUnderlyingRationalLinearPoints J X})
    (hz : z ∈ activeRationalSelectedHighFibre J X
      (activeRationalLowProjectiveDirections J X direction cutoff)
      (rationalOccurrenceProjectiveDirection J direction) o) :
    cutoff < directionHeight (direction o) := by
  classical
  have hselected : selectedActiveRationalLinearOccurrence J X z = o :=
    (Finset.mem_filter.mp hz).2.2
  by_contra hnot
  have hle : directionHeight (direction o) ≤ cutoff := Nat.le_of_not_gt hnot
  have hoActive : o ∈ activeRationalLinearOccurrences J X := by
    rw [← hselected]
    exact selectedActiveRationalLinearOccurrence_mem_active J X z
  have hoFilter : o ∈ (activeRationalLinearOccurrences J X).filter fun c ↦
      directionHeight (direction c) ≤ cutoff :=
    Finset.mem_filter.mpr ⟨hoActive, hle⟩
  have hoLow : rationalOccurrenceProjectiveDirection J direction o ∈
      activeRationalLowProjectiveDirections J X direction cutoff :=
    Finset.mem_image.mpr ⟨o, hoFilter, rfl⟩
  exact (Finset.mem_filter.mp hz).2.1 (by
    simpa only [hselected] using hoLow)

/-- End-to-end rational line ledger for the quantitative prefix family.
The occurrence budget is the actual sum `∑ d*a_o`, so the terminal cutting
degrees may vary with the height. -/
theorem exists_quantitativePrefixPersistent_rationalProjectiveLineLedger
    {d : ℕ}
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ))
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I)
    (u : IntVector 3) (m : ℕ) (hm : 0 < m)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (B : ℝ)
    (hbox : ∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
      |(integralAffineMap u z m i : ℝ)| ≤ B)
    (cutoff : ℕ) :
    let J := fun o : {o // o ∈ active} ↦
      rationalAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} ↦
      quantitativePrefixPersistentAffineCell u m cell o.1
    ∃ (base direction : RationalLinearOccurrence J → IntVector 3)
      (parameter : RationalLinearOccurrence J → IntVector 3 → ℤ),
      (∀ o ∈ activeRationalLinearOccurrences J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
        (∀ z ∈ rationalLinearOccurrencePoints J Y o,
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℚ ↦
            fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ∧
        Set.range (fun t : ℚ ↦
          fun i ↦ (base o i : ℚ) + t * (direction o i : ℚ)) ⊆
            affineIdealZeroLocus (J o.1)) ∧
      Fintype.card (RationalLinearOccurrence J) ≤
        ∑ o ∈ active, d * terminalDegree o ∧
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) *
          (1 + ⌈2 * B⌉₊ / (m * (cutoff + 1))) +
        (activeRationalExactLowUnion J Y
          (activeRationalLowProjectiveDirections J Y direction cutoff)
          (rationalOccurrenceProjectiveDirection J direction)).card := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} ↦
    rationalAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} ↦
    quantitativePrefixPersistentAffineCell u m cell o.1
  obtain ⟨base, direction, parameter, hfull⟩ :=
    exists_activeRationalLinearOccurrence_fullIntegralLines J Y
  have hoccurrence : Fintype.card (RationalLinearOccurrence J) ≤
      ∑ o ∈ active, d * terminalDegree o :=
    card_quantitativePrefixPersistent_rationalOccurrences_le_degreeSum
      I hprime hhom hdegree active terminalDegree terminalCut hterminal
  let lowDirections :=
    activeRationalLowProjectiveDirections J Y direction cutoff
  let occurrenceDirection := rationalOccurrenceProjectiveDirection J direction
  let highBound := 1 + ⌈2 * B⌉₊ / (m * (cutoff + 1))
  have hlineData : ∀ o ∈ activeRationalLinearOccurrences J Y,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑(rationalLinearOccurrencePoints J Y o) : Set (IntVector 3)) ∧
      ∀ z ∈ rationalLinearOccurrencePoints J Y o,
        z = fun i ↦ base o i + parameter o z * direction o i := by
    intro o ho
    exact ⟨(hfull o ho).1, (hfull o ho).2.1, (hfull o ho).2.2.1⟩
  have hHigh : ∀ o : RationalLinearOccurrence J,
      (activeRationalSelectedHighFibre
        J Y lowDirections occurrenceDirection o).card ≤ highBound := by
    intro o
    by_cases ho : o ∈ activeRationalLinearOccurrences J Y
    · by_cases hempty : activeRationalSelectedHighFibre
          J Y lowDirections occurrenceDirection o = ∅
      · simp [hempty]
      · have hBox' : ∀ z ∈ activeRationalSelectedHighFibre
            J Y lowDirections occurrenceDirection o, ∀ i,
            |(z.1 i : ℝ) - (0 : RealVector 3) i| ≤ B := by
          intro z _hz i
          have hzY := selectedActiveRationalLinearOccurrence_point_mem J Y z
          have hzCell : z.1 ∈ Y
              (selectedActiveRationalLinearOccurrence J Y z).1 :=
            (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mp hzY |>.1
          change z.1 ∈ (cell
            (selectedActiveRationalLinearOccurrence J Y z).1.1).image
              (fun w ↦ integralAffineMap u w m) at hzCell
          obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hzCell
          rw [← hwz]
          simpa using hbox
            (selectedActiveRationalLinearOccurrence J Y z).1.1
            (selectedActiveRationalLinearOccurrence J Y z).1.2 w hw i
        have hResidue' : ∀ z ∈ activeRationalSelectedHighFibre
            J Y lowDirections occurrenceDirection o, ∀ i,
            z.1 i ≡ u i [ZMOD (m : ℤ)] := by
          intro z _hz i
          have hzY := selectedActiveRationalLinearOccurrence_point_mem J Y z
          have hzCell : z.1 ∈ Y
              (selectedActiveRationalLinearOccurrence J Y z).1 :=
            (mem_finitePointsOnRationalAffineIdeal_iff _ _ _).mp hzY |>.1
          change z.1 ∈ (cell
            (selectedActiveRationalLinearOccurrence J Y z).1.1).image
              (fun w ↦ integralAffineMap u w m) at hzCell
          obtain ⟨w, _hw, hwz⟩ := Finset.mem_image.mp hzCell
          rw [← hwz]
          exact (ZMod.intCast_eq_intCast_iff _ _ _).1
            (integralAffineMap_congruent u w i)
        have hraw := activeRationalSelectedHighFibre_card_le
          J Y lowDirections occurrenceDirection base direction parameter
          hlineData o ho (0 : RealVector 3) B m hm u hBox' hResidue'
        have hheight : cutoff < directionHeight (direction o) := by
          obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          exact directionHeight_gt_cutoff_of_mem_activeRationalSelectedHigh
            J Y direction cutoff o z hz
        have hheight' : cutoff + 1 ≤ directionHeight (direction o) := by omega
        have hdenpos : 0 < m * (cutoff + 1) :=
          Nat.mul_pos hm (Nat.zero_lt_succ cutoff)
        exact hraw.trans (Nat.add_le_add_left
          (Nat.div_le_div_left (Nat.mul_le_mul_left m hheight') hdenpos) 1)
    · have hempty : activeRationalSelectedHighFibre
          J Y lowDirections occurrenceDirection o = ∅ := by
        ext z
        simp only [activeRationalSelectedHighFibre, Finset.mem_filter,
          Finset.notMem_empty, iff_false]
        intro hz
        exact ho (by
          rw [← hz.2.2]
          exact selectedActiveRationalLinearOccurrence_mem_active J Y z)
      simp [hempty]
  have hledger := underlyingRationalLinear_card_le_high_add_exactLow
    J Y lowDirections occurrenceDirection highBound hHigh
  have hunion :=
    quantitativePrefixPersistentRationalLinearPointUnion_eq_underlying
      I active terminalCut u m cell
  have hresult :
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card ≤
        (∑ o ∈ active, d * terminalDegree o) +
        (∑ o ∈ active, d * terminalDegree o) * highBound +
          (activeRationalExactLowUnion
            J Y lowDirections occurrenceDirection).card := by
    calc
      (quantitativePrefixPersistentRationalLinearPointUnion
          I active terminalCut u m cell).card =
          (underlyingRationalLinearContributionPoints J Y).card :=
        congrArg Finset.card hunion
      _ ≤ Fintype.card (RationalLinearOccurrence J) +
          Fintype.card (RationalLinearOccurrence J) * highBound +
            (activeRationalExactLowUnion
              J Y lowDirections occurrenceDirection).card := hledger
      _ ≤ (∑ o ∈ active, d * terminalDegree o) +
          (∑ o ∈ active, d * terminalDegree o) * highBound +
            (activeRationalExactLowUnion
              J Y lowDirections occurrenceDirection).card := by
        exact Nat.add_le_add
          (Nat.add_le_add hoccurrence
            (Nat.mul_le_mul_right highBound hoccurrence)) (le_refl _)
  refine ⟨base, direction, parameter, hfull, hoccurrence, ?_⟩
  simpa only [lowDirections, occurrenceDirection, highBound] using hresult

end

end TranslatedDepthSeven
