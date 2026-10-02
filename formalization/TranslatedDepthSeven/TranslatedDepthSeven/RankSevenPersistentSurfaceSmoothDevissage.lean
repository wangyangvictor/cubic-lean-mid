import TranslatedDepthSeven.RankSevenPersistentMultiplicityRecords
import TranslatedDepthSeven.SingularLocusDevissage

/-!
# Smooth--singular devissage for one persistent surface

This file records the exact finite-set decomposition which precedes the
application of Salberger's theorem to a fixed persistent rank-seven surface.
It is deliberately qualitative.  No point-counting estimate, degree bound,
or bound for the number of irreducible components occurs here.

For a prime affine ideal `J`, a rational point is called smooth when the
corresponding prime of the literal coordinate ring `k[X] / J` belongs to
Mathlib's smooth locus.  The closed complement is defined by its vanishing
ideal.  Its finitely many minimal primes are retained as actual ideals of the
coordinate ring, and their inverse images in `k[X]` are retained as literal
ambient ideals.  A finite set of points on `J` is exactly the union of its
smooth part and the point cells cut out by these inverse-image ideals.

If the coordinate ring is a domain of Krull dimension two and its smooth
locus is nonempty, every displayed closed piece has Krull dimension strictly
less than two.  Nonemptiness of the smooth locus is the sole standard
characteristic-zero geometric input not supplied by the finite-set argument.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

local instance persistentSurfaceSmoothPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A quotient of a polynomial ring in finitely many variables over a field
is finitely presented: Noetherianity makes the defining ideal finitely
generated. -/
local instance affinePolynomialQuotientFinitePresentation
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) :
    Algebra.FinitePresentation k (MvPolynomial sigma k ⧸ J) :=
  Algebra.FinitePresentation.quotient
    ((isNoetherianRing_iff_ideal_fg (MvPolynomial sigma k)).mp
      inferInstance J)

/-- The prime of the affine coordinate ring associated with a displayed
rational point of the affine zero locus. -/
def affineIdealRationalPointPrime
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) (z : sigma -> k)
    (hz : z ∈ affineIdealZeroLocus J) :
    PrimeSpectrum (MvPolynomial sigma k ⧸ J) :=
  let point := affineQuotientRationalPoint J z
    ((mem_affineIdealZeroLocus_iff_le_ker_aeval J z).mp hz)
  ⟨RingHom.ker point.toRingHom, rationalPoint_ker_isPrime point⟩

/-- Smoothness of a displayed affine rational point, expressed in the
literal quotient coordinate ring.  The existential proof of membership in
the zero locus makes the predicate independent of proof choices. -/
def IsSmoothAffineIdealRationalPoint
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) (z : sigma -> k) : Prop :=
  ∃ hz : z ∈ affineIdealZeroLocus J,
    affineIdealRationalPointPrime J z hz ∈
      Algebra.smoothLocus k (MvPolynomial sigma k ⧸ J)

/-- The finitely many minimal components of the closed nonsmooth locus,
retained as ideals of the actual quotient coordinate ring. -/
def affineIdealSingularComponentRecords
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) :
    Finset {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)} :=
  (finiteSingularLocusComponents k
    (MvPolynomial sigma k ⧸ J)).attach

/-- The inverse image in affine space of one actual component of the closed
nonsmooth locus of `Spec(k[X] / J)`. -/
def affineIdealSingularComponentAmbientIdeal
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k))
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) :
    Ideal (MvPolynomial sigma k) :=
  Ideal.comap (Ideal.Quotient.mk J) record.1

/-- The smooth part of a finite set, for an arbitrary literal coordinate
map into affine space. -/
def affineIdealSmoothPointCell
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha) : Finset alpha :=
  X.filter fun x => IsSmoothAffineIdealRationalPoint J (coordinate x)

/-- The points of a finite set lying on the inverse image of one literal
component of the closed nonsmooth locus. -/
def affineIdealSingularComponentPointCell
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha)
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) : Finset alpha :=
  X.filter fun x => coordinate x ∈ affineIdealZeroLocus
    (affineIdealSingularComponentAmbientIdeal J record)

@[simp]
theorem mem_affineIdealSmoothPointCell_iff
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha) (x : alpha) :
    x ∈ affineIdealSmoothPointCell J coordinate X ↔
      x ∈ X ∧ IsSmoothAffineIdealRationalPoint J (coordinate x) := by
  classical
  simp [affineIdealSmoothPointCell]

@[simp]
theorem mem_affineIdealSingularComponentPointCell_iff
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha)
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) (x : alpha) :
    x ∈ affineIdealSingularComponentPointCell J coordinate X record ↔
      x ∈ X ∧ coordinate x ∈ affineIdealZeroLocus
        (affineIdealSingularComponentAmbientIdeal J record) := by
  classical
  simp [affineIdealSingularComponentPointCell]

/-- A point lies on the inverse image of a quotient ideal exactly when that
quotient ideal is contained in the prime of the corresponding rational
point. -/
theorem mem_affineIdealZeroLocus_singularAmbientIdeal_iff
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) (z : sigma -> k)
    (hz : z ∈ affineIdealZeroLocus J)
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) :
    z ∈ affineIdealZeroLocus
        (affineIdealSingularComponentAmbientIdeal J record) ↔
      record.1 ≤ (affineIdealRationalPointPrime J z hz).asIdeal := by
  let point := affineQuotientRationalPoint J z
    ((mem_affineIdealZeroLocus_iff_le_ker_aeval J z).mp hz)
  change
    (∀ f ∈ Ideal.comap (Ideal.Quotient.mk J) record.1,
      MvPolynomial.eval z f = 0) ↔
      record.1 ≤ RingHom.ker point.toRingHom
  constructor
  · intro hzero g hg
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
    rw [RingHom.mem_ker]
    exact hzero f hg
  · intro hle f hf
    have hker := hle hf
    rw [RingHom.mem_ker] at hker
    exact hker

/-- A point on one of the recorded nonsmooth components is not a smooth
point of the affine variety. -/
theorem not_isSmooth_of_mem_affineIdealSingularComponent
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) (z : sigma -> k)
    (hz : z ∈ affineIdealZeroLocus J)
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)})
    (hzrecord : z ∈ affineIdealZeroLocus
      (affineIdealSingularComponentAmbientIdeal J record)) :
    ¬ IsSmoothAffineIdealRationalPoint J z := by
  intro hsmooth
  obtain ⟨hz', hsmooth'⟩ := hsmooth
  have hproof : hz' = hz := Subsingleton.elim _ _
  subst hz'
  have hrecordLe : record.1 ≤
      (affineIdealRationalPointPrime J z hz).asIdeal :=
    (mem_affineIdealZeroLocus_singularAmbientIdeal_iff
      J z hz record).mp hzrecord
  have hsingularLe : singularLocusIdeal k
      (MvPolynomial sigma k ⧸ J) ≤ record.1 :=
    le_of_mem_finiteMinimalPrimes record.2
  have hpzero : affineIdealRationalPointPrime J z hz ∈
      PrimeSpectrum.zeroLocus
        (singularLocusIdeal k (MvPolynomial sigma k ⧸ J)) :=
    hsingularLe.trans hrecordLe
  rw [zeroLocus_singularLocusIdeal] at hpzero
  exact hpzero hsmooth'

/-- Every nonsmooth rational point on `J` lies on one of the finitely many
recorded minimal components of the closed nonsmooth locus. -/
theorem exists_singularComponentRecord_of_not_smooth
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) (z : sigma -> k)
    (hz : z ∈ affineIdealZeroLocus J)
    (hnot : ¬ IsSmoothAffineIdealRationalPoint J z) :
    ∃ record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
        L ∈ finiteSingularLocusComponents k
          (MvPolynomial sigma k ⧸ J)},
      z ∈ affineIdealZeroLocus
        (affineIdealSingularComponentAmbientIdeal J record) := by
  let point := affineIdealRationalPointPrime J z hz
  have hpnot : point ∉ Algebra.smoothLocus k
      (MvPolynomial sigma k ⧸ J) := by
    intro hp
    exact hnot ⟨hz, hp⟩
  obtain ⟨L, hL, hLpoint⟩ :=
    exists_finiteSingularLocusComponent_le k
      (MvPolynomial sigma k ⧸ J) point hpnot
  let record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)} := ⟨L, hL⟩
  refine ⟨record, ?_⟩
  exact (mem_affineIdealZeroLocus_singularAmbientIdeal_iff
    J z hz record).mpr hLpoint

/-- Exact smooth--singular decomposition of a finite point set on one
affine ideal.  The right-hand union ranges over actual minimal primes of the
closed nonsmooth locus and every point cell retains literal zero-locus
membership in the inverse-image ideal. -/
theorem finitePointSet_eq_smooth_union_singularComponents
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha)
    (hX : ∀ x ∈ X, coordinate x ∈ affineIdealZeroLocus J) :
    X = affineIdealSmoothPointCell J coordinate X ∪
      (affineIdealSingularComponentRecords J).biUnion fun record =>
        affineIdealSingularComponentPointCell J coordinate X record := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    by_cases hsmooth : IsSmoothAffineIdealRationalPoint J (coordinate x)
    · exact Finset.mem_union_left _
        ((mem_affineIdealSmoothPointCell_iff J coordinate X x).2
          ⟨hx, hsmooth⟩)
    · obtain ⟨record, hxrecord⟩ :=
        exists_singularComponentRecord_of_not_smooth
          J (coordinate x) (hX x hx) hsmooth
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨record, by simp [affineIdealSingularComponentRecords],
          (mem_affineIdealSingularComponentPointCell_iff
            J coordinate X record x).2 ⟨hx, hxrecord⟩⟩)
  · intro hx
    rcases Finset.mem_union.mp hx with hsmooth | hsingular
    · exact (mem_affineIdealSmoothPointCell_iff J coordinate X x).mp hsmooth |>.1
    · obtain ⟨record, _hrecord, hxrecord⟩ :=
        Finset.mem_biUnion.mp hsingular
      exact (mem_affineIdealSingularComponentPointCell_iff
        J coordinate X record x).mp hxrecord |>.1

/-- The smooth cell is disjoint from the union of all recorded nonsmooth
component cells. -/
theorem disjoint_smoothPointCell_singularComponentUnion
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha)
    (hX : ∀ x ∈ X, coordinate x ∈ affineIdealZeroLocus J) :
    Disjoint (affineIdealSmoothPointCell J coordinate X)
      ((affineIdealSingularComponentRecords J).biUnion fun record =>
        affineIdealSingularComponentPointCell J coordinate X record) := by
  classical
  rw [Finset.disjoint_left]
  intro x hsmooth hsingular
  obtain ⟨record, _hrecord, hxrecord⟩ :=
    Finset.mem_biUnion.mp hsingular
  have hs := (mem_affineIdealSmoothPointCell_iff
    J coordinate X x).mp hsmooth
  have hr := (mem_affineIdealSingularComponentPointCell_iff
    J coordinate X record x).mp hxrecord
  exact (not_isSmooth_of_mem_affineIdealSingularComponent
    J (coordinate x) (hX x hs.1) record hr.2) hs.2

/-- Cardinal consequence of the exact finite decomposition.  Overlaps among
distinct irreducible components are harmless and are not artificially
removed. -/
theorem card_finitePointSet_le_smooth_add_singularComponentCells
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) (coordinate : alpha -> sigma -> k)
    (X : Finset alpha)
    (hX : ∀ x ∈ X, coordinate x ∈ affineIdealZeroLocus J) :
    X.card ≤ (affineIdealSmoothPointCell J coordinate X).card +
      ∑ record ∈ affineIdealSingularComponentRecords J,
        (affineIdealSingularComponentPointCell J coordinate X record).card := by
  classical
  have hdecomposition :=
    finitePointSet_eq_smooth_union_singularComponents
      J coordinate X hX
  calc
    X.card =
        (affineIdealSmoothPointCell J coordinate X ∪
        (affineIdealSingularComponentRecords J).biUnion fun record =>
          affineIdealSingularComponentPointCell J coordinate X record).card :=
      congrArg Finset.card hdecomposition
    _ ≤
        (affineIdealSmoothPointCell J coordinate X).card +
          ((affineIdealSingularComponentRecords J).biUnion fun record =>
            affineIdealSingularComponentPointCell J coordinate X record).card :=
      Finset.card_union_le _ _
    _ ≤ (affineIdealSmoothPointCell J coordinate X).card +
        ∑ record ∈ affineIdealSingularComponentRecords J,
          (affineIdealSingularComponentPointCell
            J coordinate X record).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _

/-- The inverse image in affine space of a recorded quotient component is
prime. -/
theorem affineIdealSingularComponentAmbientIdeal_isPrime
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k))
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) :
    (affineIdealSingularComponentAmbientIdeal J record).IsPrime := by
  letI : record.1.IsPrime :=
    isPrime_of_mem_finiteMinimalPrimes record.2
  exact Ideal.comap_isPrime (Ideal.Quotient.mk J) record.1

/-- Third-isomorphism equivalence for one recorded closed component. -/
noncomputable def affineIdealSingularComponentQuotientEquiv
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k))
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) :
    (MvPolynomial sigma k ⧸
        affineIdealSingularComponentAmbientIdeal J record) ≃+*
      ((MvPolynomial sigma k ⧸ J) ⧸ record.1) := by
  let q : MvPolynomial sigma k →+* (MvPolynomial sigma k ⧸ J) :=
    Ideal.Quotient.mk J
  let f := Ideal.quotientMap record.1 q le_rfl
  exact RingEquiv.ofBijective f
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩

/-- Every recorded nonsmooth component of an affine surface has dimension
strictly below two.  The result is stated both in the quotient coordinate
ring and for its literal inverse-image ideal in affine space. -/
theorem affineSurfaceSingularComponent_dimension_lt_two
    {k : Type u} {sigma : Type v} [Field k] [Fintype sigma]
    (J : Ideal (MvPolynomial sigma k)) [J.IsPrime]
    (hsmooth : (Algebra.smoothLocus k
      (MvPolynomial sigma k ⧸ J)).Nonempty)
    (hdim : ringKrullDim (MvPolynomial sigma k ⧸ J) = 2)
    (record : {L : Ideal (MvPolynomial sigma k ⧸ J) //
      L ∈ finiteSingularLocusComponents k
        (MvPolynomial sigma k ⧸ J)}) :
    ringKrullDim ((MvPolynomial sigma k ⧸ J) ⧸ record.1) < 2 ∧
      ringKrullDim (MvPolynomial sigma k ⧸
        affineIdealSingularComponentAmbientIdeal J record) < 2 := by
  have hdrop : ringKrullDim
      ((MvPolynomial sigma k ⧸ J) ⧸ record.1) < 2 :=
    ringKrullDim_singularComponent_lt k
      (MvPolynomial sigma k ⧸ J) hsmooth record.2 hdim
  refine ⟨hdrop, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv
    (affineIdealSingularComponentQuotientEquiv J record)]
  exact hdrop

/-- The complete qualitative statement for one actual prime affine surface:
an exact finite-point decomposition, separation of the smooth and nonsmooth
parts, and strict dimension drop for every literal nonsmooth component. -/
theorem finitePointSet_primeAffineSurface_smooth_singular_decomposition
    {k : Type u} {sigma : Type v} {alpha : Type w}
    [Field k] [Fintype sigma] [DecidableEq alpha]
    (J : Ideal (MvPolynomial sigma k)) [J.IsPrime]
    (coordinate : alpha -> sigma -> k) (X : Finset alpha)
    (hX : ∀ x ∈ X, coordinate x ∈ affineIdealZeroLocus J)
    (hsmooth : (Algebra.smoothLocus k
      (MvPolynomial sigma k ⧸ J)).Nonempty)
    (hdim : ringKrullDim (MvPolynomial sigma k ⧸ J) = 2) :
    (X = affineIdealSmoothPointCell J coordinate X ∪
        (affineIdealSingularComponentRecords J).biUnion fun record =>
          affineIdealSingularComponentPointCell J coordinate X record) ∧
      Disjoint (affineIdealSmoothPointCell J coordinate X)
        ((affineIdealSingularComponentRecords J).biUnion fun record =>
          affineIdealSingularComponentPointCell J coordinate X record) ∧
      ∀ record ∈ affineIdealSingularComponentRecords J,
        ringKrullDim ((MvPolynomial sigma k ⧸ J) ⧸ record.1) < 2 ∧
          ringKrullDim (MvPolynomial sigma k ⧸
            affineIdealSingularComponentAmbientIdeal J record) < 2 := by
  refine ⟨finitePointSet_eq_smooth_union_singularComponents
      J coordinate X hX,
    disjoint_smoothPointCell_singularComponentUnion
      J coordinate X hX, ?_⟩
  intro record _hrecord
  exact affineSurfaceSingularComponent_dimension_lt_two
    J hsmooth hdim record

/-! ## The literal projective-surface affine chart used at rank seven -/

/-- The ordinary affine chart `X_0 = 1` of a projective ideal over `Q`. -/
def rationalProjectiveAffineChartIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin N) ℚ) :=
  Ideal.map rationalDehomogenizeAtZeroHom I

/-- Integral affine coordinates on the chart of a projective ideal. -/
def rationalIntegralAffineCoordinates {N : ℕ} (z : IntVector N) :
    Fin N -> ℚ := fun i => (z i : ℚ)

/-- A finite set of integral affine-chart points on a projective ideal is
covered exactly by the smooth cell of the dehomogenized affine component and
the lower-dimensional singular-component cells above. -/
theorem finiteIntegralProjectiveChartPointSet_eq_smooth_union_singularComponents
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (X : Finset (IntVector N))
    (hX : ∀ z ∈ X,
      (fun i => (integralAffineChartVector z i : ℚ)) ∈
        affineIdealZeroLocus I) :
    X = affineIdealSmoothPointCell
        (rationalProjectiveAffineChartIdeal I)
        rationalIntegralAffineCoordinates X ∪
      (affineIdealSingularComponentRecords
        (rationalProjectiveAffineChartIdeal I)).biUnion fun record =>
        affineIdealSingularComponentPointCell
          (rationalProjectiveAffineChartIdeal I)
          rationalIntegralAffineCoordinates X record := by
  apply finitePointSet_eq_smooth_union_singularComponents
  intro z hz
  exact dehomogenized_point_of_projective_affineChart_point I z (hX z hz)

end

end TranslatedDepthSeven
