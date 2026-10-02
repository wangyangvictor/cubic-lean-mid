import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.TaggedHighSpecialization

/-!
# The two-class affine-line estimate

This file gives the line calculation in the form used in the manuscript.
There are only two classes.  A direction of primitive height greater than
`X = T^(2/21)` is counted on its tagged packet occurrence.  Every remaining
direction is counted once, as a rational point of one fixed projective
fivefold.  No smooth--singular subdivision of that fivefold is made.

For one low direction, the corresponding point fibre is divided into a
fixed finite family of proper pieces.  Each piece is sent, with a displayed
bounded fibre, to the integer points of a displayed six-variable
hypersurface.  Salberger 2023, Theorem 0.4, then gives `T^(4+epsilon)`.
Salberger 2023, Theorem 0.1, gives `X^(5+epsilon)` for all low directions.
Together with the exact residue encoding of the packet occurrences and the
proved tagged-line lemma, this gives

`30/7 + 4/21 = 5*(2/21) + 4 = 94/21`.

All geometric data below are literal maps, ideals, equations, box
conditions, and fibre conditions.  In particular, neither a cardinality
bound for directions nor a bound for a proper piece is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped LinearAlgebra.Projectivization

/-! ## The exact six-residue occurrence count -/

/-- The natural upper modulus used to encode the six residue coordinates of
a packet occurrence.  The factor `2` is the literal Bertrand-window slack
`q <= 2 T^(5/7)` used in the manuscript. -/
def lineOccurrenceNaturalModulus (T : NNReal) : ℕ :=
  ⌈(2 : NNReal) * qScale T⌉₊

/-- The literal cardinality of the six-coordinate residue box. -/
def lineOccurrenceResidueBoxMajorant (T : NNReal) : ℕ :=
  (lineOccurrenceNaturalModulus T) ^ 6

/-- An injective six-residue code gives the exact `q^6` occurrence count. -/
theorem occurrence_card_le_six_residue_box
    {Occurrence : Type*} [DecidableEq Occurrence]
    (occurrences : Finset Occurrence) (T : NNReal)
    (code : Occurrence →
      Fin 6 → Fin (lineOccurrenceNaturalModulus T))
    (hcode : Set.InjOn code (↑occurrences : Set Occurrence)) :
    occurrences.card ≤ lineOccurrenceResidueBoxMajorant T := by
  classical
  have hcard : occurrences.card ≤
      Fintype.card (Fin 6 → Fin (lineOccurrenceNaturalModulus T)) := by
    exact Finset.card_le_card_of_injOn code
      (by intro x hx; simp) hcode
  simpa [lineOccurrenceResidueBoxMajorant, Fintype.card_fun,
    lineOccurrenceNaturalModulus] using hcard

/-- The six-residue box has exponent `30/7`.  The harmless ceiling is
absorbed using `ceil(2q) <= 3q` for `T >= 1`. -/
theorem lineOccurrenceResidueBoxMajorant_bound :
    UniformPowerBound
      (fun _H T ↦ (lineOccurrenceResidueBoxMajorant T : NNReal))
      lineOccurrenceExponent := by
  intro ε hε
  obtain ⟨C, hC⟩ := (primitiveOccurrenceMass_bound.const_mul 729) ε hε
  refine ⟨C, ?_⟩
  intro H T hH hT hTH
  have hq : 1 ≤ qScale T :=
    NNReal.one_le_rpow hT (by norm_num)
  have hceil :
      (⌈(2 : NNReal) * qScale T⌉₊ : NNReal) ≤ 3 * qScale T := by
    have hlt := Nat.ceil_lt_add_one
      (show 0 ≤ (2 : NNReal) * qScale T by positivity)
    have hle : (⌈(2 : NNReal) * qScale T⌉₊ : NNReal) ≤
        2 * qScale T + 1 := hlt.le
    calc
      (⌈(2 : NNReal) * qScale T⌉₊ : NNReal) ≤
          2 * qScale T + 1 := hle
      _ ≤ 2 * qScale T + qScale T := by gcongr
      _ = 3 * qScale T := by ring
  have hmajorant :
      (lineOccurrenceResidueBoxMajorant T : NNReal) ≤
        729 * primitiveOccurrenceMass H T := by
    calc
      (lineOccurrenceResidueBoxMajorant T : NNReal) =
          ((⌈(2 : NNReal) * qScale T⌉₊ : NNReal)) ^ 6 := by
            simp [lineOccurrenceResidueBoxMajorant,
              lineOccurrenceNaturalModulus]
      _ ≤ (3 * qScale T) ^ 6 := by gcongr
      _ = 729 * primitiveOccurrenceMass H T := by
        norm_num [mul_pow, primitiveOccurrenceMass]
  exact hmajorant.trans (hC H T hH hT hTH)

/-- A literal injective residue code supplies the occurrence exponent; no
occurrence-cardinality estimate is assumed. -/
theorem occurrenceCount_uniformPowerBound_of_six_residue_code
    {Occurrence : Type*} [DecidableEq Occurrence]
    (occurrences : NNReal → NNReal → Finset Occurrence)
    (code : ∀ _H T, Occurrence →
      Fin 6 → Fin (lineOccurrenceNaturalModulus T))
    (hcode : ∀ H T,
      Set.InjOn (code H T) (↑(occurrences H T) : Set Occurrence)) :
    UniformPowerBound
      (fun H T ↦ ((occurrences H T).card : NNReal))
      lineOccurrenceExponent := by
  apply UniformPowerBound.mono _ lineOccurrenceResidueBoxMajorant_bound
  intro H T
  exact_mod_cast occurrence_card_le_six_residue_box
    (occurrences H T) T (code H T) (hcode H T)

/-! ## All low directions on one fixed fivefold -/

/-- Salberger's projective theorem counts every low direction at once on a
fixed integral projective fivefold.  The only comparison data are the
literal projective point attached to a direction, its membership in the
fivefold at height `X`, and injectivity on the displayed finite set. -/
theorem lowDirectionCount_scalePowerLaw_of_salberger2023
    {Direction : Type*} [DecidableEq Direction]
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 5 d)
    (hd : 2 ≤ d)
    (directions : NNReal → NNReal → Finset Direction)
    (projectiveDirection : Direction →
      Projectivization ℚ (Fin (N + 1) → ℚ))
    (hmem : ∀ H T h, h ∈ directions H T →
      projectiveDirection h ∈
        Published.rationalProjectivePoints I (xScale T : ℝ))
    (hinjective : ∀ H T,
      Set.InjOn projectiveDirection
        (↑(directions H T) : Set Direction)) :
    ScalePowerLaw
      (fun H T ↦ ((directions H T).card : NNReal))
      (2 / 21) 5 := by
  intro ε hε
  obtain ⟨C, hCpos, hsource⟩ :=
    hSalberger N 5 d I hI hd ε hε
  let Cnn : NNReal := ⟨C, hCpos.le⟩
  refine ⟨Cnn, ?_⟩
  intro H T hH hT hTH
  have hX : (1 : ℝ) ≤ (xScale T : ℝ) := by
    exact_mod_cast NNReal.one_le_rpow hT (by norm_num : (0 : ℝ) ≤ 2 / 21)
  obtain ⟨hfinite, hcount⟩ := hsource (xScale T : ℝ) hX
  have hcard : (directions H T).card ≤
      (Published.rationalProjectivePoints I (xScale T : ℝ)).ncard := by
    calc
      (directions H T).card ≤ hfinite.toFinset.card := by
        exact Finset.card_le_card_of_injOn projectiveDirection
          (by
            intro h hh
            simpa using hmem H T h hh)
          (hinjective H T)
      _ = (Published.rationalProjectivePoints I
          (xScale T : ℝ)).ncard := by
        exact (Set.ncard_eq_toFinset_card _ hfinite).symm
  have hreal : ((directions H T).card : ℝ) ≤
      C * (xScale T : ℝ) ^ ((5 : ℝ) + ε) := by
    calc
      ((directions H T).card : ℝ) ≤
          ((Published.rationalProjectivePoints I
            (xScale T : ℝ)).ncard : ℝ) := by exact_mod_cast hcard
      _ ≤ C * (xScale T : ℝ) ^ ((5 : ℝ) + ε) := hcount
  have hnn : ((directions H T).card : NNReal) ≤
      Cnn * (xScale T) ^ ((5 : ℝ) + ε) := by
    rw [← NNReal.coe_le_coe]
    simpa [Cnn] using hreal
  have hHpow : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
  calc
    ((directions H T).card : NNReal) ≤
        Cnn * (xScale T) ^ ((5 : ℝ) + ε) := hnn
    _ ≤ Cnn * H ^ ε * (T ^ (2 / 21 : ℝ)) ^ ((5 : ℝ) + ε) := by
      simp only [xScale]
      calc
        Cnn * (T ^ (2 / 21 : ℝ)) ^ ((5 : ℝ) + ε) =
            Cnn * 1 * (T ^ (2 / 21 : ℝ)) ^ ((5 : ℝ) + ε) := by
              simp
        _ ≤ Cnn * H ^ ε *
            (T ^ (2 / 21 : ℝ)) ^ ((5 : ℝ) + ε) := by gcongr

/-- Consequently all low directions have the canonical exponent `10/21`. -/
theorem lowDirectionCount_uniformPowerBound_of_salberger2023
    {Direction : Type*} [DecidableEq Direction]
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 5 d)
    (hd : 2 ≤ d)
    (directions : NNReal → NNReal → Finset Direction)
    (projectiveDirection : Direction →
      Projectivization ℚ (Fin (N + 1) → ℚ))
    (hmem : ∀ H T h, h ∈ directions H T →
      projectiveDirection h ∈
        Published.rationalProjectivePoints I (xScale T : ℝ))
    (hinjective : ∀ H T,
      Set.InjOn projectiveDirection
        (↑(directions H T) : Set Direction)) :
    UniformPowerBound
      (fun H T ↦ ((directions H T).card : NNReal))
      lowDirectionCountExponent := by
  have hscale := lowDirectionCount_scalePowerLaw_of_salberger2023
    hSalberger I hI hd directions projectiveDirection hmem hinjective
  have hbound := ScalePowerLaw.toUniformPowerBound
    (by norm_num : (2 / 21 : ℝ) ≤ 1) hscale
  convert hbound using 1
  norm_num [lowDirectionCountExponent]

/-! ## Literal proper pieces in one low-direction fibre -/

/-- Points assigned to one member of a fixed finite proper-piece family. -/
def pointsOfProperPiece
    {Point : Type*} [DecidableEq Point] {pieceCount : ℕ}
    (points : Finset Point) (piece : Point → Fin pieceCount)
    (c : Fin pieceCount) : Finset Point :=
  points.filter fun x ↦ piece x = c

/-- The point fibre of one projective direction. -/
def simpleLowDirectionFibre
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    (points : Finset Point) (direction : Point → Direction)
    (h : Direction) : Finset Point :=
  points.filter fun x ↦ direction x = h

/-- The actual largest low-direction fibre. -/
def maximumSimpleLowDirectionFibre
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    (points : Finset Point) (directions : Finset Direction)
    (direction : Point → Direction) : ℕ :=
  directions.sup fun h ↦ (simpleLowDirectionFibre points direction h).card

theorem simpleLowDirectionFibre_card_le_maximum
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    (points : Finset Point) (directions : Finset Direction)
    (direction : Point → Direction) {h : Direction}
    (hh : h ∈ directions) :
    (simpleLowDirectionFibre points direction h).card ≤
      maximumSimpleLowDirectionFibre points directions direction := by
  exact Finset.le_sup (f := fun h ↦
    (simpleLowDirectionFibre points direction h).card) hh

/-- For a fixed piece and direction, this is the literal image under the
displayed six-coordinate projection. -/
def properPieceProjectedImage
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (points : Finset Point) (piece : Point → Fin pieceCount)
    (direction : Point → Direction)
    (projection : Direction → Point → IntVector 6)
    (c : Fin pieceCount) (h : Direction) : Finset (IntVector 6) :=
  ((pointsOfProperPiece points piece c).filter fun x ↦
      direction x = h).image (projection h)

/-- The actual largest projected image for one member of the fixed
proper-piece family.  This is merely a finite supremum of the displayed
images. -/
def maximumProperPieceProjectedImageCard
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (points : Finset Point) (directions : Finset Direction)
    (piece : Point → Fin pieceCount) (direction : Point → Direction)
    (projection : Direction → Point → IntVector 6)
    (c : Fin pieceCount) : ℕ :=
  directions.sup fun h ↦
    (properPieceProjectedImage points piece direction projection c h).card

theorem properPieceProjectedImage_card_le_maximum
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (points : Finset Point) (directions : Finset Direction)
    (piece : Point → Fin pieceCount) (direction : Point → Direction)
    (projection : Direction → Point → IntVector 6)
    (c : Fin pieceCount) {h : Direction} (hh : h ∈ directions) :
    (properPieceProjectedImage points piece direction projection c h).card ≤
      maximumProperPieceProjectedImageCard points directions piece direction
        projection c := by
  exact Finset.le_sup (f := fun h ↦
    (properPieceProjectedImage points piece direction projection c h).card) hh

/-- If every displayed proper-piece projection has fibres of cardinality at
most `D`, the largest low-direction point fibre is at most the sum of the
corresponding largest projected-image cardinalities. -/
theorem maximumSimpleLowDirectionFibre_le_sum_projected_piece_maxima
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (points : Finset Point) (directions : Finset Direction)
    (piece : Point → Fin pieceCount)
    (direction : Point → Direction)
    (projection : Fin pieceCount → Direction → Point → IntVector 6)
    (D : ℕ)
    (hProjectionFibre : ∀ c h, h ∈ directions → ∀ z,
      ((((pointsOfProperPiece points piece c).filter fun x ↦
          direction x = h).filter fun x ↦
            projection c h x = z).card ≤ D)) :
    maximumSimpleLowDirectionFibre points directions direction ≤
      ∑ c : Fin pieceCount,
        maximumProperPieceProjectedImageCard points directions piece direction
          (projection c) c * D := by
  apply Finset.sup_le
  intro h hh
  let fibre := simpleLowDirectionFibre points direction h
  have hpartition : fibre.card =
      ∑ c : Fin pieceCount,
        ((pointsOfProperPiece points piece c).filter fun x ↦
          direction x = h).card := by
    simpa [fibre, simpleLowDirectionFibre, pointsOfProperPiece,
      Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
      (Finset.card_eq_sum_card_fiberwise
        (s := fibre) (t := Finset.univ) (f := piece)
        (by intro x hx; simp))
  rw [hpartition]
  apply Finset.sum_le_sum
  intro c hc
  let S := (pointsOfProperPiece points piece c).filter fun x ↦
    direction x = h
  let image := properPieceProjectedImage points piece direction
    (projection c) c h
  have hS : S.card ≤ image.card * D :=
    finiteSet_card_le_index_card_mul_of_fibres
      S image (projection c h) D
      (by
        intro x hx
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (by
        intro z hz
        exact hProjectionFibre c h hh z)
  have himage : image.card ≤
      maximumProperPieceProjectedImageCard points directions piece direction
        (projection c) c := by
    change (properPieceProjectedImage points piece direction
      (projection c) c h).card ≤ _
    exact properPieceProjectedImage_card_le_maximum
      points directions piece direction (projection c) c hh
  exact hS.trans (Nat.mul_le_mul_right D himage)

/-- Literal box and equation assertions put a proper-piece projected image
inside the precise integer hypersurface set used in Salberger's theorem. -/
theorem properPieceProjectedImage_subset_affineHypersurfaceIntegerPoints
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (points : Finset Point) (piece : Point → Fin pieceCount)
    (direction : Point → Direction)
    (projection : Fin pieceCount → Direction → Point → IntVector 6)
    (polynomial : Fin pieceCount → Direction →
      MvPolynomial (Fin 6) ℤ)
    (T : NNReal) (c : Fin pieceCount) (h : Direction)
    (hBox : ∀ z ∈ properPieceProjectedImage points piece direction
      (projection c) c h, ∀ i, |(z i : ℝ)| ≤ T)
    (hZero : ∀ z ∈ properPieceProjectedImage points piece direction
      (projection c) c h,
        MvPolynomial.eval z (polynomial c h) = 0) :
    properPieceProjectedImage points piece direction (projection c) c h ⊆
      Published.affineHypersurfaceIntegerPoints (polynomial c h) T := by
  intro z hz
  rw [Published.affineHypersurfaceIntegerPoints]
  apply Finset.mem_filter.mpr
  refine ⟨?_, hBox z hz, hZero z hz⟩
  rw [mem_integerSupNormBox_iff]
  intro i
  have hi : ((z i).natAbs : ℝ) ≤ T := by
    simpa [Nat.cast_natAbs] using hBox z hz i
  exact_mod_cast hi.trans (Nat.le_ceil (T : ℝ))

/-- Salberger 2023, Theorem 0.4, applied to one fixed member of the
proper-piece family.  Its coefficient-uniform constant works simultaneously
for every low direction and every value of `H,T`. -/
theorem maximumProperPieceProjectedImageCard_bound_of_salberger2023
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (hSalberger : Published.Salberger2023Theorem04)
    (points : NNReal → NNReal → Finset Point)
    (directions : NNReal → NNReal → Finset Direction)
    (piece : NNReal → NNReal → Point → Fin pieceCount)
    (direction : NNReal → NNReal → Point → Direction)
    (projection : NNReal → NNReal → Direction → Point → IntVector 6)
    (c : Fin pieceCount) (d : ℕ) (hd : 4 ≤ d)
    (polynomial : NNReal → NNReal → Direction →
      MvPolynomial (Fin 6) ℤ)
    (topPart : NNReal → NNReal → Direction →
      MvPolynomial (Fin 6) ℚ)
    (hTopPart : ∀ H T h, h ∈ directions H T →
      Published.IsTopHomogeneousPart
        (polynomial H T h) (topPart H T h) d)
    (hIrreducible : ∀ H T h, h ∈ directions H T →
      Published.IsAbsolutelyIrreducible (topPart H T h))
    (hBox : ∀ H T h, h ∈ directions H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (projection H T) c h,
          ∀ i, |(z i : ℝ)| ≤ T)
    (hZero : ∀ H T h, h ∈ directions H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (projection H T) c h,
          MvPolynomial.eval z (polynomial H T h) = 0) :
    UniformPowerBound
      (fun H T ↦
        (maximumProperPieceProjectedImageCard (points H T)
          (directions H T) (piece H T) (direction H T)
          (projection H T) c : NNReal))
      starPerDirectionExponent := by
  intro ε hε
  obtain ⟨C, hCpos, hSource⟩ :=
    hSalberger 6 d (by norm_num) (Or.inr hd) ε hε
  let Cnn : NNReal := ⟨C, hCpos.le⟩
  refine ⟨Cnn, ?_⟩
  intro H T hH hT hTH
  have hOneH : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
  have hEach : ∀ h ∈ directions H T,
      ((properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (projection H T) c h).card : NNReal) ≤
          Cnn * T ^ (4 + ε) := by
    intro h hh
    let image := properPieceProjectedImage (points H T) (piece H T)
      (direction H T) (projection H T) c h
    let sourceSet := Published.affineHypersurfaceIntegerPoints
      (polynomial H T h) T
    have hsubset : image ⊆ sourceSet :=
      properPieceProjectedImage_subset_affineHypersurfaceIntegerPoints
        (points H T) (piece H T) (direction H T)
        (fun _c ↦ projection H T) (fun _c ↦ polynomial H T)
        T c h (hBox H T h hh) (hZero H T h hh)
    have hcard : image.card ≤ sourceSet.card := Finset.card_le_card hsubset
    have hTReal : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hsource := hSource (polynomial H T h) (topPart H T h)
      (hTopPart H T h hh) (hIrreducible H T h hh) T hTReal
    have hexponent : Published.salberger2023AffineExponent 6 d ε = 4 + ε := by
      norm_num [Published.salberger2023AffineExponent,
        show d ≠ 3 by omega]
    rw [hexponent] at hsource
    have hreal : (image.card : ℝ) ≤ C * (T : ℝ) ^ (4 + ε) := by
      calc
        (image.card : ℝ) ≤ (sourceSet.card : ℝ) := by exact_mod_cast hcard
        _ ≤ C * (T : ℝ) ^ (4 + ε) := hsource
    rw [← NNReal.coe_le_coe]
    simpa [Cnn] using hreal
  have hmax :
      (maximumProperPieceProjectedImageCard (points H T)
        (directions H T) (piece H T) (direction H T)
        (projection H T) c : NNReal) ≤ Cnn * T ^ (4 + ε) := by
    by_cases hempty : directions H T = ∅
    · simp [maximumProperPieceProjectedImageCard, hempty]
    · have hne : (directions H T).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨h, hh, hsup⟩ := Finset.exists_mem_eq_sup
        (directions H T) hne fun h ↦
          (properPieceProjectedImage (points H T) (piece H T)
            (direction H T) (projection H T) c h).card
      simp only [maximumProperPieceProjectedImageCard, hsup]
      exact hEach h hh
  calc
    (maximumProperPieceProjectedImageCard (points H T)
      (directions H T) (piece H T) (direction H T)
      (projection H T) c : NNReal) ≤ Cnn * T ^ (4 + ε) := hmax
    _ ≤ Cnn * H ^ ε * T ^ (4 + ε) := by
      calc
        Cnn * T ^ (4 + ε) = Cnn * 1 * T ^ (4 + ε) := by simp
        _ ≤ Cnn * H ^ ε * T ^ (4 + ε) := by gcongr
    _ = powerEnvelope Cnn H T starPerDirectionExponent ε := by
      simp [powerEnvelope, starPerDirectionExponent]

/-- Salberger's affine theorem, applied separately to the fixed finite list
of proper pieces, gives `T^(4+epsilon)` for the largest union belonging to
one low projective direction.  No cardinality bound for a piece is an
input. -/
theorem maximumSimpleLowDirectionFibre_bound_of_proper_pieces
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (hSalberger : Published.Salberger2023Theorem04)
    (points : NNReal → NNReal → Finset Point)
    (directions : NNReal → NNReal → Finset Direction)
    (piece : NNReal → NNReal → Point → Fin pieceCount)
    (direction : NNReal → NNReal → Point → Direction)
    (projection : NNReal → NNReal → Fin pieceCount →
      Direction → Point → IntVector 6)
    (D d : ℕ) (hd : 4 ≤ d)
    (polynomial : NNReal → NNReal → Fin pieceCount → Direction →
      MvPolynomial (Fin 6) ℤ)
    (topPart : NNReal → NNReal → Fin pieceCount → Direction →
      MvPolynomial (Fin 6) ℚ)
    (hProjectionFibre : ∀ H T c h, h ∈ directions H T → ∀ z,
      (((((pointsOfProperPiece (points H T) (piece H T) c).filter fun x ↦
          direction H T x = h).filter fun x ↦
            projection H T c h x = z).card ≤ D)))
    (hBox : ∀ H T c h, h ∈ directions H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (projection H T c) c h,
          ∀ i, |(z i : ℝ)| ≤ T)
    (hZero : ∀ H T c h, h ∈ directions H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (projection H T c) c h,
          MvPolynomial.eval z (polynomial H T c h) = 0)
    (hTopPart : ∀ H T c h, h ∈ directions H T →
      Published.IsTopHomogeneousPart
        (polynomial H T c h) (topPart H T c h) d)
    (hIrreducible : ∀ H T c h, h ∈ directions H T →
      Published.IsAbsolutelyIrreducible (topPart H T c h)) :
    UniformPowerBound
      (fun H T ↦
        (maximumSimpleLowDirectionFibre (points H T) (directions H T)
          (direction H T) : NNReal))
      starPerDirectionExponent := by
  have hEach : ∀ c : Fin pieceCount,
      UniformPowerBound
        (fun H T ↦
          (maximumProperPieceProjectedImageCard (points H T)
            (directions H T) (piece H T) (direction H T)
            (projection H T c) c : NNReal))
        starPerDirectionExponent := by
    intro c
    apply maximumProperPieceProjectedImageCard_bound_of_salberger2023
      hSalberger points directions piece direction
      (fun H T ↦ projection H T c) c d hd
      (fun H T h ↦ polynomial H T c h)
      (fun H T h ↦ topPart H T c h)
    · intro H T h hh
      exact hTopPart H T c h hh
    · intro H T h hh
      exact hIrreducible H T c h hh
    · exact fun H T h hh z hz i ↦ hBox H T c h hh z hz i
    · exact fun H T h hh z hz ↦ hZero H T c h hh z hz
  have hPieceSum : UniformPowerBound
      (fun H T ↦ ∑ c : Fin pieceCount,
        (maximumProperPieceProjectedImageCard (points H T)
          (directions H T) (piece H T) (direction H T)
          (projection H T c) c : NNReal) * D)
      starPerDirectionExponent := by
    apply UniformPowerBound.finset_sum Finset.univ
    intro c hc
    have hcBound := (hEach c).const_mul D
    simpa [mul_comm] using hcBound
  have hDomination : ∀ H T,
      (maximumSimpleLowDirectionFibre (points H T) (directions H T)
        (direction H T) : NNReal) ≤
        ∑ c : Fin pieceCount,
          (maximumProperPieceProjectedImageCard (points H T)
            (directions H T) (piece H T) (direction H T)
            (projection H T c) c : NNReal) * D := by
    intro H T
    have hnat :=
      maximumSimpleLowDirectionFibre_le_sum_projected_piece_maxima
        (points H T) (directions H T) (piece H T) (direction H T)
        (projection H T) D (hProjectionFibre H T)
    exact_mod_cast hnat
  have h := UniformPowerBound.mono hDomination hPieceSum
  exact h

/-! ## The complete two-class line calculation -/

/-- The high fibre attached to one occurrence, with no auxiliary
smooth--singular subdivision. -/
def simpleHighOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (lowDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (o : Occurrence) : Finset Point :=
  points.filter fun x ↦ direction x ∉ lowDirections ∧ occurrence x = o

/-- The actual largest tagged high-direction occurrence fibre. -/
def maximumSimpleHighOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (lowDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction) : ℕ :=
  occurrences.sup fun o ↦
    (simpleHighOccurrenceFibre points lowDirections occurrence direction o).card

theorem simpleHighOccurrenceFibre_eq_highOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (lowDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (o : Occurrence) :
    simpleHighOccurrenceFibre points lowDirections occurrence direction o =
      highOccurrenceFibre points lowDirections ∅ occurrence direction o := by
  ext x
  simp [simpleHighOccurrenceFibre, highOccurrenceFibre]

theorem maximumSimpleHighOccurrenceFibre_eq_maximumHighOccurrenceFibre
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (lowDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction) :
    maximumSimpleHighOccurrenceFibre points occurrences lowDirections
      occurrence direction =
    maximumHighOccurrenceFibre points occurrences lowDirections ∅
      occurrence direction := by
  simp [maximumSimpleHighOccurrenceFibre, maximumHighOccurrenceFibre,
    simpleHighOccurrenceFibre_eq_highOccurrenceFibre]

/-- The manuscript's two-class affine-line theorem.  The occurrence count,
high tagged fibre, low direction count, and low proper-piece fibre are all
derived inside the proof from the displayed source data. -/
theorem simpleLineContribution_uniformPowerBound_of_source_data
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    {n N dFivefold pieceCount : ℕ}
    (hSalbergerProjective : Published.Salberger2023Theorem01)
    (hSalbergerAffine : Published.Salberger2023Theorem04)
    (fivefoldIdeal : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hFivefold : Published.IsIntegralProjectiveVariety
      fivefoldIdeal 5 dFivefold)
    (hFivefoldDegree : 2 ≤ dFivefold)
    (points : NNReal → NNReal → Finset Point)
    (occurrences : NNReal → NNReal → Finset Occurrence)
    (lowDirections : NNReal → NNReal → Finset Direction)
    (occurrence : NNReal → NNReal → Point → Occurrence)
    (direction : NNReal → NNReal → Point → Direction)
    (occurrenceCode : ∀ _H T, Occurrence →
      Fin 6 → Fin (lineOccurrenceNaturalModulus T))
    (projectiveDirection : Direction →
      Projectivization ℚ (Fin (N + 1) → ℚ))
    (lineParameter : NNReal → NNReal → Occurrence → Point → ℤ)
    (lineDirection lineBase lineResidue :
      NNReal → NNReal → Occurrence → IntVector n)
    (lineCenter : NNReal → NNReal → Occurrence → RealVector n)
    (lineModulus : NNReal → NNReal → Occurrence → ℕ)
    (piece : NNReal → NNReal → Point → Fin pieceCount)
    (properProjection : NNReal → NNReal → Fin pieceCount →
      Direction → Point → IntVector 6)
    (projectionFibreDegree projectedHypersurfaceDegree : ℕ)
    (hProjectedHypersurfaceDegree : 4 ≤ projectedHypersurfaceDegree)
    (properPolynomial : NNReal → NNReal → Fin pieceCount →
      Direction → MvPolynomial (Fin 6) ℤ)
    (properTopPart : NNReal → NNReal → Fin pieceCount →
      Direction → MvPolynomial (Fin 6) ℚ)
    (hOccurrenceCode : ∀ H T,
      Set.InjOn (occurrenceCode H T)
        (↑(occurrences H T) : Set Occurrence))
    (hProjectiveDirection : ∀ H T h, h ∈ lowDirections H T →
      projectiveDirection h ∈
        Published.rationalProjectivePoints fivefoldIdeal (xScale T : ℝ))
    (hProjectiveDirectionInjective : ∀ H T,
      Set.InjOn projectiveDirection
        (↑(lowDirections H T) : Set Direction))
    (hOccurrence : ∀ H T x, x ∈ points H T →
      direction H T x ∉ lowDirections H T →
        occurrence H T x ∈ occurrences H T)
    (hLineParameter : ∀ H T o, o ∈ occurrences H T →
      Set.InjOn (lineParameter H T o)
        (↑(simpleHighOccurrenceFibre (points H T) (lowDirections H T)
          (occurrence H T) (direction H T) o) : Set Point))
    (hLineModulus : ∀ H T o, o ∈ occurrences H T →
      0 < lineModulus H T o)
    (hLinePrimitive : ∀ H T o, o ∈ occurrences H T →
      PrimitiveDirection (lineDirection H T o))
    (hLineHeight : ∀ H T o, o ∈ occurrences H T →
      lowDirectionNaturalRadius T <
        directionHeight (lineDirection H T o))
    (hLineBox : ∀ H T o, o ∈ occurrences H T →
      ∀ x ∈ simpleHighOccurrenceFibre (points H T) (lowDirections H T)
        (occurrence H T) (direction H T) o, ∀ i,
      |((lineBase H T o i + lineParameter H T o x *
          lineDirection H T o i : ℤ) : ℝ) - lineCenter H T o i| ≤ uScale T)
    (hLineResidue : ∀ H T o, o ∈ occurrences H T →
      ∀ x ∈ simpleHighOccurrenceFibre (points H T) (lowDirections H T)
        (occurrence H T) (direction H T) o, ∀ i,
      lineBase H T o i + lineParameter H T o x * lineDirection H T o i ≡
        lineResidue H T o i [ZMOD (lineModulus H T o : ℤ)])
    (hProjectionFibre : ∀ H T c h, h ∈ lowDirections H T → ∀ z,
      (((((pointsOfProperPiece (points H T) (piece H T) c).filter fun x ↦
          direction H T x = h).filter fun x ↦
            properProjection H T c h x = z).card ≤ projectionFibreDegree)))
    (hProperBox : ∀ H T c h, h ∈ lowDirections H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (properProjection H T c) c h,
          ∀ i, |(z i : ℝ)| ≤ T)
    (hProperZero : ∀ H T c h, h ∈ lowDirections H T →
      ∀ z ∈ properPieceProjectedImage (points H T) (piece H T)
        (direction H T) (properProjection H T c) c h,
          MvPolynomial.eval z (properPolynomial H T c h) = 0)
    (hProperTopPart : ∀ H T c h, h ∈ lowDirections H T →
      Published.IsTopHomogeneousPart
        (properPolynomial H T c h) (properTopPart H T c h)
        projectedHypersurfaceDegree)
    (hProperIrreducible : ∀ H T c h, h ∈ lowDirections H T →
      Published.IsAbsolutelyIrreducible (properTopPart H T c h)) :
    UniformPowerBound
      (fun H T ↦ ((points H T).card : NNReal))
      sharpLineExponent := by
  let highMaximum : NNReal → NNReal → ℕ := fun H T ↦
    maximumSimpleHighOccurrenceFibre (points H T) (occurrences H T)
      (lowDirections H T) (occurrence H T) (direction H T)
  let lowMaximum : NNReal → NNReal → ℕ := fun H T ↦
    maximumSimpleLowDirectionFibre (points H T) (lowDirections H T)
      (direction H T)
  have hOccurrenceCount := occurrenceCount_uniformPowerBound_of_six_residue_code
    occurrences occurrenceCode hOccurrenceCode
  have hHighMaximum : UniformPowerBound
      (fun H T ↦ (highMaximum H T : NNReal))
      highDirectionFactorExponent := by
    have h := maximumHighOccurrenceFibre_bound_of_tagged_data
      points occurrences lowDirections (fun _H _T ↦ ∅)
      occurrence direction lineParameter lineDirection lineBase lineResidue
      lineCenter lineModulus
    have hParameter' : ∀ H T o, o ∈ occurrences H T →
        Set.InjOn (lineParameter H T o)
          (↑(highOccurrenceFibre (points H T) (lowDirections H T) ∅
            (occurrence H T) (direction H T) o) : Set Point) := by
      intro H T o ho
      rw [← simpleHighOccurrenceFibre_eq_highOccurrenceFibre]
      exact hLineParameter H T o ho
    have hBox' : ∀ H T o, o ∈ occurrences H T →
        ∀ x ∈ highOccurrenceFibre (points H T) (lowDirections H T) ∅
          (occurrence H T) (direction H T) o, ∀ i,
        |((lineBase H T o i + lineParameter H T o x *
            lineDirection H T o i : ℤ) : ℝ) - lineCenter H T o i| ≤ uScale T := by
      intro H T o ho x hx i
      rw [← simpleHighOccurrenceFibre_eq_highOccurrenceFibre] at hx
      exact hLineBox H T o ho x hx i
    have hResidue' : ∀ H T o, o ∈ occurrences H T →
        ∀ x ∈ highOccurrenceFibre (points H T) (lowDirections H T) ∅
          (occurrence H T) (direction H T) o, ∀ i,
        lineBase H T o i + lineParameter H T o x * lineDirection H T o i ≡
          lineResidue H T o i [ZMOD (lineModulus H T o : ℤ)] := by
      intro H T o ho x hx i
      rw [← simpleHighOccurrenceFibre_eq_highOccurrenceFibre] at hx
      exact hLineResidue H T o ho x hx i
    have hbound := h hParameter' hLineModulus hLinePrimitive hLineHeight
      hBox' hResidue'
    simpa [highMaximum,
      maximumSimpleHighOccurrenceFibre_eq_maximumHighOccurrenceFibre]
      using hbound
  have hLowDirections := lowDirectionCount_uniformPowerBound_of_salberger2023
    hSalbergerProjective fivefoldIdeal hFivefold hFivefoldDegree
    lowDirections projectiveDirection hProjectiveDirection
    hProjectiveDirectionInjective
  have hLowMaximum : UniformPowerBound
      (fun H T ↦ (lowMaximum H T : NNReal)) starPerDirectionExponent := by
    simpa [lowMaximum] using
      maximumSimpleLowDirectionFibre_bound_of_proper_pieces
        hSalbergerAffine points lowDirections piece direction properProjection
        projectionFibreDegree projectedHypersurfaceDegree
        hProjectedHypersurfaceDegree properPolynomial properTopPart
        hProjectionFibre hProperBox hProperZero hProperTopPart
        hProperIrreducible
  have hPointwise : ∀ H T,
      ((points H T).card : NNReal) ≤
        ((occurrences H T).card : NNReal) * (highMaximum H T : NNReal) +
          ((lowDirections H T).card : NNReal) * (lowMaximum H T : NNReal) := by
    intro H T
    have hhigh : ∀ o ∈ occurrences H T,
        ((points H T).filter fun x ↦
          direction H T x ∉ lowDirections H T ∧
            occurrence H T x = o).card ≤ highMaximum H T := by
      intro o ho
      exact Finset.le_sup (f := fun o ↦
        (simpleHighOccurrenceFibre (points H T) (lowDirections H T)
          (occurrence H T) (direction H T) o).card) ho
    have hlow : ∀ h ∈ lowDirections H T,
        ((points H T).filter fun x ↦ direction H T x = h).card ≤
          lowMaximum H T := by
      intro h hh
      exact simpleLowDirectionFibre_card_le_maximum
        (points H T) (lowDirections H T) (direction H T) hh
    have hnat := linePoints_card_le_occurrences_mul_add_directions_mul
      (points H T) (occurrences H T) (lowDirections H T)
      (occurrence H T) (direction H T) (highMaximum H T) (lowMaximum H T)
      (hOccurrence H T) hhigh hlow
    exact_mod_cast hnat
  have hHigh := hOccurrenceCount.mul hHighMaximum
  rw [highDirectionExponent_eq] at hHigh
  have hLowRaw := hLowDirections.mul hLowMaximum
  have hLow : UniformPowerBound
      (fun H T ↦ ((lowDirections H T).card : NNReal) *
        (lowMaximum H T : NNReal)) sharpLineExponent := by
    convert hLowRaw using 1
    norm_num [lowDirectionCountExponent, starPerDirectionExponent,
      sharpLineExponent]
  exact UniformPowerBound.mono hPointwise (hHigh.add hLow)

end

end TranslatedDepthSeven
