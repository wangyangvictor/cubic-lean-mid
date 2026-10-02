import TranslatedDepthSeven.RankSevenDegreeOneOccurrenceBound
import TranslatedDepthSeven.NormalizedReservoirQuotientSide
import TranslatedDepthSeven.TaggedHighSpecialization
import TranslatedDepthSeven.SimpleLineSourceSpecialization

/-!
# The literal high-direction part of the rank-seven line ledger

This file connects the actual node, edge, and persistent degree-one record
cells to the elementary primitive-line estimate.  Each component occurrence
retains its own record modulus.  The reservoir lower bound, rather than any
global line-counting assertion, supplies the high-direction saving.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped LinearAlgebra.Projectivization

local instance rankSevenProjectiveDirectionDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 13 → ℚ)) := Classical.decEq _

set_option maxHeartbeats 6000000

/-- The rounded one-line bound at the normalized box radius is dominated by
the canonical high-line majorant.  The proof uses only the reservoir lower
bound and the strict high-direction height inequality. -/
theorem normalizedRankSevenLineNumerical_le_highLineNaturalMajorant
    (p : Parameters) (q : ℕ)
    (hq : manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q)
    (h : IntVector 13)
    (hheight : lowDirectionNaturalRadius (surfaceTangentRealSide p) <
      directionHeight h) :
    1 + ⌈2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ)⌉₊ /
        (q * directionHeight h) ≤
      highLineNaturalMajorant (surfaceTangentRealSide p) := by
  have hside := normalizedReservoirQuotientSide_le_two_rpow p q hq
  have hquotReal :
      (4 * surfaceTangentNaturalSide p : ℝ) / q ≤
        2 * p.T ^ (2 / 7 : ℝ) := by
    linarith
  have hquotCast :
      (((4 * surfaceTangentNaturalSide p) / q : ℕ) : ℝ) ≤
        (4 * surfaceTangentNaturalSide p : ℝ) / q := by
    calc
      (((4 * surfaceTangentNaturalSide p) / q : ℕ) : ℝ) ≤
          ((4 * surfaceTangentNaturalSide p : ℕ) : ℝ) / (q : ℝ) :=
        Nat.cast_div_le
      _ = (4 * surfaceTangentNaturalSide p : ℝ) / q := by
        norm_num
  have hscaleCeil :
      2 * p.T ^ (2 / 7 : ℝ) ≤
        (⌈2 * (uScale (surfaceTangentRealSide p) : ℝ)⌉₊ : ℝ) := by
    simpa [uScale, surfaceTangentRealSide] using
      (Nat.le_ceil (2 * p.T ^ (2 / 7 : ℝ)))
  have hquot :
      (4 * surfaceTangentNaturalSide p) / q ≤
        ⌈2 * (uScale (surfaceTangentRealSide p) : ℝ)⌉₊ := by
    exact_mod_cast hquotCast.trans (hquotReal.trans hscaleCeil)
  have hheight' :
      lowDirectionNaturalRadius (surfaceTangentRealSide p) + 1 ≤
        directionHeight h := by
    omega
  have hdenpos :
      0 < lowDirectionNaturalRadius (surfaceTangentRealSide p) + 1 :=
    Nat.zero_lt_succ _
  have hnum :
      ⌈2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ)⌉₊ =
        4 * surfaceTangentNaturalSide p := by
    have hre :
        2 * ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) =
          ((4 * surfaceTangentNaturalSide p : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hre]
    exact Nat.ceil_natCast _
  rw [hnum, ← Nat.div_div_eq_div_mul]
  apply Nat.add_le_add_left
  exact (Nat.div_le_div_right hquot).trans
    (Nat.div_le_div_left hheight' hdenpos)

/-- At the manuscript scale the canonical natural high-line majorant has
the literal exponent `4/21`. -/
theorem highLineNaturalMajorant_cast_le_eight_rpow
    (p : Parameters) :
    (highLineNaturalMajorant (surfaceTangentRealSide p) : ℝ) ≤
      8 * p.T ^ (4 / 21 : ℝ) := by
  have hmajorant := highLineNaturalMajorant_cast_le
    (surfaceTangentRealSide p) (by exact_mod_cast p.one_le_T)
  have hratio :
      uScale (surfaceTangentRealSide p) /
          xScale (surfaceTangentRealSide p) =
        (surfaceTangentRealSide p) ^ (4 / 21 : ℝ) := by
    simpa [highDirectionFactorExponent] using
      uScale_div_xScale (T := surfaceTangentRealSide p)
        (by exact_mod_cast p.one_le_T)
  have hone : (1 : NNReal) ≤
      (surfaceTangentRealSide p) ^ (4 / 21 : ℝ) :=
    NNReal.one_le_rpow (by exact_mod_cast p.one_le_T) (by norm_num)
  have hnn :
      (highLineNaturalMajorant (surfaceTangentRealSide p) : NNReal) ≤
        8 * (surfaceTangentRealSide p) ^ (4 / 21 : ℝ) := by
    calc
      (highLineNaturalMajorant (surfaceTangentRealSide p) : NNReal) ≤
          4 * primitiveTaggedHighFactor 1 (surfaceTangentRealSide p) :=
        hmajorant
      _ = 4 * (1 +
          (surfaceTangentRealSide p) ^ (4 / 21 : ℝ)) := by
        rw [primitiveTaggedHighFactor, hratio]
      _ ≤ 4 * (2 *
          (surfaceTangentRealSide p) ^ (4 / 21 : ℝ)) := by
        gcongr
        simpa [two_mul] using
          add_le_add_right hone
            ((surfaceTangentRealSide p) ^ (4 / 21 : ℝ))
      _ = 8 * (surfaceTangentRealSide p) ^ (4 / 21 : ℝ) := by ring
  exact_mod_cast hnn

/-- Multiplying the literal occurrence scale `T^(30/7)` by the proved
high-line majorant gives exactly `T^(94/21)`.  The first summand includes the
empty/singleton component overhead. -/
theorem occurrence_add_highLineNaturalMajorant_cast_le
    (p : Parameters) (count : ℕ) (C δ : ℝ)
    (hcount : (count : ℝ) ≤
      C * p.T ^ (30 / 7 : ℝ) * p.H ^ δ) :
    ((count + count *
        highLineNaturalMajorant (surfaceTangentRealSide p) : ℕ) : ℝ) ≤
      (9 * C) * p.T ^ (94 / 21 : ℝ) * p.H ^ δ := by
  let high := highLineNaturalMajorant (surfaceTangentRealSide p)
  have hTpowOne : (1 : ℝ) ≤ p.T ^ (4 / 21 : ℝ) :=
    Real.one_le_rpow p.one_le_T (by norm_num)
  have hhigh : (high : ℝ) ≤ 8 * p.T ^ (4 / 21 : ℝ) := by
    simpa only [high] using highLineNaturalMajorant_cast_le_eight_rpow p
  have hfactor : 1 + (high : ℝ) ≤
      9 * p.T ^ (4 / 21 : ℝ) := by
    linarith
  have hnonnegFactor : 0 ≤ 9 * p.T ^ (4 / 21 : ℝ) := by positivity
  calc
    ((count + count * high : ℕ) : ℝ) =
        (count : ℝ) * (1 + (high : ℝ)) := by
      push_cast
      ring
    _ ≤ (count : ℝ) * (9 * p.T ^ (4 / 21 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg count)
    _ ≤ (C * p.T ^ (30 / 7 : ℝ) * p.H ^ δ) *
          (9 * p.T ^ (4 / 21 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcount hnonnegFactor
    _ = (9 * C) *
          (p.T ^ (30 / 7 : ℝ) * p.T ^ (4 / 21 : ℝ)) * p.H ^ δ := by
      ring
    _ = (9 * C) * p.T ^ (94 / 21 : ℝ) * p.H ^ δ := by
      rw [← Real.rpow_add p.T_pos]
      norm_num

/-! ## The intrinsic projective direction of an active component -/

/-- A fixed nonzero integral vector, used only to totalize the projective
class on inactive components. -/
def rankSevenFirstCoordinateDirection : IntVector 13 :=
  fun i ↦ if i = 0 then 1 else 0

theorem rankSevenFirstCoordinateDirection_ne_zero :
    rankSevenFirstCoordinateDirection ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin 13)
  simp [rankSevenFirstCoordinateDirection] at hzero

/-- Projectivize a nonzero integral direction; the fixed first coordinate
direction is used only if the supplied vector is zero.  Active components
never take this fallback, because their directions are primitive. -/
def integralProjectiveClassOrFirstRankSeven (h : IntVector 13) :
    Projectivization ℚ (Fin 13 → ℚ) :=
  if hh : h ≠ 0 then integralProjectiveClass h hh
  else integralProjectiveClass rankSevenFirstCoordinateDirection
    rankSevenFirstCoordinateDirection_ne_zero

/-! ## The literal height of a primitive integral direction -/

/-- Bézout-primitivity implies that the gcd of the absolute coordinates is
one.  This is the exact bridge between the primitive line ledger and the
primitive-coordinate height used in Salberger's projective theorem. -/
theorem PrimitiveDirection.isPrimitiveIntVector
    {n : ℕ} {h : IntVector n} (hp : PrimitiveDirection h) :
    IsPrimitiveIntVector h := by
  obtain ⟨c, hc⟩ := hp
  have hdZ : (intVectorContent h : ℤ) ∣ (1 : ℤ) := by
    rw [← hc]
    apply Finset.dvd_sum
    intro i _hi
    exact dvd_mul_of_dvd_right
      (Int.natCast_dvd.mpr
        (Finset.gcd_dvd (s := Finset.univ)
          (f := fun j ↦ (h j).natAbs) (Finset.mem_univ i))) _
  have hdN : intVectorContent h ∣ 1 := by
    exact_mod_cast hdZ
  exact Nat.dvd_one.mp hdN

/-- Clearing denominators and dividing by content does not change the
sup-norm of an already primitive integral vector. -/
theorem primitiveRationalVectorHeight_intCast_eq_directionHeight
    {n : ℕ} {h : IntVector n} (hp : PrimitiveDirection h) :
    primitiveRationalVectorHeight (fun i ↦ (h i : ℚ)) =
      directionHeight h := by
  let v : Fin n → ℚ := fun i ↦ (h i : ℚ)
  have hh : h ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hp.exists_ne_zero
    exact hi (congrFun hz i)
  have hv : v ≠ 0 := intCast_ne_zero hh
  have habs := primitive_proportional_natAbs_eq
    (primitiveRationalVectorScale v) h
      (primitiveRationalVectorCoordinate v)
      (primitiveRationalVectorScale_ne_zero v hv)
      hp.isPrimitiveIntVector
      (primitiveRationalVectorCoordinate_isPrimitive v hv)
      (fun i ↦ primitiveRationalVectorCoordinate_cast v hv i)
  unfold primitiveRationalVectorHeight directionHeight
  apply Finset.sup_congr rfl
  intro i _hi
  exact habs i

/-- The arbitrary representative chosen by `Projectivization.rep` has the
same primitive height as the primitive integral vector defining its class. -/
theorem primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight
    {n : ℕ} {h : IntVector n} (hp : PrimitiveDirection h) (hh : h ≠ 0) :
    primitiveRationalVectorHeight (integralProjectiveClass h hh).rep =
      directionHeight h := by
  let v : Fin n → ℚ := fun i ↦ (h i : ℚ)
  have hv : v ≠ 0 := intCast_ne_zero hh
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ v hv
  have hheight := primitiveRationalVectorHeight_smul v (a : ℚ) hv
    (Units.ne_zero a)
  have ha' : (a : ℚ) • v =
      (Projectivization.mk ℚ v hv).rep := by simpa using ha
  change primitiveRationalVectorHeight
      (Projectivization.mk ℚ v _).rep = directionHeight h
  rw [← ha', hheight,
    primitiveRationalVectorHeight_intCast_eq_directionHeight hp]

/-- On an active component the totalized projective-direction definition
never uses its fallback, and its representative has exactly the integral
direction height. -/
theorem primitiveRationalVectorHeight_integralProjectiveClassOrFirstRankSeven_eq
    (h : IntVector 13) (hp : PrimitiveDirection h) :
    primitiveRationalVectorHeight
        (integralProjectiveClassOrFirstRankSeven h).rep =
      directionHeight h := by
  have hh : h ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hp.exists_ne_zero
    exact hi (congrFun hz i)
  rw [integralProjectiveClassOrFirstRankSeven, dif_pos hh]
  exact primitiveRationalVectorHeight_integralProjectiveClass_eq_directionHeight
    hp hh

/-- The projective direction attached to a tagged point is the direction of
its selected component occurrence. -/
def taggedLinearPointProjectiveDirection
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (x : TaggedLinearContributionPoint J X) :
    Projectivization ℚ (Fin 13 → ℚ) :=
  integralProjectiveClassOrFirstRankSeven
    (lineDirection (linearComponentOccurrenceOfPoint J X x))

/-- The literal finite set of projective directions of active components
whose primitive integral height is at most `floor (T^(2/21))`.  Repeated
occurrences of the same geometric direction are identified by `Finset.image`.
-/
def activeLowProjectiveDirections
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (T : NNReal) : Finset (Projectivization ℚ (Fin 13 → ℚ)) := by
  classical
  exact ((activeTaggedLinearComponents J X).filter fun o ↦
    directionHeight (lineDirection o) ≤ lowDirectionNaturalRadius T).image
      (fun o ↦ integralProjectiveClassOrFirstRankSeven (lineDirection o))

/-- Every direction in the literal low-direction image satisfies exactly
the primitive projective-height cutoff appearing in Salberger's theorem.
The proof also shows why no multiplicity or record-count assertion is hidden
in the passage to projective directions. -/
theorem activeLowProjectiveDirection_rep_height_le_xScale
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (hPrimitive : ∀ o ∈ activeTaggedLinearComponents J X,
      PrimitiveDirection (lineDirection o))
    (h : Projectivization ℚ (Fin 13 → ℚ))
    (hh : h ∈ activeLowProjectiveDirections J X lineDirection T) :
    (primitiveRationalVectorHeight h.rep : ℝ) ≤ (xScale T : ℝ) := by
  classical
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hh
  have hoActive : o ∈ activeTaggedLinearComponents J X :=
    (Finset.mem_filter.mp ho).1
  have hoHeight : directionHeight (lineDirection o) ≤
      lowDirectionNaturalRadius T := (Finset.mem_filter.mp ho).2
  calc
    (primitiveRationalVectorHeight
        (integralProjectiveClassOrFirstRankSeven (lineDirection o)).rep : ℝ) =
        (directionHeight (lineDirection o) : ℝ) := by
      exact_mod_cast
        primitiveRationalVectorHeight_integralProjectiveClassOrFirstRankSeven_eq
          (lineDirection o) (hPrimitive o hoActive)
    _ ≤ (lowDirectionNaturalRadius T : ℝ) := by exact_mod_cast hoHeight
    _ ≤ (xScale T : ℝ) := by
      simpa [lowDirectionNaturalRadius] using
        (Nat.floor_le (a := xScale T) (show 0 ≤ xScale T by positivity))

/-- A point in the high fibre of an active occurrence has genuinely high
primitive height.  This is a direct consequence of the preceding finite-set
definition, not a separate geometric hypothesis. -/
theorem directionHeight_gt_lowRadius_of_mem_activeHigh
    {ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (X : ι → Finset (IntVector 13))
    (lineDirection : TaggedLinearComponent J → IntVector 13)
    (T : NNReal)
    (o : TaggedLinearComponent J)
    (ho : o ∈ activeTaggedLinearComponents J X)
    (x : TaggedLinearContributionPoint J X)
    (hx : x ∈ activeHighTaggedLinearComponentFibre J X
      (activeLowProjectiveDirections J X lineDirection T)
      (taggedLinearPointProjectiveDirection J X lineDirection) o) :
    lowDirectionNaturalRadius T < directionHeight (lineDirection o) := by
  classical
  by_contra hnot
  have hle : directionHeight (lineDirection o) ≤
      lowDirectionNaturalRadius T := Nat.le_of_not_gt hnot
  have hoFilter : o ∈ (activeTaggedLinearComponents J X).filter fun c ↦
      directionHeight (lineDirection c) ≤ lowDirectionNaturalRadius T :=
    Finset.mem_filter.mpr ⟨ho, hle⟩
  have hoLow : integralProjectiveClassOrFirstRankSeven (lineDirection o) ∈
      activeLowProjectiveDirections J X lineDirection T :=
    Finset.mem_image.mpr ⟨o, hoFilter, rfl⟩
  have hoccurrence : linearComponentOccurrenceOfPoint J X x = o :=
    (Finset.mem_filter.mp hx).2.2
  exact (Finset.mem_filter.mp hx).2.1 (by
    simpa [taggedLinearPointProjectiveDirection, hoccurrence] using hoLow)

/-! ## Published bounds for the two literal low-direction factors -/

/-- Salberger's projective theorem bounds a literal finite subset of the
fixed fivefold.  Since the elements of `directions` are already projective
points, there is no auxiliary direction-counting interface and no
injectivity hypothesis. -/
theorem projectiveDirectionFinset_card_le_ceil_of_salberger2023
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 5 d)
    (hd : 2 ≤ d)
    (directions : Finset (Projectivization ℚ (Fin (N + 1) → ℚ)))
    (T : NNReal) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε)
    (hmem : ∀ h ∈ directions,
      h ∈ Published.rationalProjectivePoints I (xScale T : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      directions.card ≤ ⌈C * (xScale T : ℝ) ^ (5 + ε)⌉₊ := by
  classical
  obtain ⟨C, hC, hsource⟩ := hSalberger N 5 d I hI hd ε hε
  have hxNN : (1 : NNReal) ≤ xScale T :=
    NNReal.one_le_rpow hT (by norm_num : (0 : ℝ) ≤ 2 / 21)
  have hxReal : (1 : ℝ) ≤ (xScale T : ℝ) := by exact_mod_cast hxNN
  obtain ⟨hfinite, hcount⟩ := hsource (xScale T : ℝ) hxReal
  refine ⟨C, hC, ?_⟩
  have hsubset : ↑directions ⊆ Published.rationalProjectivePoints I
      (xScale T : ℝ) := by
    intro h hh
    exact hmem h hh
  have hcard : directions.card ≤
      (Published.rationalProjectivePoints I (xScale T : ℝ)).ncard := by
    simpa [Set.ncard_eq_toFinset_card _ hfinite] using
      Finset.card_le_card (s := directions) (t := hfinite.toFinset) (by
        intro h hh
        simpa using hsubset hh)
  have hreal : (directions.card : ℝ) ≤
      C * (xScale T : ℝ) ^ (5 + ε) := by
    calc
      (directions.card : ℝ) ≤
          ((Published.rationalProjectivePoints I
            (xScale T : ℝ)).ncard : ℝ) := by exact_mod_cast hcard
      _ ≤ C * (xScale T : ℝ) ^ (5 + ε) := hcount
  exact_mod_cast hreal.trans
    (Nat.le_ceil (C * (xScale T : ℝ) ^ (5 + ε)))

/-- For a fixed low projective direction, a literal finite family of proper
pieces is counted by Salberger's coefficient-uniform affine theorem.  The
only auxiliary input is a displayed projection whose fibres have size at
most `D`; the image is required pointwise to satisfy the displayed box and
hypersurface equations. -/
theorem lowDirectionFibre_card_le_of_proper_pieces_salberger2023
    {Point Direction : Type*}
    [DecidableEq Point] [DecidableEq Direction]
    {pieceCount : ℕ}
    (hSalberger : Published.Salberger2023Theorem04)
    (points : Finset Point) (directions : Finset Direction)
    (piece : Point → Fin pieceCount) (direction : Point → Direction)
    (projection : Fin pieceCount → Direction → Point → IntVector 6)
    (D d : ℕ) (hd : 4 ≤ d)
    (polynomial : Fin pieceCount → Direction →
      MvPolynomial (Fin 6) ℤ)
    (topPart : Fin pieceCount → Direction →
      MvPolynomial (Fin 6) ℚ)
    (T : NNReal) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε)
    (hProjectionFibre : ∀ c h, h ∈ directions → ∀ z,
      (((((pointsOfProperPiece points piece c).filter fun x ↦
          direction x = h).filter fun x ↦
            projection c h x = z).card ≤ D)))
    (hBox : ∀ c h, h ∈ directions →
      ∀ z ∈ properPieceProjectedImage points piece direction
        (projection c) c h, ∀ i, |(z i : ℝ)| ≤ T)
    (hZero : ∀ c h, h ∈ directions →
      ∀ z ∈ properPieceProjectedImage points piece direction
        (projection c) c h,
          MvPolynomial.eval z (polynomial c h) = 0)
    (hTopPart : ∀ c h, h ∈ directions →
      Published.IsTopHomogeneousPart
        (polynomial c h) (topPart c h) d)
    (hIrreducible : ∀ c h, h ∈ directions →
      Published.IsAbsolutelyIrreducible (topPart c h)) :
    ∃ C : ℝ, 0 < C ∧ ∀ h ∈ directions,
      (points.filter fun x ↦ direction x = h).card ≤
        pieceCount * (⌈C * (T : ℝ) ^ (4 + ε)⌉₊ * D) := by
  classical
  obtain ⟨C, hC, hsource⟩ :=
    hSalberger 6 d (by norm_num) (Or.inr hd) ε hε
  refine ⟨C, hC, ?_⟩
  intro h hh
  let imageBound : ℕ := ⌈C * (T : ℝ) ^ (4 + ε)⌉₊
  have hImage : ∀ c : Fin pieceCount,
      maximumProperPieceProjectedImageCard points directions piece direction
        (projection c) c ≤ imageBound := by
    intro c
    apply Finset.sup_le
    intro h' hh'
    let image := properPieceProjectedImage points piece direction
      (projection c) c h'
    let source := Published.affineHypersurfaceIntegerPoints
      (polynomial c h') (T : ℝ)
    have hsubset : image ⊆ source :=
      properPieceProjectedImage_subset_affineHypersurfaceIntegerPoints
        points piece direction projection polynomial T c h'
          (hBox c h' hh') (hZero c h' hh')
    have hcard : image.card ≤ source.card := Finset.card_le_card hsubset
    have hsource' := hsource (polynomial c h') (topPart c h')
      (hTopPart c h' hh') (hIrreducible c h' hh') (T : ℝ)
      (by exact_mod_cast hT)
    have hexponent : Published.salberger2023AffineExponent 6 d ε =
        4 + ε := by
      norm_num [Published.salberger2023AffineExponent,
        show d ≠ 3 by omega]
    rw [hexponent] at hsource'
    have hreal : (image.card : ℝ) ≤ C * (T : ℝ) ^ (4 + ε) := by
      calc
        (image.card : ℝ) ≤ (source.card : ℝ) := by exact_mod_cast hcard
        _ ≤ C * (T : ℝ) ^ (4 + ε) := hsource'
    exact_mod_cast hreal.trans
      (Nat.le_ceil (C * (T : ℝ) ^ (4 + ε)))
  have hfibreMax := simpleLowDirectionFibre_card_le_maximum
    points directions direction hh
  have hpieces := maximumSimpleLowDirectionFibre_le_sum_projected_piece_maxima
    points directions piece direction projection D hProjectionFibre
  calc
    (points.filter fun x ↦ direction x = h).card ≤
        maximumSimpleLowDirectionFibre points directions direction :=
      hfibreMax
    _ ≤ ∑ c : Fin pieceCount,
        maximumProperPieceProjectedImageCard points directions piece direction
          (projection c) c * D := hpieces
    _ ≤ ∑ _c : Fin pieceCount, imageBound * D := by
      apply Finset.sum_le_sum
      intro c _hc
      exact Nat.mul_le_mul_right D (hImage c)
    _ = pieceCount * (imageBound * D) := by simp

/-! ## The actual node--edge--persistent high/low ledger -/

/-- Primitive parametrization of the actual active degree-one components
discharges the entire high-direction term.  The only remaining hypothesis is
the displayed cardinality of the fibre over each *common projective low
direction*.  Thus record multiplicity occurs in the high term, while equal
low directions from different records are grouped before any estimate is
applied. -/
theorem exists_rankSevenDegreeOne_active_high_low_ledger
    (hline : StandardAG.DegreeOneAffineCurvePrimitiveParametrization)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
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
    ∃ (base lineDirection : TaggedLinearComponent J → IntVector 13)
      (parameter : TaggedLinearComponent J → IntVector 13 → ℤ),
      (∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (lineDirection o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
        ∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1),
          z = fun i ↦ base o i + parameter o z * lineDirection o i) ∧
      ∀ lowFibreBound : ℕ,
        (∀ h ∈ activeLowProjectiveDirections J Y lineDirection
            (surfaceTangentRealSide p),
          ((activeTaggedLinearContributionPoints J Y).filter fun x ↦
            taggedLinearPointProjectiveDirection J Y lineDirection x = h).card ≤
              lowFibreBound) →
        Fintype.card (TaggedLinearContributionPoint J Y) ≤
          Fintype.card (TaggedLinearComponent J) +
        Fintype.card (TaggedLinearComponent J) *
            highLineNaturalMajorant (surfaceTangentRealSide p) +
          (activeLowProjectiveDirections J Y lineDirection
            (surfaceTangentRealSide p)).card * lowFibreBound := by
  classical
  dsimp only
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
  obtain ⟨base, lineDirection, parameter, hdata⟩ :=
    exists_activeTaggedLinearComponent_primitiveParametrizations hline J Y
  refine ⟨base, lineDirection, parameter, hdata, ?_⟩
  intro lowFibreBound hLowFibre
  apply taggedLinearContribution_card_le_active_high_low_of_line_data
    J Y
    (activeLowProjectiveDirections J Y lineDirection
      (surfaceTangentRealSide p))
    (taggedLinearPointProjectiveDirection J Y lineDirection)
    base lineDirection parameter hdata
    (fun _o _i ↦ 0)
    (fun _o ↦ ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ))
    (fun o ↦ rankSevenDegreeOneIndexModulus p x₀ equations CF Cchart
      model P k markCount hP hlower X localEquations selectedVar menu markOf
        o.1)
    (assignedLinearComponentRepresentative J Y)
    (highLineNaturalMajorant (surfaceTangentRealSide p)) lowFibreBound
  · intro o _ho
    exact rankSevenDegreeOneIndexModulus_pos p x₀ equations CF Cchart model
      P k markCount hP hlower X localEquations selectedVar menu markOf o.1
  · intro o _ho x hx i
    have hxY0 : x.2.1 ∈ Y x.1 :=
      finitePointsOnLinearCurveComponents_subset (J x.1) (Y x.1) x.2.2
    have hoccurrence : linearComponentOccurrenceOfPoint J Y x = o :=
      (Finset.mem_filter.mp hx).2.2
    have hindex : x.1 = o.1 := congrArg
      (fun c : TaggedLinearComponent J ↦ c.1) hoccurrence
    have hxY : x.2.1 ∈ Y o.1 := by simpa only [hindex] using hxY0
    have hnat := rankSevenDegreeOnePointSet_coordinate_bound
      p x₀ equations CF Cchart model P k markCount hP hlower I X
        localEquations selectedVar menu markOf o.1 hxY i
    have hreal : ((x.2.1 i).natAbs : ℝ) ≤
        ((2 * surfaceTangentNaturalSide p : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_natAbs, Int.cast_abs, sub_zero] using hreal
  · intro o ho x hx i
    have hxY0 : x.2.1 ∈ Y x.1 :=
      finitePointsOnLinearCurveComponents_subset (J x.1) (Y x.1) x.2.2
    have hoccurrence : linearComponentOccurrenceOfPoint J Y x = o :=
      (Finset.mem_filter.mp hx).2.2
    have hindex : x.1 = o.1 := congrArg
      (fun c : TaggedLinearComponent J ↦ c.1) hoccurrence
    have hxY : x.2.1 ∈ Y o.1 := by simpa only [hindex] using hxY0
    have hactiveCard : 2 ≤ (assignedLinearComponentFibre J Y o).card :=
      (Finset.mem_filter.mp ho).2
    have hnonempty : (assignedLinearComponentFibre J Y o).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hrepresentative : assignedLinearComponentRepresentative J Y o ∈
        Y o.1 := assignedLinearComponentRepresentative_mem J Y o hnonempty
    have hcongr := rankSevenDegreeOnePointSet_pair_congruent
      p x₀ equations CF Cchart model P k markCount hP hlower I X
        localEquations selectedVar menu markOf o.1 hxY hrepresentative
    exact (ZMod.intCast_eq_intCast_iff _ _ _).1 (hcongr i)
  · intro o ho hnonempty
    obtain ⟨x, hx⟩ := hnonempty
    have hheight := directionHeight_gt_lowRadius_of_mem_activeHigh
      J Y lineDirection (surfaceTangentRealSide p) o ho x hx
    exact normalizedRankSevenLineNumerical_le_highLineNaturalMajorant
      p
      (rankSevenDegreeOneIndexModulus p x₀ equations CF Cchart model P k
        markCount hP hlower X localEquations selectedVar menu markOf o.1)
      (rankSevenDegreeOneIndexModulus_lower p x₀ equations CF Cchart model
        P k markCount hP hlower X localEquations selectedVar menu markOf o.1)
      (lineDirection o) hheight
  · exact hLowFibre

end

end TranslatedDepthSeven
