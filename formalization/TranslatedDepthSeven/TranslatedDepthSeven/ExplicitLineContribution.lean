import TranslatedDepthSeven.PrimitiveLineLedger
import TranslatedDepthSeven.IntegerBoxCount
import TranslatedDepthSeven.TaggedLineCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# The explicit high--low line contribution

This file contains the finite-set calculation in the line part of the
curve--line--plane ledger.  It does not assume an aggregate estimate for the
line contribution.

The points with direction outside a prescribed finite low-height set are
summed by their packet occurrence.  The remaining points are summed by their
direction.  The low directions are further separated into smooth and
singular points of the fixed fivefold.  Smooth stars are counted from a
literal finite projection to a three-dimensional integer box.  Singular
nonvertex stars are mapped with bounded fibres to the finite hypersurface
point set to which Salberger's affine theorem is applied.  Thus no aggregate
star or line estimate is an input.

The final theorem combines the powers

`30/7 + 4/21 = 94/21`, `10/21 + 3 < 94/21`, and
`8/21 + 4 < 94/21`.

In the manuscript specialization, the low-direction set is
`H_pr(h) <= X`, where `U = T^(2/7)` and
`X = U^(1/3) = T^(2/21)`.  The tagged-line estimate gives the factor
`1 + U/X`, Salberger's projective dimension-growth theorem gives the
smooth-direction exponent `5 * (2/21) = 10/21`; on the singular locus it
gives `4 * (2/21) = 8/21`.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Sum the fibres of an explicit map into a finite index set. -/
theorem finiteSet_card_le_index_card_mul_of_fibres
    {Point Index : Type*} [DecidableEq Point] [DecidableEq Index]
    (points : Finset Point) (indices : Finset Index) (index : Point → Index)
    (fibreBound : ℕ)
    (hIndex : ∀ x ∈ points, index x ∈ indices)
    (hFibre : ∀ i ∈ indices,
      (points.filter fun x ↦ index x = i).card ≤ fibreBound) :
    points.card ≤ indices.card * fibreBound := by
  have hPartition :
      points.card = ∑ i ∈ indices,
        (points.filter fun x ↦ index x = i).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := points) (t := indices) (f := index) hIndex)
  rw [hPartition]
  calc
    (∑ i ∈ indices, (points.filter fun x ↦ index x = i).card) ≤
        ∑ _i ∈ indices, fibreBound := by
      exact Finset.sum_le_sum fun i hi ↦ hFibre i hi
    _ = indices.card * fibreBound := by simp

/-- A map with fibres of size at most `D` from a finite point set into the
integral box `[-M,M]^d` gives the elementary Noether-normalisation bound
`D(2M+1)^d`.  This is the counting step used for a smooth star once its
three-dimensional finite projection has been constructed. -/
theorem finiteSet_card_le_fibre_mul_integerBox
    {Point : Type*} [DecidableEq Point] {d : ℕ}
    (points : Finset Point) (projection : Point → IntVector d)
    (M D : ℕ)
    (hBox : ∀ x ∈ points, ∀ i, (projection x i).natAbs ≤ M)
    (hFibre : ∀ z : IntVector d,
      (points.filter fun x ↦ projection x = z).card ≤ D) :
    points.card ≤ (2 * M + 1) ^ d * D := by
  classical
  let image := points.image projection
  have hImage : ∀ x ∈ points, projection x ∈ image := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hByImage : points.card ≤ image.card * D :=
    finiteSet_card_le_index_card_mul_of_fibres
      points image projection D hImage (fun z _hz ↦ hFibre z)
  have hImageBox : image ⊆ integerSupNormBox d M := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_integerSupNormBox_iff]
    exact hBox x hx
  calc
    points.card ≤ image.card * D := hByImage
    _ ≤ (integerSupNormBox d M).card * D := by
      exact Nat.mul_le_mul_right D (Finset.card_le_card hImageBox)
    _ = (2 * M + 1) ^ d * D := by rw [card_integerSupNormBox]

/-- Transfer the proved tagged-line estimate from its integral parameter set
to any finite high-direction occurrence equipped with an injective integral
line parameter.  This is the exact bridge used to establish the high-fibre
hypothesis of the final line theorem; no high-line point count is assumed. -/
theorem highLineFibre_card_le_tagged
    {Point : Type*} [DecidableEq Point] {n : ℕ}
    (points : Finset Point) (parameter : Point → ℤ)
    (hParameter : Set.InjOn parameter (↑points : Set Point))
    (h y₀ residue : IntVector n) (center : RealVector n)
    {R : ℝ} {r : ℕ} (hr : 0 < r)
    (hPrimitive : PrimitiveDirection h)
    (hBox : ∀ x ∈ points, ∀ i,
      |((y₀ i + parameter x * h i : ℤ) : ℝ) - center i| ≤ R)
    (hResidue : ∀ x ∈ points, ∀ i,
      y₀ i + parameter x * h i ≡ residue i [ZMOD (r : ℤ)]) :
    points.card ≤ 1 + ⌈2 * R⌉₊ / (r * directionHeight h) := by
  classical
  let parameters := points.image parameter
  have hCard : parameters.card = points.card :=
    Finset.card_image_iff.mpr hParameter
  have hTagged := taggedLineParameters_card_le_realBox_directionHeight
    parameters hr hPrimitive
    (by
      intro a ha i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact hBox x hx i)
    (by
      intro a ha i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact hResidue x hx i)
  simpa [hCard] using hTagged

/-- A finite set, partitioned into high and low directions, is bounded by
the number of occurrence labels times the largest high fibre plus the number
of low directions times the largest low fibre.

This is the literal regrouping used for affine lines.  In particular, the
low-direction term is grouped by direction and therefore does not retain
packet multiplicity. -/
theorem linePoints_card_le_occurrences_mul_add_directions_mul
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (lowDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (highFibreBound lowFibreBound : ℕ)
    (hOccurrence : ∀ x ∈ points, direction x ∉ lowDirections →
      occurrence x ∈ occurrences)
    (hHighFibre : ∀ o ∈ occurrences,
      (points.filter fun x ↦
        direction x ∉ lowDirections ∧ occurrence x = o).card ≤
          highFibreBound)
    (hLowFibre : ∀ h ∈ lowDirections,
      (points.filter fun x ↦ direction x = h).card ≤ lowFibreBound) :
    points.card ≤
      occurrences.card * highFibreBound +
        lowDirections.card * lowFibreBound := by
  classical
  let highPoints := points.filter fun x ↦ direction x ∉ lowDirections
  let lowPoints := points.filter fun x ↦ direction x ∈ lowDirections
  have hHighPartition :
      highPoints.card = ∑ o ∈ occurrences,
        (highPoints.filter fun x ↦ occurrence x = o).card := by
    simpa [highPoints] using
      (Finset.card_eq_sum_card_fiberwise
        (s := highPoints) (t := occurrences) (f := occurrence)
        (by
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact hOccurrence x hx'.1 hx'.2))
  have hHigh : highPoints.card ≤ occurrences.card * highFibreBound := by
    rw [hHighPartition]
    calc
      (∑ o ∈ occurrences,
          (highPoints.filter fun x ↦ occurrence x = o).card) ≤
          ∑ _o ∈ occurrences, highFibreBound := by
            apply Finset.sum_le_sum
            intro o ho
            simpa [highPoints, Finset.filter_filter, and_assoc,
              and_left_comm, and_comm] using hHighFibre o ho
      _ = occurrences.card * highFibreBound := by simp
  have hLowPartition :
      lowPoints.card = ∑ h ∈ lowDirections,
        (lowPoints.filter fun x ↦ direction x = h).card := by
    simpa [lowPoints] using
      (Finset.card_eq_sum_card_fiberwise
        (s := lowPoints) (t := lowDirections) (f := direction)
        (by
          intro x hx
          exact (Finset.mem_filter.mp hx).2))
  have hLow : lowPoints.card ≤ lowDirections.card * lowFibreBound := by
    rw [hLowPartition]
    calc
      (∑ h ∈ lowDirections,
          (lowPoints.filter fun x ↦ direction x = h).card) ≤
          ∑ _h ∈ lowDirections, lowFibreBound := by
            apply Finset.sum_le_sum
            intro h hh
            have hsubset :
                lowPoints.filter (fun x ↦ direction x = h) ⊆
                  points.filter (fun x ↦ direction x = h) := by
              intro x hx
              simp only [lowPoints, Finset.mem_filter] at hx ⊢
              exact ⟨hx.1.1, hx.2⟩
            exact (Finset.card_le_card hsubset).trans (hLowFibre h hh)
      _ = lowDirections.card * lowFibreBound := by simp
  have hSplit : lowPoints.card + highPoints.card = points.card := by
    simpa [lowPoints, highPoints] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := points) (fun x ↦ direction x ∈ lowDirections))
  omega

/-- Exponents in the sharper smooth/singular treatment of low directions. -/
def smoothLowDirectionExponent : ℝ := 10 / 21
def smoothStarExponent : ℝ := 3
def singularLowDirectionExponent : ℝ := 8 / 21
def singularStarExponent : ℝ := 4

theorem smoothLowLineExponent_lt_sharp :
    smoothLowDirectionExponent + smoothStarExponent < sharpLineExponent := by
  norm_num [smoothLowDirectionExponent, smoothStarExponent, sharpLineExponent]

theorem singularLowLineExponent_lt_sharp :
    singularLowDirectionExponent + singularStarExponent < sharpLineExponent := by
  norm_num [singularLowDirectionExponent, singularStarExponent,
    sharpLineExponent]

/-- The elementary three-dimensional finite-projection majorant for one
smooth star. -/
def threeDimensionalProjectionMajorant
    (D : ℕ) (radius : NNReal → NNReal → ℕ) : CountFunction :=
  fun H T ↦ (D * (2 * radius H T + 1) ^ 3 : ℕ)

/-- Polynomial growth of the radius gives the expected `T^3` bound for the
literal three-dimensional box majorant.  No point-counting theorem is used
here. -/
theorem threeDimensionalProjectionMajorant_bound
    (D : ℕ) (radius : NNReal → NNReal → ℕ)
    (hRadius : UniformPowerBound
      (fun H T ↦ (radius H T : NNReal)) 1) :
    UniformPowerBound
      (threeDimensionalProjectionMajorant D radius) smoothStarExponent := by
  have hOneZero : UniformPowerBound (fun _H _T ↦ 1) 0 := by
    intro ε hε
    refine ⟨1, ?_⟩
    intro H T hH hT _hTH
    have hHpow : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
    have hTpow : 1 ≤ T ^ ε := NNReal.one_le_rpow hT hε.le
    calc
      1 = 1 * 1 := by simp
      _ ≤ H ^ ε * T ^ ε :=
        mul_le_mul hHpow hTpow (by positivity) (by positivity)
      _ = powerEnvelope 1 H T 0 ε := by simp [powerEnvelope]
  have hOne : UniformPowerBound (fun _H _T ↦ 1) 1 :=
    hOneZero.weaken (by norm_num)
  have hRadiusPlusOne : UniformPowerBound
      (fun H T ↦ (radius H T : NNReal) + 1) 1 :=
    hRadius.add hOne
  have hTwiceRadiusPlusOne : UniformPowerBound
      (fun H T ↦ 2 * ((radius H T : NNReal) + 1)) 1 :=
    hRadiusPlusOne.const_mul 2
  have hBase : UniformPowerBound
      (fun H T ↦ 2 * (radius H T : NNReal) + 1) 1 := by
    apply UniformPowerBound.mono _ hTwiceRadiusPlusOne
    intro H T
    calc
      2 * (radius H T : NNReal) + 1 ≤
          2 * (radius H T : NNReal) + 2 := by gcongr; norm_num
      _ = 2 * ((radius H T : NNReal) + 1) := by ring
  have hSquare : UniformPowerBound
      (fun H T ↦
        (2 * (radius H T : NNReal) + 1) *
          (2 * (radius H T : NNReal) + 1)) 2 := by
    have h := hBase.mul hBase
    norm_num at h ⊢
    exact h
  have hCube : UniformPowerBound
      (fun H T ↦ (2 * (radius H T : NNReal) + 1) ^ 3) 3 := by
    have h := hSquare.mul hBase
    norm_num at h ⊢
    convert h using 1
    funext H T
    ring
  have hD : UniformPowerBound
      (fun H T ↦ (D : NNReal) *
        (2 * (radius H T : NNReal) + 1) ^ 3) 3 :=
    hCube.const_mul D
  apply UniformPowerBound.mono _ hD
  intro H T
  change ((D * (2 * radius H T + 1) ^ 3 : ℕ) : NNReal) ≤ _
  norm_num

/-- Exact three-part line regrouping.  Smooth and singular low directions
are kept separate: the first admit a three-dimensional finite projection,
whereas the second are treated as proper pieces after a five-dimensional
hypersurface projection. -/
theorem linePoints_card_le_high_add_smooth_add_singular
    {Point Occurrence Direction : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (smoothDirections singularDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (highFibreBound smoothFibreBound singularFibreBound : ℕ)
    (hOccurrence : ∀ x ∈ points,
      direction x ∉ smoothDirections →
      direction x ∉ singularDirections →
        occurrence x ∈ occurrences)
    (hHighFibre : ∀ o ∈ occurrences,
      (points.filter fun x ↦
        direction x ∉ smoothDirections ∧
        direction x ∉ singularDirections ∧ occurrence x = o).card ≤
          highFibreBound)
    (hSmoothFibre : ∀ h ∈ smoothDirections,
      (points.filter fun x ↦ direction x = h).card ≤ smoothFibreBound)
    (hSingularFibre : ∀ h ∈ singularDirections,
      (points.filter fun x ↦
        direction x ∉ smoothDirections ∧ direction x = h).card ≤
          singularFibreBound) :
    points.card ≤
      occurrences.card * highFibreBound +
        smoothDirections.card * smoothFibreBound +
          singularDirections.card * singularFibreBound := by
  classical
  let smoothPoints := points.filter fun x ↦ direction x ∈ smoothDirections
  let singularPoints := points.filter fun x ↦
    direction x ∉ smoothDirections ∧ direction x ∈ singularDirections
  let highPoints := points.filter fun x ↦
    direction x ∉ smoothDirections ∧ direction x ∉ singularDirections
  have hSmooth : smoothPoints.card ≤
      smoothDirections.card * smoothFibreBound := by
    apply finiteSet_card_le_index_card_mul_of_fibres
      smoothPoints smoothDirections direction smoothFibreBound
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro h hh
      have hsubset :
          smoothPoints.filter (fun x ↦ direction x = h) ⊆
            points.filter (fun x ↦ direction x = h) := by
        intro x hx
        simp only [smoothPoints, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.2⟩
      exact (Finset.card_le_card hsubset).trans (hSmoothFibre h hh)
  have hSingular : singularPoints.card ≤
      singularDirections.card * singularFibreBound := by
    apply finiteSet_card_le_index_card_mul_of_fibres
      singularPoints singularDirections direction singularFibreBound
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.2
    · intro h hh
      have hsubset :
          singularPoints.filter (fun x ↦ direction x = h) ⊆
            points.filter (fun x ↦
              direction x ∉ smoothDirections ∧ direction x = h) := by
        intro x hx
        simp only [singularPoints, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1.1, hx.1.2.1, hx.2⟩
      exact (Finset.card_le_card hsubset).trans (hSingularFibre h hh)
  have hHigh : highPoints.card ≤
      occurrences.card * highFibreBound := by
    apply finiteSet_card_le_index_card_mul_of_fibres
      highPoints occurrences occurrence highFibreBound
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact hOccurrence x hx'.1 hx'.2.1 hx'.2.2
    · intro o ho
      simpa [highPoints, Finset.filter_filter, and_assoc,
        and_left_comm, and_comm] using hHighFibre o ho
  have hFirstSplit : smoothPoints.card +
      (points.filter fun x ↦ direction x ∉ smoothDirections).card =
        points.card := by
    simpa [smoothPoints] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := points) (fun x ↦ direction x ∈ smoothDirections))
  have hSecondSplit : singularPoints.card + highPoints.card =
      (points.filter fun x ↦ direction x ∉ smoothDirections).card := by
    let nonsmooth := points.filter fun x ↦ direction x ∉ smoothDirections
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := nonsmooth) (fun x ↦ direction x ∈ singularDirections)
    simpa [nonsmooth, singularPoints, highPoints, Finset.filter_filter,
      and_assoc, and_left_comm, and_comm] using h
  omega

/-- The same three-part regrouping with the two low-direction fibre bounds
derived from explicit finite projections.  Smooth stars are projected to a
three-dimensional integer box.  A singular nonvertex star is projected with
bounded fibres into an explicitly supplied finite hypersurface-point set;
only the cardinality of that image set is left to the affine theorem of
Salberger. -/
theorem linePoints_card_le_of_low_projection_data
    {Point Occurrence Direction ImagePoint : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    [DecidableEq ImagePoint]
    (points : Finset Point) (occurrences : Finset Occurrence)
    (smoothDirections singularDirections : Finset Direction)
    (occurrence : Point → Occurrence) (direction : Point → Direction)
    (highFibreBound : ℕ)
    (smoothRadius smoothProjectionDegree : ℕ)
    (smoothProjection : Direction → Point → IntVector 3)
    (singularImages : Direction → Finset ImagePoint)
    (singularProjection : Direction → Point → ImagePoint)
    (singularImageBound singularProjectionDegree : ℕ)
    (hOccurrence : ∀ x ∈ points,
      direction x ∉ smoothDirections →
      direction x ∉ singularDirections →
        occurrence x ∈ occurrences)
    (hHighFibre : ∀ o ∈ occurrences,
      (points.filter fun x ↦
        direction x ∉ smoothDirections ∧
        direction x ∉ singularDirections ∧ occurrence x = o).card ≤
          highFibreBound)
    (hSmoothBox : ∀ h ∈ smoothDirections, ∀ x ∈ points,
      direction x = h → ∀ i,
        (smoothProjection h x i).natAbs ≤ smoothRadius)
    (hSmoothProjectionFibre : ∀ h ∈ smoothDirections,
      ∀ z : IntVector 3,
      ((points.filter fun x ↦ direction x = h).filter fun x ↦
        smoothProjection h x = z).card ≤ smoothProjectionDegree)
    (hSingularImage : ∀ h ∈ singularDirections, ∀ x ∈ points,
      direction x ∉ smoothDirections → direction x = h →
        singularProjection h x ∈ singularImages h)
    (hSingularProjectionFibre : ∀ h ∈ singularDirections,
      ∀ z ∈ singularImages h,
      (((points.filter fun x ↦
        direction x ∉ smoothDirections ∧ direction x = h).filter fun x ↦
          singularProjection h x = z).card ≤ singularProjectionDegree))
    (hSingularImageCard : ∀ h ∈ singularDirections,
      (singularImages h).card ≤ singularImageBound) :
    points.card ≤
      occurrences.card * highFibreBound +
        smoothDirections.card *
          (smoothProjectionDegree * (2 * smoothRadius + 1) ^ 3) +
        singularDirections.card *
          (singularImageBound * singularProjectionDegree) := by
  apply linePoints_card_le_high_add_smooth_add_singular
    points occurrences smoothDirections singularDirections occurrence direction
    highFibreBound
    (smoothProjectionDegree * (2 * smoothRadius + 1) ^ 3)
    (singularImageBound * singularProjectionDegree)
    hOccurrence hHighFibre
  · intro h hh
    let S := points.filter fun x ↦ direction x = h
    have hS := finiteSet_card_le_fibre_mul_integerBox
      S (smoothProjection h) smoothRadius smoothProjectionDegree
      (by
        intro x hx i
        have hx' := Finset.mem_filter.mp hx
        exact hSmoothBox h hh x hx'.1 hx'.2 i)
      (by
        intro z
        exact hSmoothProjectionFibre h hh z)
    simpa [S, Nat.mul_comm] using hS
  · intro h hh
    let S := points.filter fun x ↦
      direction x ∉ smoothDirections ∧ direction x = h
    have hS : S.card ≤ (singularImages h).card * singularProjectionDegree :=
      finiteSet_card_le_index_card_mul_of_fibres
        S (singularImages h) (singularProjection h) singularProjectionDegree
        (by
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact hSingularImage h hh x hx'.1 hx'.2.1 hx'.2.2)
        (by
          intro z hz
          exact hSingularProjectionFibre h hh z hz)
    exact hS.trans (Nat.mul_le_mul_right singularProjectionDegree
      (hSingularImageCard h hh))

/-- The complete power calculation with low-direction star counts derived
from explicit projection data.  The only `T^4` input is the cardinality of
the projected singular hypersurface-point set; in the application this is
the direct output of Salberger's affine hypersurface theorem after the
internal finite-projection construction.  No star bound and no line-ledger
bound occurs as a hypothesis. -/
theorem lineContribution_uniformPowerBound_of_projection_data
    {Point Occurrence Direction ImagePoint : Type*}
    [DecidableEq Point] [DecidableEq Occurrence] [DecidableEq Direction]
    [DecidableEq ImagePoint]
    (points : NNReal → NNReal → Finset Point)
    (occurrences : NNReal → NNReal → Finset Occurrence)
    (smoothDirections singularDirections :
      NNReal → NNReal → Finset Direction)
    (occurrence : NNReal → NNReal → Point → Occurrence)
    (direction : NNReal → NNReal → Point → Direction)
    (highFibreBound smoothRadius singularImageBound :
      NNReal → NNReal → ℕ)
    (smoothProjectionDegree singularProjectionDegree : ℕ)
    (smoothProjection :
      NNReal → NNReal → Direction → Point → IntVector 3)
    (singularImages :
      NNReal → NNReal → Direction → Finset ImagePoint)
    (singularProjection :
      NNReal → NNReal → Direction → Point → ImagePoint)
    (hOccurrence : ∀ H T x, x ∈ points H T →
      direction H T x ∉ smoothDirections H T →
      direction H T x ∉ singularDirections H T →
        occurrence H T x ∈ occurrences H T)
    (hHighFibre : ∀ H T o, o ∈ occurrences H T →
      ((points H T).filter fun x ↦
        direction H T x ∉ smoothDirections H T ∧
        direction H T x ∉ singularDirections H T ∧
          occurrence H T x = o).card ≤ highFibreBound H T)
    (hSmoothBox : ∀ H T h, h ∈ smoothDirections H T →
      ∀ x ∈ points H T, direction H T x = h → ∀ i,
        (smoothProjection H T h x i).natAbs ≤ smoothRadius H T)
    (hSmoothProjectionFibre :
      ∀ H T h, h ∈ smoothDirections H T → ∀ z : IntVector 3,
      (((points H T).filter fun x ↦ direction H T x = h).filter fun x ↦
        smoothProjection H T h x = z).card ≤ smoothProjectionDegree)
    (hSingularImage :
      ∀ H T h, h ∈ singularDirections H T → ∀ x ∈ points H T,
      direction H T x ∉ smoothDirections H T → direction H T x = h →
        singularProjection H T h x ∈ singularImages H T h)
    (hSingularProjectionFibre :
      ∀ H T h, h ∈ singularDirections H T →
      ∀ z ∈ singularImages H T h,
      ((((points H T).filter fun x ↦
        direction H T x ∉ smoothDirections H T ∧
          direction H T x = h).filter fun x ↦
            singularProjection H T h x = z).card ≤
              singularProjectionDegree))
    (hSingularImageCard :
      ∀ H T h, h ∈ singularDirections H T →
        (singularImages H T h).card ≤ singularImageBound H T)
    (hOccurrenceMass : UniformPowerBound
      (fun H T ↦ ((occurrences H T).card : NNReal))
      lineOccurrenceExponent)
    (hTaggedHigh : UniformPowerBound
      (fun H T ↦ (highFibreBound H T : NNReal))
      highDirectionFactorExponent)
    (hSmoothDirectionCount : UniformPowerBound
      (fun H T ↦ ((smoothDirections H T).card : NNReal))
      smoothLowDirectionExponent)
    (hSmoothRadius : UniformPowerBound
      (fun H T ↦ (smoothRadius H T : NNReal)) 1)
    (hSingularDirectionCount : UniformPowerBound
      (fun H T ↦ ((singularDirections H T).card : NNReal))
      singularLowDirectionExponent)
    (hSalbergerSingularImageCount : UniformPowerBound
      (fun H T ↦ (singularImageBound H T : NNReal))
      singularStarExponent) :
    UniformPowerBound (fun H T ↦ ((points H T).card : NNReal))
      sharpLineExponent := by
  have hPointwise : ∀ H T,
      ((points H T).card : NNReal) ≤
        ((occurrences H T).card : NNReal) *
            (highFibreBound H T : NNReal) +
          ((smoothDirections H T).card : NNReal) *
            (threeDimensionalProjectionMajorant
              smoothProjectionDegree smoothRadius H T) +
          ((singularDirections H T).card : NNReal) *
            ((singularImageBound H T * singularProjectionDegree : ℕ) :
              NNReal) := by
    intro H T
    have hNat := linePoints_card_le_of_low_projection_data
        (points H T) (occurrences H T)
        (smoothDirections H T) (singularDirections H T)
        (occurrence H T) (direction H T) (highFibreBound H T)
        (smoothRadius H T) smoothProjectionDegree
        (smoothProjection H T) (singularImages H T)
        (singularProjection H T) (singularImageBound H T)
        singularProjectionDegree (hOccurrence H T) (hHighFibre H T)
        (hSmoothBox H T) (hSmoothProjectionFibre H T)
        (hSingularImage H T) (hSingularProjectionFibre H T)
        (hSingularImageCard H T)
    calc
      ((points H T).card : NNReal) ≤
          (((occurrences H T).card * highFibreBound H T +
            (smoothDirections H T).card *
              (smoothProjectionDegree * (2 * smoothRadius H T + 1) ^ 3) +
            (singularDirections H T).card *
              (singularImageBound H T * singularProjectionDegree) : ℕ) :
                NNReal) := by exact_mod_cast hNat
      _ = _ := by norm_num [threeDimensionalProjectionMajorant]
  have hHigh : UniformPowerBound
      (fun H T ↦ ((occurrences H T).card : NNReal) *
        (highFibreBound H T : NNReal)) sharpLineExponent := by
    have h := hOccurrenceMass.mul hTaggedHigh
    rw [highDirectionExponent_eq] at h
    exact h
  have hSmoothFibre : UniformPowerBound
      (threeDimensionalProjectionMajorant
        smoothProjectionDegree smoothRadius) smoothStarExponent :=
    threeDimensionalProjectionMajorant_bound
      smoothProjectionDegree smoothRadius hSmoothRadius
  have hSmoothRaw : UniformPowerBound
      (fun H T ↦ ((smoothDirections H T).card : NNReal) *
        threeDimensionalProjectionMajorant
          smoothProjectionDegree smoothRadius H T)
      (smoothLowDirectionExponent + smoothStarExponent) :=
    hSmoothDirectionCount.mul hSmoothFibre
  have hSmooth : UniformPowerBound
      (fun H T ↦ ((smoothDirections H T).card : NNReal) *
        threeDimensionalProjectionMajorant
          smoothProjectionDegree smoothRadius H T)
      sharpLineExponent :=
    hSmoothRaw.weaken smoothLowLineExponent_lt_sharp.le
  have hSingularFibre : UniformPowerBound
      (fun H T ↦
        ((singularImageBound H T * singularProjectionDegree : ℕ) : NNReal))
      singularStarExponent := by
    have h := hSalbergerSingularImageCount.const_mul singularProjectionDegree
    apply UniformPowerBound.mono _ h
    intro H T
    norm_num [Nat.mul_comm]
  have hSingularRaw : UniformPowerBound
      (fun H T ↦ ((singularDirections H T).card : NNReal) *
        ((singularImageBound H T * singularProjectionDegree : ℕ) : NNReal))
      (singularLowDirectionExponent + singularStarExponent) :=
    hSingularDirectionCount.mul hSingularFibre
  have hSingular : UniformPowerBound
      (fun H T ↦ ((singularDirections H T).card : NNReal) *
        ((singularImageBound H T * singularProjectionDegree : ℕ) : NNReal))
      sharpLineExponent :=
    hSingularRaw.weaken singularLowLineExponent_lt_sharp.le
  exact UniformPowerBound.mono hPointwise ((hHigh.add hSmooth).add hSingular)

end

end TranslatedDepthSeven
