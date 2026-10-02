import CubicTenVariables.HighTableSurfaceSlicingSeparated
import CubicTenVariables.FixedConeSurfaceSliceAggregation
import CubicTenVariables.HomogeneousProgressionBoxCount
import TranslatedDepthSeven.StrictRootTheorem

/-!
# Dimension-correct affine-four projection for good threefold fibres

The good fibres in `RationalSurfaceSlicingCertificate` have affine dimension
three.  Their determinant-method image must therefore be a hypersurface in
four affine coordinates.  This file gives the exact coordinate adapter to
Salberger's coefficient-uniform affine-hypersurface theorem.

The algebraic input below is deliberately pointwise and concrete.  It asks
for an integral four-coordinate linear map, a uniform bound on every finite
fibre of that map, and, after recentering one residue class, a displayed
integral hypersurface equation whose rational top homogeneous part is
absolutely irreducible.  Its sole cardinality premise is the displayed
uniform bound on each projection fibre; it contains no global box,
progression, or target-count estimate.  The proof forms the normalized
projection, checks its box, equation and fibres, and invokes
`Published.Salberger2023Theorem04` in ambient dimension four.  Its exponent
is exactly `2 + epsilon`.

Thus the remaining geometric statement is sharply isolated: jointly choose
the rational surface slicing and construct these bounded affine-four models,
uniformly over its good fibres, for each actual high-degree component.  This
is the dimensionally correct finite-projection/spreading assertion.  A
projection to three affine coordinates, as in the separate fixed-surface
adapter, is insufficient for a general affine threefold.

The classical ingredients behind this model boundary are Hartshorne,
*Algebraic Geometry*, Proposition I.4.9 (a birational hypersurface model),
Stacks Project, Algebra Lemma 10.115.4, Tag 00OW, and Varieties Lemma
33.18.2, Tag 0CBG (Noether normalization and finite projection in a family),
Stacks Project, Intersection Theory Lemma 43.23.1, Tag 0B1N (finite linear
projection from a centre outside the projective variety, in the stated
complex setting), and Hartshorne, Theorem I.7.7 (degree control under linear
sections/projection).  These references supply the standard geometric
ingredients.  They do not state verbatim the single uniform rational
integral-matrix, fibre-cardinality and translated-integral-equation package
used below.  That rational choice, uniform boundedness and coordinate
bookkeeping remain exactly the explicit premise
`AffineFourProjectionModelsN10`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace CubicTenVariables.GoodSurfaceFibreAffineFourProjection

open MvPolynomial TranslatedDepthSeven Published
open FixedConeSurfaceSliceAggregation
open FixedConeSurfaceSlicingReduction
open ConeComponentSurfaceSlicingEndpoint
open HessianTheorem11 PolynomialExponentialFamily

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coefficient-uniform bounded-degree version of Salberger's theorem in
four affine coordinates, with an arbitrary fixed fibre multiplicity. -/
theorem finiteSet_card_le_salberger2023_affineFour_boundedDegree
    {Point : Type*} [DecidableEq Point]
    (salberger : Salberger2023Theorem04)
    (degreeBound fibreBound : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ degree : ℕ, 4 ≤ degree → degree ≤ degreeBound →
        ∀ (f : MvPolynomial (Fin 4) ℤ)
          (topPart : MvPolynomial (Fin 4) ℚ),
          IsTopHomogeneousPart f topPart degree →
          IsAbsolutelyIrreducible topPart →
          ∀ B : ℝ, 1 ≤ B →
            ∀ (points : Finset Point) (projection : Point → IntVector 4),
              (∀ x ∈ points,
                projection x ∈ affineHypersurfaceIntegerPoints f B) →
              (∀ z ∈ affineHypersurfaceIntegerPoints f B,
                (points.filter fun x => projection x = z).card ≤ fibreBound) →
              (points.card : ℝ) ≤ C * B ^ ((2 : ℝ) + epsilon) := by
  classical
  let degreeSet : Finset ℕ := Finset.Icc 4 degreeBound
  let Degree := {degree : ℕ // degree ∈ degreeSet}
  have hEach : ∀ degree : Degree, ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 4) ℤ)
        (topPart : MvPolynomial (Fin 4) ℚ),
        IsTopHomogeneousPart f topPart degree.1 →
        IsAbsolutelyIrreducible topPart →
        ∀ B : ℝ, 1 ≤ B →
          ∀ (points : Finset Point) (projection : Point → IntVector 4),
            (∀ x ∈ points,
              projection x ∈ affineHypersurfaceIntegerPoints f B) →
            (∀ z ∈ affineHypersurfaceIntegerPoints f B,
              (points.filter fun x => projection x = z).card ≤ fibreBound) →
            (points.card : ℝ) ≤ C * B ^ ((2 : ℝ) + epsilon) := by
    intro degree
    have hdegree : 4 ≤ degree.1 :=
      (Finset.mem_Icc.mp (show degree.1 ∈ Finset.Icc 4 degreeBound from
        degree.2)).1
    obtain ⟨C, hC, hbound⟩ :=
      finiteSet_card_le_salberger2023_affineHypersurface
        (Point := Point) salberger 4 degree.1 fibreBound (by omega)
          (Or.inr hdegree) epsilon hepsilon
    refine ⟨C, hC, ?_⟩
    intro f topPart htop hirred B hB points projection himage hfibre
    have h := hbound f topPart htop hirred B hB points projection
      himage hfibre
    convert h using 1
    norm_num [salberger2023AffineExponent,
      (show degree.1 ≠ 3 by omega)]
  choose c hc hbound using hEach
  let C : ℝ := 1 + ∑ degree : Degree, c degree
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ degree : Degree, c degree :=
      Finset.sum_nonneg fun degree _ => (hc degree).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro degree hdegree hdegreeBound f topPart htop hirred B hB points
    projection himage hfibre
  have hdegreeMem : degree ∈ degreeSet := by
    simp only [degreeSet, Finset.mem_Icc]
    exact ⟨hdegree, hdegreeBound⟩
  let degree' : Degree := ⟨degree, hdegreeMem⟩
  have hcSum : c degree' ≤ ∑ e : Degree, c e := by
    exact Finset.single_le_sum
      (fun e _ => (hc e).le) (Finset.mem_univ degree')
  have hcC : c degree' ≤ C := by
    dsimp only [C]
    linarith
  exact (hbound degree' f topPart (by simpa [degree'] using htop)
    hirred B hB points projection himage hfibre).trans
      (mul_le_mul_of_nonneg_right hcC
        (Real.rpow_nonneg (by positivity) _))

/-- The normalized four-coordinate image of `x`, based at the projected
point `A x0`, in a common modulus-`m` residue class. -/
def normalizedProjection
    (A : Matrix (Fin 4) (Fin 10) ℤ) (x0 x : Fin 10 → ℤ) (m : ℕ) :
    IntVector 4 :=
  fun i => (A.mulVec x i - A.mulVec x0 i) / (m : ℤ)

/-- Exact reconstruction of the projected point after normalization. -/
theorem integralAffineMap_normalizedProjection
    (A : Matrix (Fin 4) (Fin 10) ℤ)
    (x x0 b : Fin 10 → ℤ) (m : ℕ)
    (hx : ∀ i, (m : ℤ) ∣ x i - b i)
    (hx0 : ∀ i, (m : ℤ) ∣ x0 i - b i) :
    integralAffineMap (A.mulVec x0) (normalizedProjection A x0 x m) m =
      A.mulVec x := by
  have hdiv : ∀ i, (m : ℤ) ∣ A.mulVec x i - A.mulVec x0 i := by
    intro i
    exact integerProjection_preservesProgression A x x0 m
      (fun j => by
        simpa only [sub_sub_sub_cancel_right] using
          dvd_sub (hx j) (hx0 j)) i
  funext i
  dsimp only [integralAffineMap, normalizedProjection]
  rw [mul_comm (m : ℤ), Int.ediv_mul_cancel (hdiv i)]
  ring

/-- Literal finite-projection and translated-equation data for an affine
threefold `V(J)` in ten-space.  `coefficientBound` and `fibreBound` are
uniform external bounds.  The only cardinality field is the local geometric
bounded-fibre condition `projection_fibre_card_le`; there is no global box,
progression, or target-count estimate in the model. -/
structure AffineFourHypersurfaceProjectionModel
    (J : Ideal (MvPolynomial (Fin 10) ℚ))
    (degreeBound coefficientBound fibreBound : ℕ) where
  degree : ℕ
  degree_at_least_four : 4 ≤ degree
  degree_le : degree ≤ degreeBound
  matrix : Matrix (Fin 4) (Fin 10) ℤ
  matrix_coefficient_bound :
    integerProjectionCoefficientBound matrix ≤ coefficientBound
  equation : (Fin 10 → ℤ) → ℕ → MvPolynomial (Fin 4) ℤ
  topPart : (Fin 10 → ℤ) → ℕ → MvPolynomial (Fin 4) ℚ
  equation_topPart : ∀ x0 : Fin 10 → ℤ,
    (fun i => (x0 i : ℚ)) ∈ affineIdealZeroLocus J →
    ∀ m : ℕ, 0 < m →
      IsTopHomogeneousPart (equation x0 m) (topPart x0 m) degree
  topPart_absolutelyIrreducible : ∀ x0 : Fin 10 → ℤ,
    (fun i => (x0 i : ℚ)) ∈ affineIdealZeroLocus J →
    ∀ m : ℕ, 0 < m → IsAbsolutelyIrreducible (topPart x0 m)
  normalizedProjection_zero : ∀ x0 x : Fin 10 → ℤ,
    (fun i => (x0 i : ℚ)) ∈ affineIdealZeroLocus J →
    (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus J →
    ∀ m : ℕ, 0 < m →
    (∀ i, (m : ℤ) ∣ x i - x0 i) →
      eval (normalizedProjection matrix x0 x m) (equation x0 m) = 0
  projection_fibre_card_le : ∀ (S : Finset (Fin 10 → ℤ)),
    (∀ x ∈ S, (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus J) →
    ∀ z : IntVector 4,
      (S.filter fun x => matrix.mulVec x = z).card ≤ fibreBound

/-- A uniform family of the preceding literal models for every good fibre
of one slicing certificate.  The three numerical bounds are chosen before
the fibre parameter. -/
structure GoodFibreAffineFourProjectionModels
    {r d : ℕ} (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I) where
  degreeBound : ℕ
  coefficientBound : ℕ
  fibreBound : ℕ
  coefficientBound_pos : 1 ≤ coefficientBound
  models : ∀ (y : Fin (r - 2) → ℚ),
    eval y slicing.discriminant ≠ 0 →
      AffineFourHypersurfaceProjectionModel
        (rationalSliceIdeal I slicing.matrix y)
        degreeBound coefficientBound fibreBound

/-- A normalized projected fibre is contained in one fibre of the original
linear projection, so it has the same uniform multiplicity bound. -/
theorem normalizedProjection_fibre_card_le
    {J : Ideal (MvPolynomial (Fin 10) ℚ)}
    {degreeBound coefficientBound fibreBound : ℕ}
    (model : AffineFourHypersurfaceProjectionModel J
      degreeBound coefficientBound fibreBound)
    (S : Finset (Fin 10 → ℤ))
    (hsource : ∀ x ∈ S,
      (fun i => (x i : ℚ)) ∈ affineIdealZeroLocus J)
    (x0 b : Fin 10 → ℤ) (hx0 : x0 ∈ S) (m : ℕ)
    (hres : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i - b i)
    (z : IntVector 4) :
    (S.filter fun x => normalizedProjection model.matrix x0 x m = z).card ≤
      fibreBound := by
  classical
  calc
    (S.filter fun x => normalizedProjection model.matrix x0 x m = z).card ≤
        (S.filter fun x => model.matrix.mulVec x =
          integralAffineMap (model.matrix.mulVec x0) z m).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hreconstruct := integralAffineMap_normalizedProjection
        model.matrix x x0 b m (hres x hx.1) (hres x0 hx0)
      rw [← hreconstruct, hx.2]
    _ ≤ fibreBound := model.projection_fibre_card_le S hsource _

/-- Salberger's four-coordinate theorem gives the desired exponent two for
one uniformly modelled good-fibre family.  The proof explicitly recentres
the source residue class, projects it, checks the closed box and equation,
and absorbs the auxiliary `epsilon/2` into the source-height factor. -/
theorem goodSurfaceFibreProgressionEstimate_of_affineFourModels
    (salberger : Salberger2023Theorem04)
    {r d : ℕ} {I : Ideal (MvPolynomial (Fin 10) ℚ)}
    (slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I)
    (family : GoodFibreAffineFourProjectionModels I slicing) :
    GoodSurfaceFibreProgressionEstimate I slicing := by
  intro epsilon hepsilon
  let epsilon' : ℝ := epsilon / 2
  have hepsilon' : 0 < epsilon' := by positivity
  obtain ⟨C0, hC0, hcount⟩ :=
    finiteSet_card_le_salberger2023_affineFour_boundedDegree
      (Point := Fin 10 → ℤ) salberger family.degreeBound family.fibreBound
        epsilon' hepsilon'
  let K : ℝ := family.coefficientBound
  let C : ℝ := max 1 (C0 * (2 * K) ^ ((2 : ℝ) + epsilon'))
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro y hy S u L hL m hm b hbox hres hsource
  let model := family.models y hy
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hK : 1 ≤ K := by
    dsimp only [K]
    exact_mod_cast family.coefficientBound_pos
  have hbase : 0 ≤ 1 + L / (m : ℝ) := by positivity
  have hbaseStrict : 0 < 1 + L / (m : ℝ) := by positivity
  have hheight : 1 + L / (m : ℝ) ≤ 2 + ‖u‖ + L + (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hdiv : L / (m : ℝ) ≤ L := div_le_self hL hm1
    linarith [norm_nonneg u]
  by_cases hS : S.Nonempty
  · obtain ⟨x0, hx0⟩ := hS
    have hres0 : ∀ x ∈ S, ∀ i, (m : ℤ) ∣ x i - x0 i := by
      intro x hx i
      convert dvd_sub (hres x hx i) (hres x0 hx0 i) using 1
      ring
    let Y : Finset (IntVector 4) := S.image model.matrix.mulVec
    have hy0 : model.matrix.mulVec x0 ∈ Y :=
      Finset.mem_image.mpr ⟨x0, hx0, rfl⟩
    have hYbox : ∀ z ∈ Y, ∀ i,
        |(z i : ℝ) - integerProjectionRealCenter model.matrix u i| ≤ K * L := by
      intro z hz i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hactual := integerProjection_transformedBox model.matrix x u L hL
        (hbox x hx) i
      have hmass : (integerProjectionCoefficientBound model.matrix : ℝ) ≤ K := by
        dsimp only [K]
        exact_mod_cast model.matrix_coefficient_bound
      exact hactual.trans (mul_le_mul_of_nonneg_right hmass hL)
    have hYres : ∀ z ∈ Y, ∀ i,
        (m : ℤ) ∣ z i - model.matrix.mulVec x0 i := by
      intro z hz i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact integerProjection_preservesProgression model.matrix x x0 m
        (hres0 x hx) i
    obtain ⟨_hreconstruct, _hinjective, hnormalizedBox⟩ :=
      HomogeneousProgressionBoxCount.displacement_bound
        Y (integerProjectionRealCenter model.matrix u) (K * L) m hm
          (model.matrix.mulVec x0) hy0 hYbox hYres
    let Bnat : ℕ := ⌈2 * (K * L) / (m : ℝ)⌉₊ + 1
    let projection : (Fin 10 → ℤ) → IntVector 4 :=
      fun x => normalizedProjection model.matrix x0 x m
    have hprojectionBox : ∀ x ∈ S, ∀ i,
        (projection x i).natAbs ≤ Bnat := by
      intro x hx i
      exact hnormalizedBox (model.matrix.mulVec x)
        (Finset.mem_image.mpr ⟨x, hx, rfl⟩) i
    have hB : (1 : ℝ) ≤ (Bnat : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Bnat)
    have himage : ∀ x ∈ S,
        projection x ∈ affineHypersurfaceIntegerPoints
          (model.equation x0 m) (Bnat : ℝ) := by
      intro x hx
      rw [affineHypersurfaceIntegerPoints, Finset.mem_filter]
      refine ⟨?_, ?_, model.normalizedProjection_zero x0 x
        (hsource x0 hx0) (hsource x hx) m hm (hres0 x hx)⟩
      · rw [mem_integerSupNormBox_iff]
        intro i
        simpa using hprojectionBox x hx i
      · intro i
        have hi := hprojectionBox x hx i
        have hiR : ((projection x i).natAbs : ℝ) ≤ (Bnat : ℝ) := by
          exact_mod_cast hi
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hiR
    have hfibre : ∀ z ∈ affineHypersurfaceIntegerPoints
        (model.equation x0 m) (Bnat : ℝ),
        (S.filter fun x => projection x = z).card ≤ family.fibreBound := by
      intro z _hz
      exact normalizedProjection_fibre_card_le model S hsource x0 b hx0 m hres z
    have hraw := hcount model.degree model.degree_at_least_four
      model.degree_le (model.equation x0 m) (model.topPart x0 m)
      (model.equation_topPart x0 (hsource x0 hx0) m hm)
      (model.topPart_absolutelyIrreducible x0 (hsource x0 hx0) m hm)
      (Bnat : ℝ) hB S projection himage hfibre
    have hBupper : (Bnat : ℝ) ≤ 2 * K * (1 + L / (m : ℝ)) := by
      have hceil := (Nat.ceil_lt_add_one
        (div_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * K) hL) hmR.le)).le
      dsimp only [Bnat]
      push_cast
      rw [show 2 * (K * L) / (m : ℝ) = 2 * K * L / (m : ℝ) by ring]
      calc
        (⌈2 * K * L / (m : ℝ)⌉₊ : ℝ) + 1 ≤
            (2 * K * L / (m : ℝ) + 1) + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hceil 1
        _ = 2 * K * (L / (m : ℝ)) + 2 := by ring
        _ ≤ 2 * K * (L / (m : ℝ)) + 2 * K := by linarith
        _ = 2 * K * (1 + L / (m : ℝ)) := by ring
    have hexponent : 0 ≤ (2 : ℝ) + epsilon' := by positivity
    have hbasepos : 0 ≤ 2 * K * (1 + L / (m : ℝ)) := by positivity
    calc
      (S.card : ℝ) ≤ C0 * (Bnat : ℝ) ^ ((2 : ℝ) + epsilon') := hraw
      _ ≤ C0 * (2 * K * (1 + L / (m : ℝ))) ^
          ((2 : ℝ) + epsilon') :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hBupper hexponent) hC0.le
      _ = (C0 * (2 * K) ^ ((2 : ℝ) + epsilon')) *
          ((1 + L / (m : ℝ)) ^ 2 *
            (1 + L / (m : ℝ)) ^ epsilon') := by
        rw [Real.mul_rpow (by positivity) hbase]
        rw [Real.rpow_add hbaseStrict 2 epsilon']
        norm_num [Real.rpow_natCast]
        ring
      _ ≤ C * ((1 + L / (m : ℝ)) ^ 2 *
            (1 + L / (m : ℝ)) ^ epsilon') := by
        gcongr
        exact le_max_right _ _
      _ ≤ C * ((1 + L / (m : ℝ)) ^ 2 *
            (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon') := by
        gcongr
      _ ≤ C * ((1 + L / (m : ℝ)) ^ 2 *
            (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon) := by
        have hheightOne : 1 ≤ 2 + ‖u‖ + L + (m : ℝ) := by
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith [norm_nonneg u]
        have hhalf :
            (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon' ≤
              (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon := by
          apply Real.rpow_le_rpow_of_exponent_le hheightOne
          dsimp only [epsilon']
          linarith
        gcongr
      _ = C * (2 + ‖u‖ + L + (m : ℝ)) ^ epsilon *
          (1 + L / (m : ℝ)) ^ 2 := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty,
      Nat.cast_zero]
    positivity

/-- Legacy over-universal model input.  This asks for models for every
slicing certificate whose degree parameter is at least four, even though the
certificate itself records only a fibre degree bounded above by that
parameter.  It is retained to document and support the older separated
adapter, but is deliberately not the premise of the canonical endpoint. -/
def UniversalAffineFourProjectionModelsN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    4 ≤ d →
    ∀ slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      Nonempty (GoodFibreAffineFourProjectionModels I slicing)

/-- The sound joint slicing-and-model boundary in the `n = 10` high rows.
The source is required to have actual projective dimension `r` and degree
`d ≥ 4`; the returned slicing certificate and its uniformly bounded
affine-four models are chosen together.  Consequently the model's
degree-at-least-four field belongs to the actual high-degree branch rather
than to an arbitrary certificate carrying only an upper degree bound. -/
def AffineFourProjectionModelsN10 : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 10) ℚ)) (r d : ℕ),
    (r = 4 ∨ r = 5) →
    I.IsPrime →
    GeometricallyPrimeMvPolynomialIdeal I →
    I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ) →
    HasProjectiveDimensionDegree I r d →
    4 ≤ d →
    ∃ slicing : RationalSurfaceSlicingCertificate (r := r) (d := d) I,
      Nonempty (GoodFibreAffineFourProjectionModels I slicing)

/-- The legacy universal model input and Salberger's published theorem imply
the broad separated good-fibre premise.  The canonical endpoint instead uses
`highTableSurfaceSlicing_of_affineFourModels`, whose joint input is restricted
to the actual high-degree component. -/
theorem goodSurfaceFibreProgressionEstimatesN10_of_universalAffineFourModels
    (salberger : Salberger2023Theorem04)
    (models : UniversalAffineFourProjectionModelsN10) :
    HighTableSurfaceSlicingSeparated.GoodSurfaceFibreProgressionEstimatesN10 := by
  intro I r d hr hd slicing
  obtain ⟨family⟩ := models I r d hr hd slicing
  exact goodSurfaceFibreProgressionEstimate_of_affineFourModels
    salberger slicing family

/-- The joint affine-four input supplies exactly the slicing datum required
for one genuine high-degree component. -/
theorem highComponentSurfaceSlicingData_of_affineFourModels
    (salberger : Salberger2023Theorem04)
    (models : AffineFourProjectionModelsN10)
    {r : ℕ} (hr : r = 4 ∨ r = 5)
    (I : Ideal (MvPolynomial (Fin 10) ℚ))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ)) :
    HighComponentSurfaceSlicingData r I := by
  intro d hprime hgeometric hdegree hd
  obtain ⟨slicing, ⟨family⟩⟩ :=
    models I r d hr hprime hgeometric hhom hdegree hd
  exact ⟨slicing,
    goodSurfaceFibreProgressionEstimate_of_affineFourModels
      salberger slicing family⟩

/-- Construct the actual high-row surface-slicing table from the joint
dimension-correct slicing/model input. -/
theorem highTableSurfaceSlicing_of_affineFourModels
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (planeWeil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (salberger : Salberger2023Theorem04)
    (models : AffineFourProjectionModelsN10) :
    MicrolocalRationalPartition.HighTableSurfaceSlicing := by
  intro t N F f hgeo hF hAn j hj hnext
  obtain ⟨T⟩ := MicrolocalPromotionTable.exists_table
    degreeSpan smooth spread planeWeil dichotomy hgeo hF hAn
      (by omega : 1 ≤ j.val ∧ j.val ≤ 4) hnext
  refine ⟨T, ?_⟩
  intro i
  apply highComponentSurfaceSlicingData_of_affineFourModels
    salberger models (I := baseIdeal (T.G i))
  · omega
  · exact T.homogeneous i

end CubicTenVariables.GoodSurfaceFibreAffineFourProjection
