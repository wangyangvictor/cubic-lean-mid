import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.RationalLinearProjectionBoxCount
import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# Counting after a marked finite birational linear projection

This file connects the standard algebraic-geometric projection statement
`IsMarkedFiniteBirationalLinearProjection` to literal affine lattice-point
counts.  It contains no application-specific counting estimate.

The first row of the chosen homogeneous projection is required to be the
distinguished source coordinate `X₀`.  On the chart `X₀ = 1`, the
remaining rows are therefore honest affine linear forms, with no
point-dependent projective rescaling.  The common matrix denominator makes
them integral.  The all-field fibre bound in the geometric projection then
controls each literal integral fibre.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The rational affine representative `(1,x)` in the consecutive `Fin`
coordinate convention. -/
def rationalFinStandardAffineRepresentative {n : ℕ}
    (x : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  Fin.cases 1 x

@[simp]
theorem rationalFinStandardAffineRepresentative_zero
    {n : ℕ} (x : Fin n → ℚ) :
    rationalFinStandardAffineRepresentative x 0 = 1 := rfl

@[simp]
theorem rationalFinStandardAffineRepresentative_succ
    {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    rationalFinStandardAffineRepresentative x i.succ = x i := rfl

theorem rationalFinStandardAffineRepresentative_eq_option
    {n : ℕ} (x : Fin n → ℚ) (j : Fin (n + 1)) :
    rationalFinStandardAffineRepresentative x j =
      rationalStandardAffineRepresentative x (finSuccEquiv n j) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j <;>
    simp [rationalFinStandardAffineRepresentative,
      rationalStandardAffineRepresentative]

/-- The complete homogeneous target tuple of a rational affine-chart
point. -/
def rationalFinProjectiveProjection {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : Fin n → ℚ) : Fin (d + 1) → ℚ :=
  fun i ↦ ∑ j, A i j * rationalFinStandardAffineRepresentative x j

theorem rationalFinProjectiveProjection_succ_eq_tail
    {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : Fin n → ℚ) (i : Fin d) :
    rationalFinProjectiveProjection A x i.succ =
      rationalFinProjectiveAffineTailProjection A x i := by
  unfold rationalFinProjectiveProjection
  unfold rationalFinProjectiveAffineTailProjection
  unfold rationalProjectiveAffineTailProjection
  unfold finProjectiveMatrixAsOption
  rw [← Equiv.sum_comp (finSuccEquiv n)]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [← rationalFinStandardAffineRepresentative_eq_option]

theorem rationalFinProjectiveProjection_zero_eq_one
    {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : Fin n → ℚ) :
    rationalFinProjectiveProjection A x 0 = 1 := by
  unfold rationalFinProjectiveProjection
  have hsum := Equiv.sum_comp (finSuccEquiv n)
    (fun j ↦ A 0 ((finSuccEquiv n).symm j) *
      rationalStandardAffineRepresentative x j)
  have hsum' :
      (∑ j, A 0 j * rationalFinStandardAffineRepresentative x j) =
        ∑ j, (finProjectiveMatrixAsOption A) 0 j *
          rationalStandardAffineRepresentative x j := by
    simpa [finProjectiveMatrixAsOption,
      rationalFinStandardAffineRepresentative_eq_option] using hsum
  rw [hsum']
  exact rationalFinProjectiveAffine_firstCoordinate_eq_one A hfirst x

/-- An affine tuple belongs to the standard chart of the projective source
ideal. -/
def IsRationalAffineChartPoint
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (x : Fin n → ℚ) : Prop :=
  I ≤ RingHom.ker
    (MvPolynomial.aeval
      (rationalFinStandardAffineRepresentative x)).toRingHom

/-- Evaluation of a projection row is the corresponding coordinate of the
displayed homogeneous target tuple. -/
theorem eval_projectiveMatrixLinearForm_affineChart
    {n d : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : Fin n → ℚ) (i : Fin (d + 1)) :
    MvPolynomial.eval (rationalFinStandardAffineRepresentative x)
        (StandardAG.projectiveMatrixLinearForm A i) =
      rationalFinProjectiveProjection A x i := by
  simp [StandardAG.projectiveMatrixLinearForm,
    rationalFinProjectiveProjection]

/-- A rational affine point of the source gives a rational point of its
coordinate ring. -/
def rationalAffineChartPointAlgHom
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (x : {x : Fin n → ℚ // IsRationalAffineChartPoint I x}) :
    (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
  affineQuotientRationalPoint I
    (rationalFinStandardAffineRepresentative x.1) x.2

theorem rationalAffineChartPointAlgHom_injective
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) :
    Function.Injective (rationalAffineChartPointAlgHom I) := by
  intro x x' h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h
    (Ideal.Quotient.mk I (MvPolynomial.X i.succ))
  simpa [rationalAffineChartPointAlgHom,
    affineQuotientRationalPoint_mk] using hi

/-- The quotient point attached to an affine source point lies in the
scheme-theoretic fibre over its displayed projected tuple. -/
theorem rationalAffineChartPointAlgHom_comp_projectiveMatrixCoordinateMap
    {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (A : Matrix (Fin (d + 1)) (Fin (n + 1)) ℚ)
    (x : {x : Fin n → ℚ // IsRationalAffineChartPoint I x}) :
    (rationalAffineChartPointAlgHom I x).comp
        (StandardAG.projectiveMatrixCoordinateMap I A) =
      MvPolynomial.aeval (rationalFinProjectiveProjection A x.1) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalAffineChartPointAlgHom,
    StandardAG.projectiveMatrixCoordinateMap,
    StandardAG.projectiveMatrixLinearForm,
    rationalFinProjectiveProjection]

/-- The defining homogeneous equation of the projected image vanishes on
the displayed projection of every rational affine source point. -/
theorem eval_projectionEquation_rationalFinProjectiveProjection_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (x : Fin N → ℚ) (hx : IsRationalAffineChartPoint I x) :
    MvPolynomial.eval (rationalFinProjectiveProjection A x) G = 0 := by
  letI : I.IsPrime := hI
  dsimp only [StandardAG.IsMarkedFiniteBirationalLinearProjection]
    at hprojection
  rcases hprojection with
    ⟨_hlinear, _hfinite, hkernel, _hhomogeneous, _hirreducible,
      _hdegreeOne, _hmarkedChart, _hmarkedFibre, _hallFibres⟩
  have hGkernel : G ∈ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom := by
    rw [hkernel]
    exact Ideal.subset_span (Set.mem_singleton G)
  have hGzero : StandardAG.projectiveMatrixCoordinateMap I A G = 0 :=
    RingHom.mem_ker.mp hGkernel
  have hcomp :=
    rationalAffineChartPointAlgHom_comp_projectiveMatrixCoordinateMap
      I A ⟨x, hx⟩
  have hvalue := DFunLike.congr_fun hcomp G
  simp only [AlgHom.comp_apply, hGzero, map_zero] at hvalue
  simpa using hvalue.symm

/-- The all-field scheme-theoretic fibre bound in a marked finite
birational projection specializes to the rational affine chart. -/
theorem rationalFinProjectiveAffineTail_fibres_of_markedProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A) :
    ∀ y : Fin (r + 1) → ℚ,
      Set.Finite {x : Fin N → ℚ |
        IsRationalAffineChartPoint I x ∧
          rationalFinProjectiveAffineTailProjection A x = y} ∧
      Set.ncard {x : Fin N → ℚ |
        IsRationalAffineChartPoint I x ∧
          rationalFinProjectiveAffineTailProjection A x = y} ≤ degree := by
  classical
  letI : I.IsPrime := hI
  dsimp only [StandardAG.IsMarkedFiniteBirationalLinearProjection]
    at hprojection
  rcases hprojection with
    ⟨_hlinear, _hfinite, _hkernel, _hhomogeneous, _hirreducible,
      _hdegreeOne, _hmarkedChart, _hmarkedFibre, hallFibres⟩
  intro y
  let fullTarget : Fin (r + 2) → ℚ := Fin.cases 1 y
  let targetPoint : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] ℚ :=
    MvPolynomial.aeval fullTarget
  let sourceFibre : Set
      ((MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ) :=
    {z | z.comp (StandardAG.projectiveMatrixCoordinateMap I A) = targetPoint}
  have hsource := hallFibres ℚ targetPoint
  have hsourceFinite : sourceFibre.Finite := hsource.1
  let affineFibre : Set (Fin N → ℚ) :=
    {x | IsRationalAffineChartPoint I x ∧
      rationalFinProjectiveAffineTailProjection A x = y}
  let markedPoint : (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
    affineQuotientRationalPoint I marked hmarked
  let embedPoint : (Fin N → ℚ) →
      ((MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ) :=
    fun x ↦ if hx : IsRationalAffineChartPoint I x then
      rationalAffineChartPointAlgHom I ⟨x, hx⟩ else markedPoint
  have hembed_of_mem (x : Fin N → ℚ) (hx : x ∈ affineFibre) :
      embedPoint x = rationalAffineChartPointAlgHom I ⟨x, hx.1⟩ := by
    simp [embedPoint, hx.1]
  have hembedInjective : Set.InjOn embedPoint affineFibre := by
    intro x hx x' hx' h
    rw [hembed_of_mem x hx, hembed_of_mem x' hx'] at h
    exact congrArg Subtype.val
      (rationalAffineChartPointAlgHom_injective I h)
  have hmaps : Set.MapsTo embedPoint affineFibre sourceFibre := by
    intro x hx
    rw [hembed_of_mem x hx]
    have hfull : rationalFinProjectiveProjection A x = fullTarget := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact rationalFinProjectiveProjection_zero_eq_one A hfirst x
      · simpa [fullTarget] using
          (rationalFinProjectiveProjection_succ_eq_tail A x j).trans
            (congrFun hx.2 j)
    change (rationalAffineChartPointAlgHom I ⟨x, hx.1⟩).comp
        (StandardAG.projectiveMatrixCoordinateMap I A) = targetPoint
    rw [rationalAffineChartPointAlgHom_comp_projectiveMatrixCoordinateMap]
    exact congrArg MvPolynomial.aeval hfull
  have haffineFinite : affineFibre.Finite := by
    exact Set.Finite.of_finite_image
      (hsourceFinite.subset (Set.image_subset_iff.mpr hmaps))
      hembedInjective
  constructor
  · simpa only [affineFibre] using haffineFinite
  · simpa only [affineFibre] using
      (Set.ncard_le_ncard_of_injOn embedPoint hmaps hembedInjective
        hsourceFinite).trans hsource.2

/-- Exact affine-chart box-count specialization of a marked finite
birational projection.  The numerical fibre factor is the geometric degree
appearing in `IsMarkedFiniteBirationalLinearProjection`; it is not an
additional counting assumption. -/
theorem card_le_integerBox_mul_degree_of_markedProjection
    {N r degree M : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (points : Finset (IntVector N))
    (hbox : ∀ x ∈ points, ∀ j, (x j).natAbs ≤ M)
    (hsource : ∀ x ∈ points,
      IsRationalAffineChartPoint I (intVectorToRat x)) :
    points.card ≤
      (2 * (rationalFinProjectiveAffineTailNumeratorConstant A * max 1 M) + 1) ^
          (r + 1) * degree := by
  have hfibres :=
    rationalFinProjectiveAffineTail_fibres_of_markedProjection
      I hI marked hmarked A G hprojection hfirst
  exact card_le_integerBox_mul_of_finProjectiveAffineTail_fibres
    A points (IsRationalAffineChartPoint I) hbox hsource
    (fun y ↦ (hfibres y).1) (fun y ↦ (hfibres y).2)

/-- Direct use of the permitted standard generic-projection theorem.  Its
literal conclusion supplies `A`, `G`, and the complete marked finite
birational projection data.  Once the chosen witness retains `X₀`, the
affine-chart count is the preceding theorem with no further geometric
fibre assumption.

The universal implication in the last line is intentional: the current
statement of `StandardAG.MarkedFiniteBirationalLinearProjection` does not
assert that its witness retains a prescribed source coordinate. -/
theorem exists_markedProjection_with_affineChart_count_of_standardAG
    (hStandard : StandardAG.MarkedFiniteBirationalLinearProjection)
    {N r degree : ℕ} (hrN : r < N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hGeometricallyPrime : GeometricallyPrimeMvPolynomialIdeal I)
    (hHomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hRelevant : ¬ Published.projectiveIrrelevantIdeal ℚ N ≤ I)
    (hDimensionDegree :
      Published.HasProjectiveDimensionDegree I r degree)
    (marked : Fin (N + 1) → ℚ) (hmarkedNonzero : marked ≠ 0)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (hmarkedSmooth : Algebra.FormallySmooth ℚ
      (AffineQuotientRationalPointLocalRing I marked hmarked)) :
    ∃ A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ,
    ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
      StandardAG.IsMarkedFiniteBirationalLinearProjection
          (d := degree) I hI marked hmarked A G ∧
      ∀ (_hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
        (M : ℕ) (points : Finset (IntVector N)),
        (∀ x ∈ points, ∀ j, (x j).natAbs ≤ M) →
        (∀ x ∈ points,
          IsRationalAffineChartPoint I (intVectorToRat x)) →
        points.card ≤
          (2 *
            (rationalFinProjectiveAffineTailNumeratorConstant A * max 1 M) +
              1) ^ (r + 1) * degree := by
  obtain ⟨A, G, hprojection⟩ :=
    hStandard N r degree hrN I hI hGeometricallyPrime hHomogeneous
      hRelevant hDimensionDegree marked hmarkedNonzero hmarked hmarkedSmooth
  refine ⟨A, G, hprojection, ?_⟩
  intro hfirst M points hbox hsource
  exact card_le_integerBox_mul_degree_of_markedProjection
    I hI marked hmarked A G hprojection hfirst points hbox hsource

/-! ## The literal integral affine equation of the image -/

/-- Substitute a fixed rational value for homogeneous coordinate zero and
retain the remaining consecutive coordinates. -/
def rationalSpecializeFirstCoordinate {d : ℕ} (c : ℚ) :
    MvPolynomial (Fin (d + 1)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin d) ℚ :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C c) MvPolynomial.X)

theorem eval_rationalSpecializeFirstCoordinate
    {d : ℕ} (c : ℚ) (y : Fin d → ℚ)
    (G : MvPolynomial (Fin (d + 1)) ℚ) :
    MvPolynomial.eval y (rationalSpecializeFirstCoordinate c G) =
      MvPolynomial.eval (Fin.cases c y) G := by
  let lhs : MvPolynomial (Fin (d + 1)) ℚ →+* ℚ :=
    (MvPolynomial.eval y).comp
      (rationalSpecializeFirstCoordinate c).toRingHom
  let rhs : MvPolynomial (Fin (d + 1)) ℚ →+* ℚ :=
    MvPolynomial.eval (Fin.cases c y)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs, rationalSpecializeFirstCoordinate]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [lhs, rhs, rationalSpecializeFirstCoordinate]
  exact RingHom.congr_fun hhom G

/-- Homogeneous substitution which multiplies the first coordinate by a
fixed scalar before passing to the standard affine chart. -/
def homogeneousFirstCoordinateRescaling {d : ℕ} (c : ℚ) :
    MvPolynomial (Fin (d + 1)) ℚ →ₐ[ℚ]
      MvPolynomial (Option (Fin d)) ℚ :=
  MvPolynomial.aeval
    (Fin.cases
      (MvPolynomial.C c * MvPolynomial.X none)
      (fun i ↦ MvPolynomial.X (some i)))

theorem homogeneousFirstCoordinateRescaling_isHomogeneous
    {d degree : ℕ} (c : ℚ)
    {G : MvPolynomial (Fin (d + 1)) ℚ}
    (hG : G.IsHomogeneous degree) :
    (homogeneousFirstCoordinateRescaling c G).IsHomogeneous degree := by
  change (MvPolynomial.aeval
    (Fin.cases
      (MvPolynomial.C c * MvPolynomial.X none)
      (fun i ↦ MvPolynomial.X (some i))) G).IsHomogeneous degree
  convert hG.aeval
    (Fin.cases
      (MvPolynomial.C c * MvPolynomial.X none)
      (fun i ↦ MvPolynomial.X (some i)))
    (fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact MvPolynomial.isHomogeneous_C_mul_X c none
      · exact MvPolynomial.isHomogeneous_X ℚ (some j)) using 1
  simp

theorem multivariateDehomogenization_homogeneousFirstCoordinateRescaling
    {d : ℕ} (c : ℚ)
    (G : MvPolynomial (Fin (d + 1)) ℚ) :
    multivariateDehomogenization
        (homogeneousFirstCoordinateRescaling c G) =
      rationalSpecializeFirstCoordinate c G := by
  let lhs : MvPolynomial (Fin (d + 1)) ℚ →ₐ[ℚ]
      MvPolynomial (Fin d) ℚ :=
    multivariateDehomogenization.comp
      (homogeneousFirstCoordinateRescaling c)
  have hhom : lhs = rationalSpecializeFirstCoordinate c := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [lhs, homogeneousFirstCoordinateRescaling,
        rationalSpecializeFirstCoordinate, multivariateDehomogenization]
  exact DFunLike.congr_fun hhom G

theorem rationalSpecializeFirstCoordinate_totalDegree_le
    {d degree : ℕ} (c : ℚ)
    {G : MvPolynomial (Fin (d + 1)) ℚ}
    (hG : G.IsHomogeneous degree) :
    (rationalSpecializeFirstCoordinate c G).totalDegree ≤ degree := by
  let g := homogeneousFirstCoordinateRescaling c G
  have hg : g.IsHomogeneous degree :=
    homogeneousFirstCoordinateRescaling_isHomogeneous c hG
  have hdegree :=
    (multivariateHomogenization_dehomogenization_of_isHomogeneous g hg).1
  simpa only [g,
    multivariateDehomogenization_homogeneousFirstCoordinateRescaling]
    using hdegree

/-- The affine equation obtained from the homogeneous image equation by
putting its first coordinate equal to the common denominator of the
projection matrix. -/
def rationalAffineProjectionEquation {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    MvPolynomial (Fin (r + 1)) ℚ :=
  rationalSpecializeFirstCoordinate
    ((finProjectiveMatrixAsOption A).den : ℚ) G

/-- Coefficientwise denominator clearing of the preceding rational affine
equation. -/
def integralAffineProjectionEquation {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    MvPolynomial (Fin (r + 1)) ℤ :=
  clearRationalMvPolynomial (rationalAffineProjectionEquation A G)

theorem integralAffineProjectionEquation_totalDegree_le
    {N r degree : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    {G : MvPolynomial (Fin (r + 2)) ℚ}
    (hG : G.IsHomogeneous degree) :
    (integralAffineProjectionEquation A G).totalDegree ≤ degree := by
  exact (totalDegree_clearRationalMvPolynomial_le
    (rationalAffineProjectionEquation A G)).trans
      (rationalSpecializeFirstCoordinate_totalDegree_le
        ((finProjectiveMatrixAsOption A).den : ℚ) hG)

/-- The literal rational top homogeneous part of the cleared integral image
equation. -/
def integralAffineProjectionTopPart {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) (degree : ℕ) :
    MvPolynomial (Fin (r + 1)) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)
    (MvPolynomial.homogeneousComponent degree
      (integralAffineProjectionEquation A G))

theorem integralAffineProjectionEquation_isTopHomogeneousPart
    {N r degree : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    {G : MvPolynomial (Fin (r + 2)) ℚ}
    (hG : G.IsHomogeneous degree)
    (htop : integralAffineProjectionTopPart A G degree ≠ 0) :
    Published.IsTopHomogeneousPart
      (integralAffineProjectionEquation A G)
      (integralAffineProjectionTopPart A G degree) degree := by
  refine ⟨rfl, htop, ?_⟩
  intro k hk
  apply MvPolynomial.homogeneousComponent_eq_zero
  exact lt_of_le_of_lt
    (integralAffineProjectionEquation_totalDegree_le A hG) hk

/-- Complete cleared homogeneous target coordinates.  Its zeroth
coordinate is the common denominator and its tail is the literal integral
numerator map. -/
def clearedFinProjectiveAffineTarget {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (x : IntVector N) : Fin (r + 2) → ℚ :=
  Fin.cases ((finProjectiveMatrixAsOption A).den : ℚ)
    (fun i ↦
      (integralNumeratorFinProjectiveAffineTailProjection A x i : ℚ))

theorem clearedFinProjectiveAffineTarget_eq_den_mul
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : IntVector N) :
    clearedFinProjectiveAffineTarget A x =
      fun i ↦ ((finProjectiveMatrixAsOption A).den : ℚ) *
        rationalFinProjectiveProjection A (intVectorToRat x) i := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [clearedFinProjectiveAffineTarget,
      rationalFinProjectiveProjection_zero_eq_one A hfirst]
  · have hclear :=
      integralNumeratorProjectiveAffineTailProjection_cast_eq_den_mul
        (finProjectiveMatrixAsOption A) x j
    simpa [clearedFinProjectiveAffineTarget,
      integralNumeratorFinProjectiveAffineTailProjection,
      rationalFinProjectiveAffineTailProjection,
      rationalFinProjectiveProjection_succ_eq_tail] using hclear

/-- The rational affine equation vanishes on the cleared integral image of
every integral affine-chart point of the source. -/
theorem eval_rationalAffineProjectionEquation_integralNumerator_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : IntVector N)
    (hx : IsRationalAffineChartPoint I (intVectorToRat x)) :
    MvPolynomial.eval
        (fun i ↦
          (integralNumeratorFinProjectiveAffineTailProjection A x i : ℚ))
        (rationalAffineProjectionEquation A G) = 0 := by
  letI : I.IsPrime := hI
  have hhomogeneous : G.IsHomogeneous degree := by
    dsimp only [StandardAG.IsMarkedFiniteBirationalLinearProjection]
      at hprojection
    exact hprojection.2.2.2.1
  have hsourceZero :=
    eval_projectionEquation_rationalFinProjectiveProjection_eq_zero
      I hI marked hmarked A G hprojection (intVectorToRat x) hx
  have hclearedZero :
      MvPolynomial.eval (clearedFinProjectiveAffineTarget A x) G = 0 := by
    rw [clearedFinProjectiveAffineTarget_eq_den_mul A hfirst x,
      eval_smul_of_isHomogeneous G
        (rationalFinProjectiveProjection A (intVectorToRat x))
        ((finProjectiveMatrixAsOption A).den : ℚ) degree hhomogeneous,
      hsourceZero, mul_zero]
  rw [rationalAffineProjectionEquation,
    eval_rationalSpecializeFirstCoordinate]
  exact hclearedZero

/-- Consequently the explicitly denominator-cleared integral equation
vanishes on every literal integral projected point. -/
theorem eval_integralAffineProjectionEquation_integralNumerator_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : IntVector N)
    (hx : IsRationalAffineChartPoint I (intVectorToRat x)) :
    MvPolynomial.eval
        (integralNumeratorFinProjectiveAffineTailProjection A x)
        (integralAffineProjectionEquation A G) = 0 := by
  have hcast : ((MvPolynomial.eval
        (integralNumeratorFinProjectiveAffineTailProjection A x)
        (integralAffineProjectionEquation A G) : ℤ) : ℚ) = 0 := by
    rw [integralAffineProjectionEquation,
      intCast_eval_clearRationalMvPolynomial]
    rw [eval_rationalAffineProjectionEquation_integralNumerator_eq_zero
      I hI marked hmarked A G hprojection hfirst x hx, mul_zero]
  exact_mod_cast hcast

/-- A positive integral radius containing the cleared affine image of the
source box. -/
def markedProjectionImageRadius {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ) (M : ℕ) : ℕ :=
  max 1
    (rationalFinProjectiveAffineTailNumeratorConstant A * max 1 M)

theorem one_le_markedProjectionImageRadius
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ) (M : ℕ) :
    1 ≤ markedProjectionImageRadius A M :=
  Nat.le_max_left _ _

/-- Literal image containment in the integral hypersurface point set used
by Salberger's affine theorem. -/
theorem integralNumeratorProjection_mem_affineHypersurfaceIntegerPoints
    {N r degree M : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (x : IntVector N) (hbox : ∀ j, (x j).natAbs ≤ M)
    (hx : IsRationalAffineChartPoint I (intVectorToRat x)) :
    integralNumeratorFinProjectiveAffineTailProjection A x ∈
      Published.affineHypersurfaceIntegerPoints
        (integralAffineProjectionEquation A G)
        (markedProjectionImageRadius A M : ℝ) := by
  rw [Published.affineHypersurfaceIntegerPoints]
  apply Finset.mem_filter.mpr
  have hcoordinate : ∀ i,
      (integralNumeratorFinProjectiveAffineTailProjection A x i).natAbs ≤
        markedProjectionImageRadius A M := by
    intro i
    exact (integralNumeratorProjectiveAffineTailProjection_coordinate_natAbs_le
      (finProjectiveMatrixAsOption A) x hbox i).trans
        (Nat.le_max_right 1
          (rationalFinProjectiveAffineTailNumeratorConstant A * max 1 M))
  refine ⟨?_, ?_,
    eval_integralAffineProjectionEquation_integralNumerator_eq_zero
      I hI marked hmarked A G hprojection hfirst x hx⟩
  · rw [mem_integerSupNormBox_iff]
    simpa using hcoordinate
  · intro i
    simpa [Nat.cast_natAbs] using
      (show ((integralNumeratorFinProjectiveAffineTailProjection A x i).natAbs : ℝ) ≤
          (markedProjectionImageRadius A M : ℝ) by
        exact_mod_cast hcoordinate i)

/-- Literal integral fibres inherit the degree bound in the standard
geometric projection statement. -/
theorem integralNumeratorProjection_fibre_card_le_degree_of_markedProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (points : Finset (IntVector N))
    (hsource : ∀ x ∈ points,
      IsRationalAffineChartPoint I (intVectorToRat x))
    (z : IntVector (r + 1)) :
    (points.filter fun x ↦
      integralNumeratorFinProjectiveAffineTailProjection A x = z).card ≤
        degree := by
  have hfibres :=
    rationalFinProjectiveAffineTail_fibres_of_markedProjection
      I hI marked hmarked A G hprojection hfirst
  simpa only [integralNumeratorFinProjectiveAffineTailProjection,
      rationalFinProjectiveAffineTailProjection] using
    integralNumeratorProjectiveAffineTail_fibre_card_le_geometric
      (finProjectiveMatrixAsOption A) points
      (IsRationalAffineChartPoint I) hsource
      (fun y ↦ (hfibres y).1) (fun y ↦ (hfibres y).2) z

/-- Direct application of Salberger 2023, Theorem 0.4, after a marked
finite birational projection retaining `X₀` has been supplied.  The only
additional geometric hypothesis is precisely the one required by the
published affine theorem: the top homogeneous part of the explicitly
cleared equation must be absolutely irreducible. -/
theorem finiteIntegralAffineChartPointSet_card_le_salberger2023_of_markedProjection
    (hSalberger : Published.Salberger2023Theorem04)
    {N r degree M : ℕ}
    (hTargetDimension : 3 ≤ r + 1)
    (hDegreeRange : degree = 3 ∨ 4 ≤ degree)
    (ε : ℝ) (hε : 0 < ε)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (topPart : MvPolynomial (Fin (r + 1)) ℚ)
    (hTopPart : Published.IsTopHomogeneousPart
      (integralAffineProjectionEquation A G) topPart degree)
    (hTopIrreducible : Published.IsAbsolutelyIrreducible topPart) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (points : Finset (IntVector N)),
        (∀ x ∈ points, ∀ j, (x j).natAbs ≤ M) →
        (∀ x ∈ points,
          IsRationalAffineChartPoint I (intVectorToRat x)) →
        (points.card : ℝ) ≤
          C * (markedProjectionImageRadius A M : ℝ) ^
            Published.salberger2023AffineExponent (r + 1) degree ε := by
  obtain ⟨C, hC, hbound⟩ :=
    finiteSet_card_le_salberger2023_affineHypersurface
      (Point := IntVector N) hSalberger
      (r + 1) degree degree hTargetDimension hDegreeRange ε hε
  refine ⟨C, hC, ?_⟩
  intro points hbox hsource
  apply hbound (integralAffineProjectionEquation A G) topPart
    hTopPart hTopIrreducible (markedProjectionImageRadius A M : ℝ)
    (by exact_mod_cast one_le_markedProjectionImageRadius A M)
    points (integralNumeratorFinProjectiveAffineTailProjection A)
  · intro x hx
    exact integralNumeratorProjection_mem_affineHypersurfaceIntegerPoints
      I hI marked hmarked A G hprojection hfirst x (hbox x hx)
        (hsource x hx)
  · intro z _hz
    exact
      integralNumeratorProjection_fibre_card_le_degree_of_markedProjection
        I hI marked hmarked A G hprojection hfirst points hsource z

/-- Streamlined form of the preceding theorem.  Homogeneity of `G` comes
from the marked projection, and the routine top-degree bookkeeping for
coefficient clearing is discharged internally.  Thus the sole additional
condition on the affine image equation is irreducibility of its literal top
homogeneous part. -/
theorem finiteIntegralAffineChartPointSet_card_le_salberger2023_of_markedProjection'
    (hSalberger : Published.Salberger2023Theorem04)
    {N r degree M : ℕ}
    (hTargetDimension : 3 ≤ r + 1)
    (hDegreeRange : degree = 3 ∨ 4 ≤ degree)
    (ε : ℝ) (hε : 0 < ε)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (marked : Fin (N + 1) → ℚ)
    (hmarked : I ≤ RingHom.ker (MvPolynomial.aeval marked).toRingHom)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsMarkedFiniteBirationalLinearProjection
      (d := degree) I hI marked hmarked A G)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate A)
    (hTopIrreducible :
      Published.IsAbsolutelyIrreducible (integralAffineProjectionTopPart A G degree)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (points : Finset (IntVector N)),
        (∀ x ∈ points, ∀ j, (x j).natAbs ≤ M) →
        (∀ x ∈ points,
          IsRationalAffineChartPoint I (intVectorToRat x)) →
        (points.card : ℝ) ≤
          C * (markedProjectionImageRadius A M : ℝ) ^
            Published.salberger2023AffineExponent (r + 1) degree ε := by
  have hGhomogeneous : G.IsHomogeneous degree := by
    dsimp only [StandardAG.IsMarkedFiniteBirationalLinearProjection]
      at hprojection
    exact hprojection.2.2.2.1
  exact
    finiteIntegralAffineChartPointSet_card_le_salberger2023_of_markedProjection
      hSalberger hTargetDimension hDegreeRange ε hε I hI marked hmarked
      A G hprojection hfirst (integralAffineProjectionTopPart A G degree)
      (integralAffineProjectionEquation_isTopHomogeneousPart
        A hGhomogeneous hTopIrreducible.ne_zero)
      hTopIrreducible

end

end TranslatedDepthSeven
