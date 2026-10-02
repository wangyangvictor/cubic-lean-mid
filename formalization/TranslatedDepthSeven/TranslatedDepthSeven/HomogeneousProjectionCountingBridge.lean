import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.RationalLinearProjectionBoxCount
import TranslatedDepthSeven.IntegralHomogeneousIdealModel
import TranslatedDepthSeven.AffineTransformBounds
import TranslatedDepthSeven.PublishedCountingApplications
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount
import TranslatedDepthSeven.GeometricProjectionIrreducibility

/-!
# Counting after a homogeneous projection of an affine cone

The proper-fourfold argument in the manuscript projects the homogeneous
affine cone in `A^(N+1)` directly to `A^(r+2)`.  It does not first pass to
the affine chart `X_0 = 1`.  Consequently no projected coordinate has to be
the distinguished homogenizing coordinate.

This file records that literal route.  The only external geometric input is
the standard generic-projection assertion that a geometrically integral
projective variety admits a finite birational homogeneous linear projection
to a hypersurface, with the usual degree bound on every geometric fibre.
After clearing the projection matrix denominator, the normalized point
`z` is sent by the integral linear map `A.num * z`.  The image equation is
the actual affine translate of the cleared homogeneous image equation.
Its top homogeneous part is proved below to be a nonzero scalar multiple of
the original image equation. Geometric primality of the source proves that
this equation is absolutely irreducible, as required by the corrected
hypothesis of Salberger 2023, Theorem 0.4.

There is no proper-piece, star, or lattice-point estimate in the standard
algebraic-geometric input below.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace StandardAG

/-- Data of a finite birational homogeneous linear projection of an
integral projective variety to a hypersurface.  The final clause is the
scheme-theoretic geometric fibre bound supplied by projective Bezout. -/
def IsHomogeneousFiniteBirationalLinearProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ) : Prop := by
  letI : I.IsPrime := hI
  let source := MvPolynomial (Fin (N + 1)) ℚ ⧸ I
  let h := projectiveMatrixCoordinateMap I A
  let imageIdeal := RingHom.ker h.toRingHom
  letI : imageIdeal.IsPrime := RingHom.ker_isPrime h
  let image := MvPolynomial (Fin (r + 2)) ℚ ⧸ imageIdeal
  let imageToSource : image →ₐ[ℚ] source := Ideal.kerLiftAlg h
  letI : Algebra image source := imageToSource.toRingHom.toAlgebra
  letI : NoZeroSMulDivisors image source :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr
      (Ideal.kerLiftAlg_injective h)
  letI : Algebra (FractionRing image) (FractionRing source) :=
    FractionRing.liftAlgebra image (FractionRing source)
  exact
    (∀ i, (projectiveMatrixLinearForm A i).IsHomogeneous 1) ∧
    h.Finite ∧
    imageIdeal = Ideal.span {G} ∧
    G.IsHomogeneous degree ∧
    Irreducible G ∧
    Module.finrank (FractionRing image) (FractionRing source) = 1 ∧
    ∀ (L : Type) [Field L] [Algebra ℚ L]
      (y : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] L),
      Set.Finite {z : source →ₐ[ℚ] L | z.comp h = y} ∧
        Set.ncard {z : source →ₐ[ℚ] L | z.comp h = y} ≤ degree

/-- Standard generic linear projection, stated only at the algebraic level
needed for a homogeneous affine cone.  This is the unmarked counterpart of
`MarkedFiniteBirationalLinearProjection`: no selected rational point and no
preferred target coordinate occurs.

References: Stacks Project, Section 43.23 (Tag `0B1N`), together with the
projective Bezout fibre bound. -/
def HomogeneousFiniteBirationalLinearProjection : Prop :=
  ∀ (N r degree : ℕ), r < N →
    ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (hI : I.IsPrime),
      GeometricallyPrimeMvPolynomialIdeal I →
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      ¬ (Published.projectiveIrrelevantIdeal ℚ N ≤ I) →
      Published.HasProjectiveDimensionDegree I r degree →
        ∃ A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ,
        ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
          IsHomogeneousFiniteBirationalLinearProjection
            (degree := degree) I hI A G

/-- Uniform bounded-degree form of generic homogeneous projection.  It says
that one finite list of rational matrices works for every geometrically
integral projective `r`-fold of degree at most `degreeBound` in the fixed
ambient projective space.  This is the precise finite-grid consequence of
the bounded-degree incidence calculation in Browning--Heath-Brown--Salberger,
*Counting rational points on algebraic varieties*, Duke Math. J. 132 (2006),
Section 3, Lemma 6 and the ensuing projection construction (using Lemma 3).
Its proof uses standard Chow parameter spaces, upper semicontinuity and
Bezout.  Stacks Tag `0B1N` alone supplies generic projection, not this
uniform finite-list conclusion.  This remains an explicit geometric input;
it contains no lattice-point or application-specific counting conclusion.
See `BOUNDED_PROJECTION_REFERENCE.md` for its precise status. -/
def BoundedDegreeHomogeneousProjectionMenu : Prop :=
  ∀ (N r degreeBound : ℕ), r < N →
    ∃ menu : Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ),
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hI : I.IsPrime),
        GeometricallyPrimeMvPolynomialIdeal I →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        ¬ (Published.projectiveIrrelevantIdeal ℚ N ≤ I) →
        ∀ degree : ℕ,
          Published.HasProjectiveDimensionDegree I r degree →
          degree ≤ degreeBound →
            ∃ A ∈ menu, ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
              IsHomogeneousFiniteBirationalLinearProjection
                (degree := degree) I hI A G

end StandardAG

/-- A rational vector is a point of the affine cone cut out by `I`. -/
def IsRationalConePoint {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ)) (x : Fin N → ℚ) : Prop :=
  I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom

/-- The quotient-ring point represented by a rational point of the cone. -/
def rationalConePointAlgHom {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (x : {x : Fin N → ℚ // IsRationalConePoint I x}) :
    (MvPolynomial (Fin N) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
  affineQuotientRationalPoint I x.1 x.2

theorem rationalConePointAlgHom_injective {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ)) :
    Function.Injective (rationalConePointAlgHom I) := by
  intro x x' h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h
    (Ideal.Quotient.mk I (MvPolynomial.X i))
  simpa [rationalConePointAlgHom,
    affineQuotientRationalPoint_mk] using hi

/-- A cone point lies over its literal homogeneous linear projection. -/
theorem rationalConePointAlgHom_comp_projectiveMatrixCoordinateMap
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin d) (Fin N) ℚ)
    (x : {x : Fin N → ℚ // IsRationalConePoint I x}) :
    (rationalConePointAlgHom I x).comp
        (StandardAG.projectiveMatrixCoordinateMap I A) =
      MvPolynomial.aeval (rationalLinearProjection A x.1) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalConePointAlgHom,
    StandardAG.projectiveMatrixCoordinateMap,
    StandardAG.projectiveMatrixLinearForm,
    rationalLinearProjection]

/-- The projected hypersurface equation vanishes on every rational cone
point. -/
theorem eval_homogeneousProjectionEquation_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (x : Fin (N + 1) → ℚ) (hx : IsRationalConePoint I x) :
    MvPolynomial.eval (rationalLinearProjection A x) G = 0 := by
  letI : I.IsPrime := hI
  dsimp only [StandardAG.IsHomogeneousFiniteBirationalLinearProjection]
    at hprojection
  rcases hprojection with
    ⟨_hlinear, _hfinite, hkernel, _hhomogeneous, _hirreducible,
      _hdegreeOne, _hallFibres⟩
  have hGkernel : G ∈ RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I A).toRingHom := by
    rw [hkernel]
    exact Ideal.subset_span (Set.mem_singleton G)
  have hGzero : StandardAG.projectiveMatrixCoordinateMap I A G = 0 :=
    RingHom.mem_ker.mp hGkernel
  have hcomp :=
    rationalConePointAlgHom_comp_projectiveMatrixCoordinateMap
      I A ⟨x, hx⟩
  have hvalue := DFunLike.congr_fun hcomp G
  simp only [AlgHom.comp_apply, hGzero, map_zero] at hvalue
  simpa using hvalue.symm

/-- The geometric fibre bound in the homogeneous projection controls every
literal rational fibre of the affine cone. -/
theorem rationalConeProjection_fibres_of_homogeneousProjection
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G) :
    ∀ y : Fin (r + 2) → ℚ,
      Set.Finite {x : Fin (N + 1) → ℚ |
        IsRationalConePoint I x ∧ rationalLinearProjection A x = y} ∧
      Set.ncard {x : Fin (N + 1) → ℚ |
        IsRationalConePoint I x ∧ rationalLinearProjection A x = y} ≤
          degree := by
  classical
  letI : I.IsPrime := hI
  dsimp only [StandardAG.IsHomogeneousFiniteBirationalLinearProjection]
    at hprojection
  rcases hprojection with
    ⟨_hlinear, _hfinite, _hkernel, _hhomogeneous, _hirreducible,
      _hdegreeOne, hallFibres⟩
  intro y
  let targetPoint : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] ℚ :=
    MvPolynomial.aeval y
  let sourceFibre : Set
      ((MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ) :=
    {z | z.comp (StandardAG.projectiveMatrixCoordinateMap I A) = targetPoint}
  have hsource := hallFibres ℚ targetPoint
  have hsourceFinite : sourceFibre.Finite := hsource.1
  let coneFibre : Set (Fin (N + 1) → ℚ) :=
    {x | IsRationalConePoint I x ∧ rationalLinearProjection A x = y}
  by_cases hempty : coneFibre.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hempty
    let defaultPoint : (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
      rationalConePointAlgHom I ⟨x₀, hx₀.1⟩
    let embedPoint : (Fin (N + 1) → ℚ) →
        ((MvPolynomial (Fin (N + 1)) ℚ ⧸ I) →ₐ[ℚ] ℚ) :=
      fun x ↦ if hx : IsRationalConePoint I x then
        rationalConePointAlgHom I ⟨x, hx⟩ else defaultPoint
    have hembed_of_mem (x : Fin (N + 1) → ℚ) (hx : x ∈ coneFibre) :
        embedPoint x = rationalConePointAlgHom I ⟨x, hx.1⟩ := by
      simp [embedPoint, hx.1]
    have hembedInjective : Set.InjOn embedPoint coneFibre := by
      intro x hx x' hx' h
      rw [hembed_of_mem x hx, hembed_of_mem x' hx'] at h
      exact congrArg Subtype.val
        (rationalConePointAlgHom_injective I h)
    have hmaps : Set.MapsTo embedPoint coneFibre sourceFibre := by
      intro x hx
      rw [hembed_of_mem x hx]
      change (rationalConePointAlgHom I ⟨x, hx.1⟩).comp
          (StandardAG.projectiveMatrixCoordinateMap I A) = targetPoint
      rw [rationalConePointAlgHom_comp_projectiveMatrixCoordinateMap]
      exact congrArg MvPolynomial.aeval hx.2
    have hfinite : coneFibre.Finite := by
      exact Set.Finite.of_finite_image
        (hsourceFinite.subset (Set.image_subset_iff.mpr hmaps))
        hembedInjective
    constructor
    · simpa only [coneFibre] using hfinite
    · simpa only [coneFibre] using
        (Set.ncard_le_ncard_of_injOn embedPoint hmaps hembedInjective
          hsourceFinite).trans hsource.2
  · have hempty' : coneFibre = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    constructor
    · simpa only [coneFibre, hempty'] using (Set.finite_empty : (∅ : Set (Fin (N + 1) → ℚ)).Finite)
    · simp only [coneFibre, hempty', Set.ncard_empty]
      exact Nat.zero_le _

/-! ## The translated image equation and its leading form -/

/-- The integral homogeneous equation obtained by clearing the rational
image equation. -/
def integralHomogeneousProjectionEquation {r : ℕ}
    (G : MvPolynomial (Fin (r + 2)) ℚ) :
    MvPolynomial (Fin (r + 2)) ℤ :=
  clearRationalMvPolynomial G

/-- The actual integral equation of the projected normalized displacement:
the translation is the cleared projection of `x₀`, and the scale is `m`. -/
def integralTranslatedHomogeneousProjectionEquation
    {N r : ℕ}
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (x₀ : IntVector (N + 1)) (m : ℕ) :
    MvPolynomial (Fin (r + 2)) ℤ :=
  integralAffineTransform (integralNumeratorLinearProjection A x₀) m
    (integralHomogeneousProjectionEquation G)

/-- The literal rational top homogeneous part of the translated cleared
image equation.  It is the original homogeneous image equation multiplied
by the nonzero scalar introduced by denominator clearing and dilation. -/
def rationalTranslatedHomogeneousProjectionTopPart {r : ℕ}
    (G : MvPolynomial (Fin (r + 2)) ℚ) (m degree : ℕ) :
    MvPolynomial (Fin (r + 2)) ℚ :=
  MvPolynomial.C
      ((mvPolynomialRationalCommonDenominator G : ℚ) * (m : ℚ) ^ degree) *
    G

/-- The degree-`d` homogeneous part of an affine transform of a homogeneous
polynomial is the original polynomial multiplied by `m^d`. -/
theorem homogeneousComponent_integralAffineTransform_of_isHomogeneous
    {n d : ℕ} (x₀ : IntVector n) (m : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (hf : f.IsHomogeneous d)
    (hne : f ≠ 0) :
    MvPolynomial.homogeneousComponent d
        (integralAffineTransform x₀ m f) =
      f * MvPolynomial.C ((m : ℤ) ^ d) := by
  classical
  rw [integralAffineTransform_eq_sum_starCoefficient]
  rw [map_sum]
  rw [Finset.sum_eq_single d]
  · have hcoeff : starCoefficient f x₀ d = f :=
      starCoefficient_eq_of_isHomogeneous f x₀ d hf
    have hstar : (starCoefficient f x₀ d).IsHomogeneous d := by
      rw [hcoeff]
      exact hf
    have hterm :
        (starCoefficient f x₀ d * MvPolynomial.C ((m : ℤ) ^ d)).IsHomogeneous d :=
      by simpa [mul_comm] using
        (MvPolynomial.isHomogeneous_C (Fin n) ((m : ℤ) ^ d)).mul hstar
    rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hterm,
      if_pos rfl, hcoeff]
  · intro k hk hkd
    have hkstar : (starCoefficient f x₀ k).IsHomogeneous k :=
      starCoefficient_isHomogeneous f x₀ k
    have hterm :
        (starCoefficient f x₀ k * MvPolynomial.C ((m : ℤ) ^ k)).IsHomogeneous k :=
      by simpa [mul_comm] using
        (MvPolynomial.isHomogeneous_C (Fin n) ((m : ℤ) ^ k)).mul hkstar
    rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hterm]
    simp [Ne.symm hkd]
  · intro hdnot
    have hcoeff : starCoefficient f x₀ d = f :=
      starCoefficient_eq_of_isHomogeneous f x₀ d hf
    have hmem : d ∈ (symbolicLinePolynomial f x₀).support := by
      rw [Polynomial.mem_support_iff]
      change starCoefficient f x₀ d ≠ 0
      rw [hcoeff]
      exact hne
    exact (hdnot hmem).elim

/-- For a positive dilation, the displayed polynomial has exactly the
top part claimed above. Geometric primality of the source proves absolute
irreducibility of that top part through the injective image quotient. -/
theorem integralTranslatedHomogeneousProjectionEquation_topPart
    {N r degree m : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hIgeometric : GeometricallyPrimeMvPolynomialIdeal I)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (x₀ : IntVector (N + 1)) (hm : 0 < m) :
    Published.IsTopHomogeneousPart
        (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
        (rationalTranslatedHomogeneousProjectionTopPart G m degree)
        degree ∧
      Published.IsAbsolutelyIrreducible
        (rationalTranslatedHomogeneousProjectionTopPart G m degree) := by
  have hGhomogeneous : G.IsHomogeneous degree := by
    dsimp only [StandardAG.IsHomogeneousFiniteBirationalLinearProjection]
      at hprojection
    exact hprojection.2.2.2.1
  have hGirreducible : Irreducible G := by
    dsimp only [StandardAG.IsHomogeneousFiniteBirationalLinearProjection]
      at hprojection
    exact hprojection.2.2.2.2.1
  have hGne : G ≠ 0 := hGirreducible.ne_zero
  have hGabsolute : Published.IsAbsolutelyIrreducible G := by
    apply absolutelyIrreducible_of_ker_eq_span_of_geometricallyPrime
      I hIgeometric (StandardAG.projectiveMatrixCoordinateMap I A) G hGne
    exact hprojection.2.2.1
  have hclearHomogeneous :
      (integralHomogeneousProjectionEquation G).IsHomogeneous degree :=
    clearRationalMvPolynomial_isHomogeneous hGhomogeneous
  have hclearNe : integralHomogeneousProjectionEquation G ≠ 0 :=
    clearRationalMvPolynomial_ne_zero hGne
  have hden :
      (mvPolynomialRationalCommonDenominator G : ℚ) ≠ 0 := by
    exact_mod_cast (mvPolynomialRationalCommonDenominator_pos G).ne'
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hscalar :
      (mvPolynomialRationalCommonDenominator G : ℚ) *
          (m : ℚ) ^ degree ≠ 0 :=
    mul_ne_zero hden (pow_ne_zero degree hmQ)
  have htopIrreducible : Published.IsAbsolutelyIrreducible
      (rationalTranslatedHomogeneousProjectionTopPart G m degree) := by
    exact hGabsolute.const_mul _ hscalar
  refine ⟨⟨?_, htopIrreducible.ne_zero, ?_⟩, htopIrreducible⟩
  · rw [integralTranslatedHomogeneousProjectionEquation,
      homogeneousComponent_integralAffineTransform_of_isHomogeneous
        (integralNumeratorLinearProjection A x₀) m
        (integralHomogeneousProjectionEquation G)
        hclearHomogeneous hclearNe]
    simp only [rationalTranslatedHomogeneousProjectionTopPart,
      integralHomogeneousProjectionEquation, map_mul,
      map_clearRationalMvPolynomial, map_pow, map_natCast]
    ring
  · intro k hk
    apply MvPolynomial.homogeneousComponent_eq_zero
    rw [integralTranslatedHomogeneousProjectionEquation,
      totalDegree_integralAffineTransform hm,
      hclearHomogeneous.totalDegree hclearNe]
    exact_mod_cast hk

/-- Clearing the projection denominator commutes with the normalized affine
map `x = x₀ + m z`. -/
theorem integralNumeratorLinearProjection_integralAffineMap
    {N d m : ℕ} (A : Matrix (Fin d) (Fin N) ℚ)
    (x₀ z : IntVector N) :
    integralNumeratorLinearProjection A (integralAffineMap x₀ z m) =
      integralAffineMap (integralNumeratorLinearProjection A x₀)
        (integralNumeratorLinearProjection A z) m := by
  funext i
  simp only [integralNumeratorLinearProjection, integralAffineMap,
    Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Rational linear projection commutes with the same affine map. -/
theorem rationalLinearProjection_integralAffineMap
    {N d m : ℕ} (A : Matrix (Fin d) (Fin N) ℚ)
    (x₀ z : IntVector N) :
    rationalLinearProjection A
        (intVectorToRat (integralAffineMap x₀ z m)) =
      fun i ↦ rationalLinearProjection A (intVectorToRat x₀) i +
        (m : ℚ) * rationalLinearProjection A (intVectorToRat z) i := by
  funext i
  simp only [rationalLinearProjection, intVectorToRat, integralAffineMap,
    Int.cast_add, Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Int.cast_mul, Int.cast_natCast]
  ring

/-- The cleared image equation vanishes at the cleared projection of every
rational point of the source cone. -/
theorem eval_integralHomogeneousProjectionEquation_eq_zero
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (x : IntVector (N + 1))
    (hx : IsRationalConePoint I (intVectorToRat x)) :
    MvPolynomial.eval (integralNumeratorLinearProjection A x)
        (integralHomogeneousProjectionEquation G) = 0 := by
  have hGhomogeneous : G.IsHomogeneous degree := by
    dsimp only [StandardAG.IsHomogeneousFiniteBirationalLinearProjection]
      at hprojection
    exact hprojection.2.2.2.1
  have hzero := eval_homogeneousProjectionEquation_eq_zero
    I hI A G hprojection (intVectorToRat x) hx
  have hscaled :
      MvPolynomial.eval
          (fun i ↦
            ((integralNumeratorLinearProjection A x i : ℤ) : ℚ)) G = 0 := by
    have hcoords :
        (fun i ↦ ((integralNumeratorLinearProjection A x i : ℤ) : ℚ)) =
          fun i ↦ (A.den : ℚ) *
            rationalLinearProjection A (intVectorToRat x) i := by
      funext i
      exact integralNumeratorLinearProjection_cast_eq_den_mul A x i
    rw [hcoords]
    rw [eval_smul_of_isHomogeneous G
      (rationalLinearProjection A (intVectorToRat x)) (A.den : ℚ)
      degree hGhomogeneous]
    rw [hzero, mul_zero]
  have hcast := intCast_eval_clearRationalMvPolynomial G
    (integralNumeratorLinearProjection A x)
  rw [hscaled, mul_zero] at hcast
  exact_mod_cast hcast

/-- Therefore the translated image equation vanishes at the integral
projection of every normalized displacement whose affine image lies on the
source cone. -/
theorem eval_integralTranslatedHomogeneousProjectionEquation_eq_zero
    {N r degree m : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (x₀ z : IntVector (N + 1))
    (hz : IsRationalConePoint I
      (intVectorToRat (integralAffineMap x₀ z m))) :
    MvPolynomial.eval (integralNumeratorLinearProjection A z)
      (integralTranslatedHomogeneousProjectionEquation A G x₀ m) = 0 := by
  rw [integralTranslatedHomogeneousProjectionEquation,
    eval_integralAffineTransform,
    ← integralNumeratorLinearProjection_integralAffineMap]
  exact eval_integralHomogeneousProjectionEquation_eq_zero
    I hI A G hprojection (integralAffineMap x₀ z m) hz

/-- The natural integral radius of the projected normalized box. -/
def homogeneousProjectionImageRadius {N d : ℕ}
    (A : Matrix (Fin d) (Fin N) ℚ) (M : ℕ) : ℕ :=
  max 1 (rationalLinearProjectionNumeratorConstant A * M)

/-- Maximum cleared row mass of a fixed finite projection menu. -/
def homogeneousProjectionMenuNumeratorConstant {N d : ℕ}
    (menu : Finset (Matrix (Fin d) (Fin N) ℚ)) : ℕ :=
  menu.sup rationalLinearProjectionNumeratorConstant

theorem rationalLinearProjectionNumeratorConstant_le_menuConstant
    {N d : ℕ}
    (menu : Finset (Matrix (Fin d) (Fin N) ℚ))
    {A : Matrix (Fin d) (Fin N) ℚ} (hA : A ∈ menu) :
    rationalLinearProjectionNumeratorConstant A ≤
      homogeneousProjectionMenuNumeratorConstant menu := by
  exact Finset.le_sup (s := menu)
    (f := rationalLinearProjectionNumeratorConstant) hA

theorem homogeneousProjectionImageRadius_le_menuScale
    {N d M : ℕ}
    (menu : Finset (Matrix (Fin d) (Fin N) ℚ))
    {A : Matrix (Fin d) (Fin N) ℚ} (hA : A ∈ menu) :
    homogeneousProjectionImageRadius A M ≤
      max 1 (homogeneousProjectionMenuNumeratorConstant menu) * max 1 M := by
  apply max_le
  · have hleft : 1 ≤ max 1 (homogeneousProjectionMenuNumeratorConstant menu) :=
      Nat.le_max_left _ _
    have hright : 1 ≤ max 1 M := Nat.le_max_left _ _
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hleft))
        (Nat.ne_of_gt (Nat.zero_lt_of_lt hright)))
  · exact Nat.mul_le_mul
      ((rationalLinearProjectionNumeratorConstant_le_menuConstant
        menu hA).trans (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)

theorem one_le_homogeneousProjectionImageRadius {N d : ℕ}
    (A : Matrix (Fin d) (Fin N) ℚ) (M : ℕ) :
    1 ≤ homogeneousProjectionImageRadius A M :=
  Nat.le_max_left _ _

/-- Literal membership of the projected displacement in the integer
hypersurface point set used by Salberger's affine theorem. -/
theorem integralNumeratorProjection_mem_translatedHypersurfacePoints
    {N r degree m M : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (x₀ z : IntVector (N + 1))
    (hbox : ∀ i, (z i).natAbs ≤ M)
    (hz : IsRationalConePoint I
      (intVectorToRat (integralAffineMap x₀ z m))) :
    integralNumeratorLinearProjection A z ∈
      Published.affineHypersurfaceIntegerPoints
        (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
        (homogeneousProjectionImageRadius A M : ℝ) := by
  rw [Published.affineHypersurfaceIntegerPoints]
  apply Finset.mem_filter.mpr
  have hcoordinate : ∀ i,
      (integralNumeratorLinearProjection A z i).natAbs ≤
        homogeneousProjectionImageRadius A M := by
    intro i
    exact (integralNumeratorLinearProjection_coordinate_natAbs_le
      A z hbox i).trans (Nat.le_max_right 1 _)
  refine ⟨?_, ?_,
    eval_integralTranslatedHomogeneousProjectionEquation_eq_zero
      I hI A G hprojection x₀ z hz⟩
  · rw [mem_integerSupNormBox_iff]
    simpa using hcoordinate
  · intro i
    simpa [Nat.cast_natAbs] using
      (show ((integralNumeratorLinearProjection A z i).natAbs : ℝ) ≤
          (homogeneousProjectionImageRadius A M : ℝ) by
        exact_mod_cast hcoordinate i)

/-- The degree bound for the homogeneous projection controls every literal
fibre on a normalized finite point set.  Notice that the source point in
the geometric fibre is `x₀ + m z`, whereas the integral target coordinate
is the cleared projection of `z`; the displayed affine identity is what
connects these two exact objects. -/
theorem integralNumeratorProjection_fibre_card_le_degree_of_homogeneousProjection
    {N r degree m : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (hm : 0 < m) (x₀ : IntVector (N + 1))
    (points : Finset (IntVector (N + 1)))
    (hsource : ∀ z ∈ points,
      IsRationalConePoint I
        (intVectorToRat (integralAffineMap x₀ z m)))
    (target : IntVector (r + 2)) :
    (points.filter fun z ↦
      integralNumeratorLinearProjection A z = target).card ≤ degree := by
  classical
  let y : Fin (r + 2) → ℚ := fun i ↦
    rationalLinearProjection A (intVectorToRat x₀) i +
      (m : ℚ) * rationalTargetOfIntegralNumerator A.den target i
  let fibre : Set (Fin (N + 1) → ℚ) :=
    {x | IsRationalConePoint I x ∧ rationalLinearProjection A x = y}
  have hfibres :=
    rationalConeProjection_fibres_of_homogeneousProjection
      I hI A G hprojection y
  have hfibreFinite : fibre.Finite := by
    simpa only [fibre] using hfibres.1
  let sourceMap : IntVector (N + 1) → Fin (N + 1) → ℚ :=
    fun z ↦ intVectorToRat (integralAffineMap x₀ z m)
  have hmaps : Set.MapsTo sourceMap
      (↑(points.filter fun z ↦
        integralNumeratorLinearProjection A z = target) :
          Set (IntVector (N + 1)))
      (↑hfibreFinite.toFinset : Set (Fin (N + 1) → ℚ)) := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hprojectionZ :
        rationalLinearProjection A (intVectorToRat z) =
          rationalTargetOfIntegralNumerator A.den target :=
      rationalLinearProjection_eq_target_of_integralNumerator_eq
        A z target hz'.2
    have hprojectionSource :
        rationalLinearProjection A
            (intVectorToRat (integralAffineMap x₀ z m)) = y := by
      rw [rationalLinearProjection_integralAffineMap, hprojectionZ]
    apply hfibreFinite.mem_toFinset.mpr
    change IsRationalConePoint I
        (intVectorToRat (integralAffineMap x₀ z m)) ∧
      rationalLinearProjection A
        (intVectorToRat (integralAffineMap x₀ z m)) = y
    exact ⟨hsource z hz'.1, hprojectionSource⟩
  have hmapInjective : Function.Injective sourceMap := by
    exact intVectorToRat_injective.comp
      (integralAffineMap_injective hm x₀)
  have hcard :
      (points.filter fun z ↦
        integralNumeratorLinearProjection A z = target).card ≤
          hfibreFinite.toFinset.card :=
    Finset.card_le_card_of_injOn sourceMap hmaps hmapInjective.injOn
  calc
    (points.filter fun z ↦
        integralNumeratorLinearProjection A z = target).card ≤
        hfibreFinite.toFinset.card := hcard
    _ = Set.ncard fibre :=
      (Set.ncard_eq_toFinset_card fibre hfibreFinite).symm
    _ ≤ degree := by simpa only [fibre] using hfibres.2

/-! ## The coefficient-uniform Salberger estimate on the literal image -/

/-- Direct application of Salberger 2023, Theorem 0.4, to a normalized
finite set on a homogeneous affine cone.  Every map, image equation, and
fibre used in the count is displayed above. -/
theorem finiteNormalizedConePointSet_card_le_salberger2023_of_homogeneousProjection
    (hSalberger : Published.Salberger2023Theorem04)
    {N r degree m M : ℕ}
    (hTargetDimension : 3 ≤ r + 2)
    (hDegreeRange : degree = 3 ∨ 4 ≤ degree)
    (ε : ℝ) (hε : 0 < ε)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hIgeometric : GeometricallyPrimeMvPolynomialIdeal I)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection :
      StandardAG.IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) I hI A G)
    (hm : 0 < m) (x₀ : IntVector (N + 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (points : Finset (IntVector (N + 1))),
        (∀ z ∈ points, ∀ j, (z j).natAbs ≤ M) →
        (∀ z ∈ points,
          IsRationalConePoint I
            (intVectorToRat (integralAffineMap x₀ z m))) →
        (points.card : ℝ) ≤
          C * (homogeneousProjectionImageRadius A M : ℝ) ^
            Published.salberger2023AffineExponent (r + 2) degree ε := by
  have htop :=
    integralTranslatedHomogeneousProjectionEquation_topPart
      I hI hIgeometric A G hprojection x₀ hm
  obtain ⟨C, hC, hbound⟩ :=
    finiteSet_card_le_salberger2023_affineHypersurface
      (Point := IntVector (N + 1)) hSalberger
      (r + 2) degree degree hTargetDimension hDegreeRange ε hε
  refine ⟨C, hC, ?_⟩
  intro points hbox hsource
  apply hbound
    (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
    (rationalTranslatedHomogeneousProjectionTopPart G m degree)
    htop.1 htop.2 (homogeneousProjectionImageRadius A M : ℝ)
    (by exact_mod_cast one_le_homogeneousProjectionImageRadius A M)
    points (integralNumeratorLinearProjection A)
  · intro z hz
    exact integralNumeratorProjection_mem_translatedHypersurfacePoints
      I hI A G hprojection x₀ z (hbox z hz) (hsource z hz)
  · intro target _htarget
    exact
      integralNumeratorProjection_fibre_card_le_degree_of_homogeneousProjection
        I hI A G hprojection hm x₀ points hsource target

/-- Coefficient-uniform affine-six estimate for all degree-at-least-four
homogeneous cone images of a fixed bounded degree.  The constant is chosen
before the cone ideal, projection matrix, image equation, affine centre,
dilation, and finite point set.  The only dependence on the particular
projection in the right-hand side is its explicit image radius. -/
theorem finiteNormalizedConeFourfoldPointSet_card_le_salberger2023_boundedDegree
    (hSalberger : Published.Salberger2023Theorem04)
    (N degreeBound : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {degree m M : ℕ}, 4 ≤ degree → degree ≤ degreeBound →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hI : I.IsPrime),
        GeometricallyPrimeMvPolynomialIdeal I →
      ∀
        (A : Matrix (Fin 6) (Fin (N + 1)) ℚ)
        (G : MvPolynomial (Fin 6) ℚ),
        StandardAG.IsHomogeneousFiniteBirationalLinearProjection
            (r := 4) (degree := degree) I hI A G →
        0 < m →
        ∀ (x₀ : IntVector (N + 1))
          (points : Finset (IntVector (N + 1))),
          (∀ z ∈ points, ∀ j, (z j).natAbs ≤ M) →
          (∀ z ∈ points,
            IsRationalConePoint I
              (intVectorToRat (integralAffineMap x₀ z m))) →
          (points.card : ℝ) ≤
            C * (homogeneousProjectionImageRadius A M : ℝ) ^
              ((4 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    finiteSet_card_le_salberger2023_affineSix_boundedDegree
      (Point := IntVector (N + 1)) hSalberger
      degreeBound degreeBound ε hε
  refine ⟨C, hC, ?_⟩
  intro degree m M hdegree hdegreeBound I hI hIgeometric A G hprojection hm
    x₀ points hbox hsource
  have htop :=
    integralTranslatedHomogeneousProjectionEquation_topPart
      I hI hIgeometric A G hprojection x₀ hm
  apply hbound degree hdegree hdegreeBound
    (integralTranslatedHomogeneousProjectionEquation A G x₀ m)
    (rationalTranslatedHomogeneousProjectionTopPart G m degree)
    htop.1 htop.2 (homogeneousProjectionImageRadius A M : ℝ)
    (by exact_mod_cast one_le_homogeneousProjectionImageRadius A M)
    points (integralNumeratorLinearProjection A)
  · intro z hz
    exact integralNumeratorProjection_mem_translatedHypersurfacePoints
      I hI A G hprojection x₀ z (hbox z hz) (hsource z hz)
  · intro target _htarget
    exact
      (integralNumeratorProjection_fibre_card_le_degree_of_homogeneousProjection
        I hI A G hprojection hm x₀ points hsource target).trans
          hdegreeBound

/-- The literal proper-fourfold estimate obtained from the finite uniform
projection menu and Salberger 2023.  Both constants are selected before the
fourfold ideal, its degree, the affine centre and scale, and the finite point
set.  The target radius is a fixed multiple of the original normalized box
radius; no projection coefficient is absorbed after the variety is chosen. -/
theorem exists_uniform_normalizedProperFourfold_salbergerBound
    (hSalberger : Published.Salberger2023Theorem04)
    (hProjection : StandardAG.BoundedDegreeHomogeneousProjectionMenu)
    (N degreeBound : ℕ) (hAmbient : 4 < N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {degree m M : ℕ}
        (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hI : I.IsPrime),
        GeometricallyPrimeMvPolynomialIdeal I →
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        ¬ (Published.projectiveIrrelevantIdeal ℚ N ≤ I) →
        Published.HasProjectiveDimensionDegree I 4 degree →
        4 ≤ degree → degree ≤ degreeBound →
        0 < m →
        ∀ (x₀ : IntVector (N + 1))
          (points : Finset (IntVector (N + 1))),
          (∀ z ∈ points, ∀ j, (z j).natAbs ≤ M) →
          (∀ z ∈ points,
            IsRationalConePoint I
              (intVectorToRat (integralAffineMap x₀ z m))) →
          (points.card : ℝ) ≤
            C * ((K * max 1 M : ℕ) : ℝ) ^ ((4 : ℝ) + ε) := by
  obtain ⟨menu, hmenu⟩ := hProjection N 4 degreeBound hAmbient
  obtain ⟨C, hC, hcount⟩ :=
    finiteNormalizedConeFourfoldPointSet_card_le_salberger2023_boundedDegree
      hSalberger N degreeBound ε hε
  let K : ℕ := max 1 (homogeneousProjectionMenuNumeratorConstant menu)
  refine ⟨K, C, hC, ?_⟩
  intro degree m M I hI hgeometric hhomogeneous hirrelevant
    hdimension hdegree hdegreeBound hm x₀ points hbox hsource
  obtain ⟨A, hA, G, hAG⟩ :=
    hmenu I hI hgeometric hhomogeneous hirrelevant degree hdimension
      hdegreeBound
  have hraw := hcount hdegree hdegreeBound I hI hgeometric A G hAG hm
    x₀ points hbox hsource
  have hradiusNat : homogeneousProjectionImageRadius A M ≤ K * max 1 M := by
    simpa only [K] using
      homogeneousProjectionImageRadius_le_menuScale menu hA
  have hradiusReal :
      (homogeneousProjectionImageRadius A M : ℝ) ≤
        ((K * max 1 M : ℕ) : ℝ) := by
    exact_mod_cast hradiusNat
  have hexponent : (0 : ℝ) ≤ (4 : ℝ) + ε :=
    add_nonneg (by norm_num) hε.le
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hradiusReal hexponent) hC.le)

end

end TranslatedDepthSeven
