import TranslatedDepthSeven.IsolatedVertexCoordinateBridge
import TranslatedDepthSeven.StandardAlgebraicGeometry
import TranslatedDepthSeven.HomogeneousCone

/-!
# From a projective vertex to a literal product coordinate

This file closes the algebraic-geometric seam in the isolated-vertex branch.
The geometric hypothesis is written over an algebraic closure: the nonzero
vector `h` represents a point of the projective variety and every projective
line joining `[h]` to a geometric point of the variety is contained in the
variety.  The standard cone--vertex lemma then says that the rational
homogeneous radical ideal is stable under all affine translations along `h`.

Two universal textbook inputs are displayed separately.  The first is the
Nullstellensatz/descent implication from the geometric line condition to
ideal stability.  The second is the characteristic-zero cylinder lemma from
`IsolatedVertexCoordinateBridge`, which chooses homogeneous generators
independent of the translation coordinate.  Everything after those inputs is
formal: denominator clearing, a unimodular integral coordinate change, and
the exact first-coordinate fibre count from `FirstCoordinateProduct`.

No point-counting estimate for an algebraic variety is assumed here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Extension of a rational homogeneous ideal to the fixed algebraic closure
used throughout the strict proof. -/
def rationalIdealGeometricExtension {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) ℚ)) :
    Ideal (MvPolynomial (Fin m) StandardAG.GeometricRationals) :=
  I.map (MvPolynomial.map
    (algebraMap ℚ StandardAG.GeometricRationals))

/-- The algebraic-closure representative of an integral direction. -/
def geometricDirectionOfIntVector {m : ℕ} (h : IntVector m) :
    Fin m → StandardAG.GeometricRationals :=
  fun i ↦ algebraMap ℚ StandardAG.GeometricRationals (h i : ℚ)

/-- A concrete affine-cone formulation of `[h]` belonging to the projective
vertex of `Proj(Q[x]/I)`.  Besides requiring `h` itself to vanish on the
geometric extension of `I`, it requires the complete two-parameter span of
`h` and every nonzero geometric cone point to vanish on that extension.

For a homogeneous ideal this is exactly the usual statement that every
projective line joining `[h]` to a geometric point of the projective variety
is contained in the variety. -/
def LiesInGeometricProjectiveVertex {m : ℕ}
    (h : IntVector m) (I : Ideal (MvPolynomial (Fin m) ℚ)) : Prop :=
  h ≠ 0 ∧
    (∀ f ∈ rationalIdealGeometricExtension I,
      MvPolynomial.eval (geometricDirectionOfIntVector h) f = 0) ∧
    ∀ (x : Fin m → StandardAG.GeometricRationals),
      x ≠ 0 →
      (∀ f ∈ rationalIdealGeometricExtension I,
        MvPolynomial.eval x f = 0) →
      ∀ (s t : StandardAG.GeometricRationals)
        (f : MvPolynomial (Fin m) StandardAG.GeometricRationals),
        f ∈ rationalIdealGeometricExtension I →
          MvPolynomial.eval
            (s • x + t • geometricDirectionOfIntVector h) f = 0

namespace StandardAG

/-- The cone--vertex lemma for a homogeneous radical ideal.

Indeed, the line condition with `s=1` makes the geometric affine cone stable
under translation by every scalar multiple of `h`.  Hilbert's
Nullstellensatz identifies the ideal of that cone with the radical of the
extended ideal; inverse translation gives equality rather than inclusion.
Faithfully flat descent from `Qbar` to `Q` then gives the displayed rational
ideal equality.

This is a standard structural fact about projective cones; it contains no
degree, height, or point-counting conclusion. -/
def ProjectiveVertexIdealTranslationStability : Prop :=
  ∀ (m : ℕ) (I : Ideal (MvPolynomial (Fin m) ℚ))
      (h : IntVector m),
    I.IsRadical →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℚ) →
    LiesInGeometricProjectiveVertex h I →
      RationalIdealTranslationInvariant h I

end StandardAG

/-- Direct specialization of the textbook cone--vertex lemma. -/
theorem rationalIdealTranslationInvariant_of_geometricProjectiveVertex
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℚ))
    (h : IntVector m) (hIradical : I.IsRadical)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℚ))
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    RationalIdealTranslationInvariant h I :=
  hvertexTheorem m I h hIradical hIhomogeneous hvertex

/-- Prime-ideal form of the preceding implication. -/
theorem rationalIdealTranslationInvariant_of_geometricProjectiveVertex_of_prime
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℚ))
    (h : IntVector m) (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℚ))
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    RationalIdealTranslationInvariant h I :=
  rationalIdealTranslationInvariant_of_geometricProjectiveVertex
    hvertexTheorem I h hIprime.isRadical hIhomogeneous hvertex

/-- The complete structural reduction from a geometric projective vertex to
integral equations which, after a unimodular change of coordinates, are
literal lifts from one fewer variable. -/
theorem exists_unimodular_firstCoordinateEquationReduction_of_projectiveVertex
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hIradical : I.IsRadical)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (h : IntVector (n + 1)) (hprimitive : PrimitiveDirection h)
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    ∃ (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
        (U : IntegralUnimodularChange (n + 1))
        (lowerEquations : Finset (MvPolynomial (Fin n) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equations :
            Set (MvPolynomial (Fin (n + 1)) ℤ))) = I ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equations =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ x : IntVector (n + 1),
        IntegralCommonZero (liftEquationFinsetAfterFirst lowerEquations)
            (U.pointEquiv x) ↔
          IntegralCommonZero equations x := by
  apply exists_unimodular_firstCoordinateEquationReduction_of_ideal
    hcylinder hcompletion I hIhomogeneous h hprimitive
  exact rationalIdealTranslationInvariant_of_geometricProjectiveVertex
    hvertexTheorem I h hIradical hIhomogeneous hvertex

/-- An integral point vanishes on a rational ideal after the evident
coefficient and coordinate embedding. -/
def IntegralPointVanishesOnRationalIdeal {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) ℚ)) (x : IntVector m) : Prop :=
  ∀ f ∈ I, MvPolynomial.eval (fun i ↦ (x i : ℚ)) f = 0

/-- If an integral equation family generates `I` after extending
coefficients to `Q`, every integral zero of `I` is a common zero of that
family. -/
theorem integralCommonZero_of_vanishesOnRationalIdeal
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℚ))
    (equations : Finset (MvPolynomial (Fin m) ℤ))
    (hideal : Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
        (Ideal.span (equations : Set (MvPolynomial (Fin m) ℤ))) = I)
    (x : IntVector m) (hx : IntegralPointVanishesOnRationalIdeal I x) :
    IntegralCommonZero equations x := by
  intro f hf
  let φ : MvPolynomial (Fin m) ℤ →+* MvPolynomial (Fin m) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hfspan : f ∈ Ideal.span
      (equations : Set (MvPolynomial (Fin m) ℤ)) :=
    Ideal.subset_span hf
  have hfI : φ f ∈ I := by
    rw [← hideal]
    exact Ideal.mem_map_of_mem φ hfspan
  have heval := hx (φ f) hfI
  have heval' :
      MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 := by
    simpa [φ] using heval
  rw [eval_map_intCast] at heval'
  exact Int.cast_eq_zero.mp heval'

/-- Final exact composition with `FirstCoordinateProduct`.  The transformed
box hypothesis is stated explicitly because an arbitrary unimodular change
need not preserve a sup-norm box.  Subject to that honest hypothesis, the
first coordinate contributes exactly the elementary factor `2M+1`; all
remaining points are counted by the lower-dimensional equations. -/
theorem exists_isolatedVertex_productBound
    (hvertexTheorem : StandardAG.ProjectiveVertexIdealTranslationStability)
    (hcylinder : StandardAG.TranslationStableHomogeneousIdealCylinderGenerators)
    (hcompletion : StandardLattice.PrimitiveDirectionUnimodularCompletion)
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hIradical : I.IsRadical)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℚ))
    (h : IntVector (n + 1)) (hprimitive : PrimitiveDirection h)
    (hvertex : LiesInGeometricProjectiveVertex h I) :
    ∃ (equations : Finset (MvPolynomial (Fin (n + 1)) ℤ))
        (U : IntegralUnimodularChange (n + 1))
        (lowerEquations : Finset (MvPolynomial (Fin n) ℤ)),
      Ideal.map (MvPolynomial.map (Int.castRingHom ℚ))
          (Ideal.span (equations :
            Set (MvPolynomial (Fin (n + 1)) ℤ))) = I ∧
      Matrix.mulVec U.forward h = firstCoordinateIntDirection ∧
      U.transformEquationFinset equations =
          liftEquationFinsetAfterFirst lowerEquations ∧
      (∀ g ∈ lowerEquations, ∃ d : ℕ, g.IsHomogeneous d) ∧
      ∀ (M : ℕ) (points : Finset (IntVector (n + 1))),
        (∀ x ∈ points, ∀ i, ((U.pointEquiv x) i).natAbs ≤ M) →
        (∀ x ∈ points, IntegralPointVanishesOnRationalIdeal I x) →
          points.card ≤ (2 * M + 1) *
            (integralCommonZeroInBox (M := M) lowerEquations).card := by
  obtain ⟨equations, U, lowerEquations, hideal, hforward,
      hfamily, hhomogeneous, hzero⟩ :=
    exists_unimodular_firstCoordinateEquationReduction_of_projectiveVertex
      hvertexTheorem hcylinder hcompletion I hIradical hIhomogeneous h
      hprimitive hvertex
  refine ⟨equations, U, lowerEquations, hideal, hforward, hfamily,
    hhomogeneous, ?_⟩
  intro M points hbox hpoints
  let transformedPoints : Finset (IntVector (n + 1)) :=
    points.map U.pointEquiv.toEmbedding
  have htransformedBox : ∀ y ∈ transformedPoints, ∀ i,
      (y i).natAbs ≤ M := by
    intro y hy i
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact hbox x hx i
  have htransformedZero : ∀ y ∈ transformedPoints,
      IntegralCommonZero
        (liftEquationFinsetAfterFirst lowerEquations) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact (hzero x).2
      (integralCommonZero_of_vanishesOnRationalIdeal
        I equations hideal x (hpoints x hx))
  have hbound :=
    card_le_interval_mul_integralCommonZeroInBox_of_lifted_equations
      lowerEquations transformedPoints htransformedBox htransformedZero
  simpa [transformedPoints] using hbound

end

end TranslatedDepthSeven
