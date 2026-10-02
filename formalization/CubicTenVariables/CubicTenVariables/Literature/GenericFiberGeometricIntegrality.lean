import CubicTenVariables.Literature.FiberGeometricIntegralitySpreading
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
Two generic geometric-integrality inputs. They are explicit propositions;
no inhabitant and no axiom is declared.

`SmoothInfinityGeometricIntegrality` is the affine-hypersurface-at-infinity
corollary of Stacks Project, Lemma 33.25.10 (tag 0CDW): an integral variety
with a smooth rational point is geometrically integral.
https://stacks.math.columbia.edu/tag/0CDW
For an integral affine hypersurface f=0 of positive degree d, its projective
closure is integral. Its equation on the hyperplane at infinity is the top
homogeneous component of f. A nonzero rational zero of this component with
a nonzero partial derivative is a smooth rational point of that closure,
by the hypersurface Jacobian criterion. Thus the closure is geometrically
integral; its nonempty affine open f=0 is geometrically integral as well.
This is a corollary, not the verbatim statement of 0CDW. The input below
retains the actual equation, actual quotient domain, degree and partials.
It contains no cubic, anisotropy or selected-family hypothesis.

`GenericFiberGeometricIntegralityOpen` is the coordinate-ring corollary of
Stacks Project Lemma 37.26.4 (tag 0578) and Lemma 37.27.5 (tag 0559):
https://stacks.math.columbia.edu/tag/0578
https://stacks.math.columbia.edu/tag/0559
A geometrically reduced and geometrically irreducible generic fiber of a
finite-type morphism over an integral base has both properties over some
nonempty open of the base. Apply this to the explicitly presented family
over Spec Z[parameters], and choose one principal open D(g) inside the
intersection. Nonemptiness means g is nonzero. Geometric integrality may
be tested after the field extension Q(parameters) -> Qbar(parameters),
and then after an algebraic closure: Stacks Lemma 10.49.3 (tag 0FWF),
https://stacks.math.columbia.edu/tag/0FWF . Invariance under the initial
field extension follows from Lemmas 33.8.2 and 33.6.6, at
https://stacks.math.columbia.edu/tag/0364 and
https://stacks.math.columbia.edu/tag/035U .
No flatness, properness, fixed characteristic or prime-field-only condition
is needed. To ensure that g remains a nonzero polynomial in a particular
characteristic, applications separately exclude the prime divisors of one
nonzero coefficient. The supplied proposition does not assume or return a
cubic-specific exceptional-locus estimate.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11

/-- Generic affine hypersurface criterion via an actual smooth point of its
projective closure at infinity. This is the documented corollary of 0CDW. -/
def SmoothInfinityGeometricIntegrality : Prop :=
  ∀ (K : Type) [Field K] (n d : ℕ) (f : MvPolynomial (Fin n) K),
    0 < d → f.totalDegree = d →
    IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {f}) →
    (∃ x : Fin n → K, x ≠ 0 ∧
      eval x (homogeneousComponent d f) = 0 ∧
      ∃ i, eval x (pderiv i (homogeneousComponent d f)) ≠ 0) →
    IsDomain (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) f})

/-- The rational-function field over Qbar in the actual parameter variables. -/
abbrev GeometricParameterField (σ : Type) := FractionRing (MvPolynomial σ GeometricField)

/-- The literal generic parameter point in an algebraic closure of Qbar(parameters). -/
def geometricGenericParameter (σ : Type) : σ → AlgebraicClosure (GeometricParameterField σ) :=
  fun i => algebraMap (GeometricParameterField σ) (AlgebraicClosure (GeometricParameterField σ))
    (algebraMap (MvPolynomial σ GeometricField) (GeometricParameterField σ) (X i))

/-- A generic geometrically integral finitely presented affine family has
one nonzero integral parameter polynomial whose principal open consists of
geometrically integral fibers, in every characteristic. -/
def GenericFiberGeometricIntegralityOpen : Prop :=
  ∀ (σ τ ι : Type) [Fintype σ] [Fintype τ] [Fintype ι]
    (f : ι → MvPolynomial τ (MvPolynomial σ ℤ)),
    IsDomain (MvPolynomial τ (AlgebraicClosure (GeometricParameterField σ)) ⧸
      integralityFiberIdeal f (AlgebraicClosure (GeometricParameterField σ))
        (geometricGenericParameter σ)) →
    ∃ g : MvPolynomial σ ℤ, g ≠ 0 ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (v : σ → K),
        eval₂ (Int.castRingHom K) v g ≠ 0 →
        IsDomain (MvPolynomial τ K ⧸ integralityFiberIdeal f K v)

end CubicTenVariables.Literature
