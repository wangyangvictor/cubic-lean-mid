import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.GeometricPrimeness
import TranslatedDepthSeven.JacobianMinorStandardSmoothChart
import TranslatedDepthSeven.PublishedCountingTheorems
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import TranslatedDepthSeven.RationalPointLocalPolynomialExtension
import TranslatedDepthSeven.FiniteGaloisIdealDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A precise boundary for standard algebraic geometry

This file gives names to the standard algebraic-geometric propositions that
may be cited without formalizing their textbook proofs.  Every unproved
external principle below is a `def` whose value is a proposition; the other
declarations are data definitions or elementary conversion lemmas.  In
particular, this file adds no axiom and proves none of the external
propositions merely by naming it.

The statements use literal polynomial ideals, minimal primes, Hilbert
functions, local rings, coefficient specialization, and algebra maps.  They
do not contain a counting estimate or a conclusion tailored to an analytic
application.

The main references are:

* Hartshorne, *Algebraic Geometry*, Chapter I, Section 7 (Hilbert
  polynomials, degree, and the hypersurface case of Bézout), Fulton,
  *Intersection Theory*, Section 8.4 (general projective Bézout), and
  Harris, *Algebraic Geometry: A First Course*, Lecture 18, Corollary 18.12
  (the degree--span inequality);
* the Stacks Project, Sections 10.58 and 10.60 (Hilbert functions and
  dimension), Section 43.16 (Tag `0B04`, proper intersections), and Section
  43.23 (Tag `0B1N`, linear projections);
* the Stacks Project, Section 37.27 (Tag `0553`, components of fibres),
  Section 37.54 (Tag `0H3Y`, generic-flatness stratification), and Section
  38.21 (Tag `052F`, flattening stratifications);
* the Stacks Project, Lemmas 10.137.9 (`00TA`), 10.140.2 (`00TS`), and
  10.140.3 (`00TT`) for standard-smooth local equations, Lemma 10.138.14
  (`00TP`) for spreading out smooth algebras, and Section 29.35 (`01V4`)
  for base change and openness of smoothness;
* the Stacks Project, Proposition 35.3.9 (Tag `023N`) and Section 10.164
  (Tag `033D`) for faithfully flat descent.  For a finite Galois extension,
  the ideal statement below is also the usual trace-dual proof of Galois
  descent.

The relative-component proposition is deliberately stated fibrewise after a
finite locally closed stratification.  It does **not** assert that individual
geometric components admit global labels over a stratum; that assertion is
false in the presence of monodromy.  A component list is chosen only after
the geometric parameter point has been fixed.
-/

namespace TranslatedDepthSeven
namespace StandardAG

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators TensorProduct
open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Exact Hilbert-polynomial certificates -/

/-- The entire cumulative affine Hilbert polynomial, rather than only its
degree and leading coefficient. -/
def HasAffineDimensionDegreeWithPolynomial
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (n d : ℕ) (P : Polynomial ℚ) : Prop :=
  I.IsPrime ∧
    ringKrullDim (MvPolynomial (Fin N) K ⧸ I) = n ∧
    0 < d ∧
    P.natDegree = n ∧
    P.leadingCoeff = (d : ℚ) / n.factorial ∧
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (Module.finrank K (Published.affineHilbertFiltration K N I k) : ℚ) =
        P.eval (k : ℚ)

/-- The entire homogeneous projective Hilbert polynomial. -/
def HasProjectiveDimensionDegreeWithPolynomial
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (r d : ℕ) (P : Polynomial ℚ) : Prop :=
  ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) = r + 1 ∧
    0 < d ∧
    P.natDegree = r ∧
    P.leadingCoeff = (d : ℚ) / r.factorial ∧
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (Module.finrank K (Published.projectiveHilbertPiece K N I k) : ℚ) =
        P.eval (k : ℚ)

/-- Forgetting the chosen affine Hilbert polynomial recovers the published
dimension--degree predicate used by the counting interfaces. -/
theorem HasAffineDimensionDegreeWithPolynomial.toPublished
    {K : Type u} [Field K] {N n d : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)} {P : Polynomial ℚ}
    (h : HasAffineDimensionDegreeWithPolynomial I n d P) :
    Published.HasAffineDimensionDegree I n d :=
  ⟨h.1, h.2.1, h.2.2.1, P, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2⟩

/-- Forgetting the chosen projective Hilbert polynomial recovers the
published dimension--degree predicate. -/
theorem HasProjectiveDimensionDegreeWithPolynomial.toPublished
    {K : Type u} [Field K] {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) K)} {P : Polynomial ℚ}
    (h : HasProjectiveDimensionDegreeWithPolynomial I r d P) :
    Published.HasProjectiveDimensionDegree I r d :=
  ⟨h.1, h.2.1, P, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Hilbert--Serre and the dimension theorem for affine prime quotients.

Reference: Stacks Project, Sections 10.58 and 10.60; Hartshorne, Chapter I,
Section 7. -/
def AffineHilbertDegreeCertification
    (K : Type u) [Field K] : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) K)),
    I.IsPrime →
      ∃ n d : ℕ, ∃ P : Polynomial ℚ,
        HasAffineDimensionDegreeWithPolynomial I n d P

/-- Hilbert--Serre for a nonempty integral projective closed subscheme.  The
condition on the irrelevant ideal excludes the empty projective scheme (the
homogeneous maximal ideal of the cone vertex).

Reference: Stacks Project, Sections 10.58 and 10.60; Hartshorne, Chapter I,
Section 7. -/
def ProjectiveHilbertDegreeCertification
    (K : Type u) [Field K] : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) →
    ¬ Published.projectiveIrrelevantIdeal K N ≤ I →
      ∃ r d : ℕ, ∃ P : Polynomial ℚ,
        HasProjectiveDimensionDegreeWithPolynomial I r d P

/-! ## Projective intersections and linear spans -/

/-- An ideal regarded as a coefficient-field submodule of its polynomial
ring. -/
def idealAsCoefficientSubmodule
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) :
    Submodule K (MvPolynomial (Fin N) K) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro c f hf
    simpa only [MvPolynomial.smul_eq_C_mul] using
      I.mul_mem_left (MvPolynomial.C c) hf

/-- The degree-one part of a homogeneous ideal.  Its dimension is the number
of independent hyperplanes containing the corresponding projective closed
subscheme. -/
def degreeOnePartInIdeal
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) :
    Submodule K (MvPolynomial (Fin N) K) :=
  idealAsCoefficientSubmodule I ⊓
    MvPolynomial.homogeneousSubmodule (Fin N) K 1

/-- Literal properness of an intersection, including a fixed projective
dimension and degree for every reduced irreducible component. -/
def IsProperProjectiveIntersection
    {K : Type u} [Field K] {N : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K))
    (r s : ℕ) : Prop :=
  N ≤ r + s ∧
    ∀ P ∈ finiteMinimalPrimes (I ⊔ J),
      ∃ d : ℕ,
        Published.HasProjectiveDimensionDegree P (r + s - N) d

/-- Reduced-component form of projective Bézout.  Scheme-theoretic
intersection multiplicities are positive, so forgetting them gives the
displayed inequality for the sum of the degrees of the reduced components.

References: Fulton, *Intersection Theory*, Section 8.4; Stacks Project,
Sections 43.13--43.26 (`0AZQ`, `0B08`, `0B0F`, `0B0G`) for proper
intersection products and Chow rings.  Hartshorne, Theorem I.7.7 is the
special case in which one factor is a hypersurface. -/
def ProjectiveProperIntersectionBezout
    (K : Type u) [Field K] : Prop :=
  ∀ (N r s d e : ℕ)
    (I J : Ideal (MvPolynomial (Fin (N + 1)) K)),
    I.IsPrime →
    J.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) →
    J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) →
    Published.HasProjectiveDimensionDegree I r d →
    Published.HasProjectiveDimensionDegree J s e →
    IsProperProjectiveIntersection I J r s →
      ∃ componentDegree : Ideal (MvPolynomial (Fin (N + 1)) K) → ℕ,
        (∀ P ∈ finiteMinimalPrimes (I ⊔ J),
          Published.HasProjectiveDimensionDegree P (r + s - N)
            (componentDegree P)) ∧
        ∑ P ∈ finiteMinimalPrimes (I ⊔ J), componentDegree P ≤ d * e

/-- The classical degree--span inequality in its coordinate-ring form.
For a geometrically integral `r`-fold of degree `d` in `P^N`, it says
`dim Span(X) ≤ r + d - 1`, equivalently that the ideal contains at least
`N-r-d+1` independent linear forms.

Geometric integrality is essential over a non-algebraically-closed field.
For example, the kernel of
`Q[x₀,x₁,x₂,x₃] → Q(√2)[u,v]`, given by
`(x₀,x₁,x₂,x₃) ↦ (u,v,√2*u,√2*v)`, is a homogeneous prime of
projective dimension one and degree two with no linear equation.  Over
`Qbar` it is the union of two conjugate skew lines.  Without the displayed
algebraic-closure primality hypothesis the proposed inequality would say
`4 ≤ 3` for this example.

Reference: Harris, *Algebraic Geometry: A First Course*, Lecture 18,
Corollary 18.12 (deduced there from Proposition 18.9 and hyperplane
sections). -/
def ProjectiveDegreeSpanInequality
    (K : Type u) [Field K] : Prop :=
  ∀ (N r d : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
    I.IsPrime →
    (I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))).IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) →
    Published.HasProjectiveDimensionDegree I r d →
      N + 1 ≤ Module.finrank K (degreeOnePartInIdeal I) + r + d

/-! ## Relative component stratification -/

/-- The algebraic closure used to state geometric fibre data. -/
abbrev GeometricRationals := AlgebraicClosure ℚ

/-- A polynomial in `N` fibre variables whose coefficients are polynomials
in `M` parameters. -/
abbrev RelativePolynomial (M N : ℕ) :=
  MvPolynomial (Fin N) (MvPolynomial (Fin M) ℚ)

/-- Specialize all parameter coefficients at a geometric parameter point. -/
def specializeRelativePolynomial {M N : ℕ}
    (u : Fin M → GeometricRationals) :
    RelativePolynomial M N →+* MvPolynomial (Fin N) GeometricRationals :=
  MvPolynomial.map
    (MvPolynomial.eval₂Hom (algebraMap ℚ GeometricRationals) u)

/-- The specialized ideal generated by a finite relative equation family. -/
def relativeFibreEquationIdeal {M N : ℕ}
    (equations : Finset (RelativePolynomial M N))
    (u : Fin M → GeometricRationals) :
    Ideal (MvPolynomial (Fin N) GeometricRationals) := by
  classical
  exact finiteEquationIdeal
    (equations.image (specializeRelativePolynomial u))

/-- A principal locally closed parameter stratum `V(closed) ∩ D(open)`.
Finite unions of such strata suffice after refining a constructible
stratification. -/
structure RelativeHilbertStratum (M : ℕ) where
  closedEquations : Finset (MvPolynomial (Fin M) ℚ)
  openEquation : MvPolynomial (Fin M) ℚ
  componentCount : ℕ
  componentDimension : Fin componentCount → ℕ
  componentDegree : Fin componentCount → ℕ
  componentHilbertPolynomial : Fin componentCount → Polynomial ℚ

/-- The closed ideal defining the closure of a displayed parameter stratum. -/
def RelativeHilbertStratum.parameterIdeal {M : ℕ}
    (S : RelativeHilbertStratum M) :
    Ideal (MvPolynomial (Fin M) ℚ) :=
  Ideal.span (S.closedEquations : Set (MvPolynomial (Fin M) ℚ))

/-- The displayed locally closed stratum has an integral closure over `ℚ`,
and its principal open is nonempty.  Geometric irreducibility is
deliberately not required: conjugate geometric branches are handled after a
finite extension of its function field. -/
def RelativeHilbertStratum.IsIntegral {M : ℕ}
    (S : RelativeHilbertStratum M) : Prop :=
  S.parameterIdeal.IsPrime ∧ S.openEquation ∉ S.parameterIdeal

/-- Membership in the literal locally closed stratum. -/
def RelativeHilbertStratum.Contains {M : ℕ}
    (S : RelativeHilbertStratum M)
    (u : Fin M → GeometricRationals) : Prop :=
  (∀ f ∈ S.closedEquations,
      MvPolynomial.eval₂ (algebraMap ℚ GeometricRationals) u f = 0) ∧
    MvPolynomial.eval₂ (algebraMap ℚ GeometricRationals) u
      S.openEquation ≠ 0

/-- A finite locally closed partition on which the complete component
Hilbert data are constant.  Component labels are fibrewise: the equivalence
to the actual finite minimal-prime set is chosen after `u` is fixed. -/
def IsRelativeComponentHilbertStratification {M N t : ℕ}
    (equations : Finset (RelativePolynomial M N))
    (strata : Fin t → RelativeHilbertStratum M) : Prop :=
  (∀ i, (strata i).IsIntegral) ∧
    (∀ u : Fin M → GeometricRationals,
      ∃! i : Fin t, (strata i).Contains u) ∧
    ∀ (i : Fin t) (u : Fin M → GeometricRationals),
      (strata i).Contains u →
        ∃ components : Fin (strata i).componentCount ≃
            {P // P ∈ finiteMinimalPrimes
              (relativeFibreEquationIdeal equations u)},
          ∀ j,
            HasAffineDimensionDegreeWithPolynomial
              (components j : Ideal
                (MvPolynomial (Fin N) GeometricRationals))
              ((strata i).componentDimension j)
              ((strata i).componentDegree j)
              ((strata i).componentHilbertPolynomial j)

/-- Finite relative component stratification with constant Hilbert data.
The statement allows monodromy, because it asks for no global ordering of
the geometric components over a stratum.

References: Stacks Project, Sections 37.27 (`0553`), 37.54 (`0H3Y`), and
38.21 (`052F`), together with constancy of the Hilbert polynomial in a flat
projective family.  This is a derived finite-stratification package, not the
statement of any one of those references: homogenization, flattening
stratification, constructibility of geometric irreducible components, and
Noetherian induction are combined.  Over the generic point of an integral
`ℚ`-stratum, the finitely many geometric components are defined over one
finite normal extension of the function field.  Galois orbits, rather than
individual geometric components, descend to the stratum; this is why the
statement labels components only after a geometric point is fixed. -/
def RelativeFiniteComponentHilbertStratification : Prop :=
  ∀ (M N : ℕ) (equations : Finset (RelativePolynomial M N)),
    ∃ t : ℕ, ∃ strata : Fin t → RelativeHilbertStratum M,
      IsRelativeComponentHilbertStratification equations strata

/-! ## Reduced components and triangular presentations -/

/-- The algebra map defined by displayed normalization coordinates on an
affine component. -/
def affineNormalizationMap
    {K : Type u} [Field K] {N s : ℕ}
    (P : Ideal (MvPolynomial (Fin N) K))
    (q : Fin s → MvPolynomial (Fin N) K) :
    MvPolynomial (Fin s) K →ₐ[K]
      (MvPolynomial (Fin N) K ⧸ P) :=
  (Ideal.Quotient.mkₐ K P).comp (MvPolynomial.aeval q)

/-- A literal Noether-normalization and triangular-integrality certificate
for one reduced irreducible component.  The component is represented by its
prime ideal `P`; `q` displays the normalization coordinates; every ambient
coordinate satisfies the displayed monic polynomial over the normalization
ring.  The final field records generic freeness on one principal open of
the normalization base.

The word "triangular" here has its classical algebraic meaning: after the
normalization variables have been fixed, the ambient coordinates are
successively algebraic and satisfy monic equations.  No ordering procedure
or point-dependent construction is part of the statement. -/
def IsReducedComponentTriangularPresentation
    {K : Type u} [Field K] {N s : ℕ}
    (P : Ideal (MvPolynomial (Fin N) K))
    (q : Fin s → MvPolynomial (Fin N) K)
    (relation : Fin N → Polynomial (MvPolynomial (Fin s) K))
    (freeDenominator : MvPolynomial (Fin s) K) : Prop := by
  let A := MvPolynomial (Fin N) K ⧸ P
  let g := affineNormalizationMap P q
  letI : Algebra (MvPolynomial (Fin s) K) A :=
    g.toRingHom.toAlgebra
  exact
    P.IsPrime ∧
    Function.Injective g ∧
    g.Finite ∧
    freeDenominator ≠ 0 ∧
    Module.Free (Localization (Submonoid.powers freeDenominator))
      (LocalizedModule (Submonoid.powers freeDenominator) A) ∧
    ∀ i,
      (relation i).Monic ∧
      (relation i).eval₂ g.toRingHom
        (Ideal.Quotient.mk P (MvPolynomial.X i)) = 0

/-- Each minimal prime of the radical of a finite equation ideal admits a
normalization with exactly its Hilbert dimension, monic coordinate
relations, and a principal open on which the finite module is free.

This is the field-level algebra used after passing to the generic point of
an irreducible parameter stratum.  Requiring
`P ∈ finiteMinimalPrimes I.radical` makes the reduced-support convention
literal and prevents nilpotent or embedded components from entering the
list.

References: Noether normalization, Stacks Project Section 10.115 (`00OW`),
especially Lemma 10.115.4 (`00OY`); generic freeness, Section 10.118
(`051Q`); and the elementary integrality criterion that a finite algebra is
generated by elements satisfying monic equations.  In this repository the
individual algebraic steps are also realized in
`PrimeAffineNoetherNormalization.lean` and
`FractionFieldFiniteCoefficientClearing.lean`.

For a relative family, this proposition may be applied at the generic point
of an irreducible parameter stratum.  A separate qualitative spreading
statement is nevertheless required: the generic reduced pieces and their
finitely many displayed coefficients must extend over one principal open,
and the closed complement must be treated by Noetherian induction.  The
literal boundary for that step is recorded in
`RelativeReducedEquidimensionalSpreading.lean`.  Only after the resulting
finite integral numerator and denominator polynomials have been displayed
do polynomial coefficient-height bounds under integral specialization
follow from elementary evaluation.  In particular, the fibrewise theorem
below must not be read as a uniform coefficient-height assertion. -/
def ReducedComponentTriangularization
    (K : Type u) [Field K] : Prop :=
  ∀ (N : ℕ) (I P : Ideal (MvPolynomial (Fin N) K))
    (s d : ℕ) (H : Polynomial ℚ),
    P ∈ finiteMinimalPrimes I.radical →
    HasAffineDimensionDegreeWithPolynomial P s d H →
      ∃ q : Fin s → MvPolynomial (Fin N) K,
      ∃ relation : Fin N → Polynomial (MvPolynomial (Fin s) K),
      ∃ freeDenominator : MvPolynomial (Fin s) K,
        IsReducedComponentTriangularPresentation
          P q relation freeDenominator

/-! ## Smooth local equations and spreading out -/

/-- At a smooth rational point of local dimension `s`, one can select
`N-s` global equations and `N-s` distinct variables so that the equations
generate the localized ideal and the selected Jacobian minor is nonzero.

References: Stacks Project, Lemmas `00TA`, `00TS`, and `00TT`, together
with the conormal exact sequence and Nakayama's lemma. -/
def SmoothLocalEquationExtraction
    (K : Type u) [Field K] : Prop :=
  ∀ (N s : ℕ) (I : Ideal (MvPolynomial (Fin N) K))
    (z : Fin N → K)
    (hz : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom),
    s ≤ N →
    ringKrullDim (AffineQuotientRationalPointLocalRing I z hz) = s →
    Algebra.FormallySmooth K
      (AffineQuotientRationalPointLocalRing I z hz) →
      ∃ equations : Fin (N - s) → MvPolynomial (Fin N) K,
      ∃ selectedVar : Fin (N - s) → Fin N,
        Function.Injective selectedVar ∧
        (∀ i, equations i ∈ I) ∧
        Ideal.map
            (algebraMap (MvPolynomial (Fin N) K)
              (Localization.AtPrime (affineEvaluationPrime z)))
            (Ideal.span (Set.range equations)) =
          Ideal.map
            (algebraMap (MvPolynomial (Fin N) K)
              (Localization.AtPrime (affineEvaluationPrime z))) I ∧
        MvPolynomial.eval z
          (selectedJacobianDeterminant equations selectedVar) ≠ 0

/-- Contract a rational affine ideal to an integral model. -/
def integralModelOfRationalAffineIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ)) :
    Ideal (MvPolynomial (Fin N) ℤ) :=
  I.comap (MvPolynomial.map (Int.castRingHom ℚ))

/-- The coefficientwise reduction of the contracted integral model. -/
def affineSpecialFibreIdeal {N p : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ)) :
    Ideal (MvPolynomial (Fin N) (ZMod p)) :=
  (integralModelOfRationalAffineIdeal I).map
    (MvPolynomial.map (Int.castRingHom (ZMod p)))

/-- A smooth rational point and its local dimension spread to all residue
characteristics outside one nonzero integer.  The special-fibre point and
its local ring are displayed literally.

References: Stacks Project, Lemma 10.138.14 (`00TP`) for spreading out a
smooth algebra, Section 29.35 (`01V4`) for base change and openness of
smoothness, and generic freeness (Section 37.54, `0H3Y`) for constancy of
the fibre dimension after one further localization. -/
def SmoothPointSpreading : Prop :=
  ∀ (N s : ℕ) (I : Ideal (MvPolynomial (Fin N) ℚ))
    (z : Fin N → ℤ)
    (hz : I ≤ RingHom.ker
      (MvPolynomial.aeval (fun i ↦ (z i : ℚ))).toRingHom),
    ringKrullDim
      (AffineQuotientRationalPointLocalRing I
        (fun i ↦ (z i : ℚ)) hz) = s →
    Algebra.FormallySmooth ℚ
      (AffineQuotientRationalPointLocalRing I
        (fun i ↦ (z i : ℚ)) hz) →
      ∃ Δ : ℤ, Δ ≠ 0 ∧
        ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
          letI : Fact p.Prime := ⟨hp⟩
          ∃ hpnt : affineSpecialFibreIdeal (p := p) I ≤
                RingHom.ker
                  (MvPolynomial.aeval (fun i ↦ (z i : ZMod p))).toRingHom,
              ringKrullDim
                  (AffineQuotientRationalPointLocalRing
                    (affineSpecialFibreIdeal (p := p) I)
                    (fun i ↦ (z i : ZMod p)) hpnt) = s ∧
                Algebra.FormallySmooth (ZMod p)
                  (AffineQuotientRationalPointLocalRing
                    (affineSpecialFibreIdeal (p := p) I)
                    (fun i ↦ (z i : ZMod p)) hpnt)

/-! ## Marked finite birational linear projection -/

/-- The homogeneous linear form given by one row of a matrix. -/
def projectiveMatrixLinearForm {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (i : Fin c) :
    MvPolynomial (Fin N) ℚ :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

/-- The algebra map on affine cones induced by a homogeneous linear matrix. -/
def projectiveMatrixCoordinateMap {N c : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin c) (Fin N) ℚ) :
    MvPolynomial (Fin c) ℚ →ₐ[ℚ]
      (MvPolynomial (Fin N) ℚ ⧸ I) :=
  (Ideal.Quotient.mkₐ ℚ I).comp
    (MvPolynomial.aeval (projectiveMatrixLinearForm A))

/-- Literal data asserted of a marked finite birational linear projection.
The equality of maximal ideals says that the full scheme-theoretic fibre at
the marked image is the single reduced marked point. -/
def IsMarkedFiniteBirationalLinearProjection
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (x : Fin (N + 1) → ℚ)
    (hx : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom)
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
  let targetPoint : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] ℚ :=
    MvPolynomial.aeval (fun i ↦ MvPolynomial.eval x
      (projectiveMatrixLinearForm A i))
  let sourcePoint : source →ₐ[ℚ] ℚ :=
    affineQuotientRationalPoint I x hx
  exact
    (∀ i, (projectiveMatrixLinearForm A i).IsHomogeneous 1) ∧
    h.Finite ∧
    imageIdeal = Ideal.span {G} ∧
    G.IsHomogeneous d ∧
    Irreducible G ∧
    Module.finrank (FractionRing image) (FractionRing source) = 1 ∧
    (∃ i, MvPolynomial.eval x (projectiveMatrixLinearForm A i) ≠ 0) ∧
    Ideal.map h.toRingHom (RingHom.ker targetPoint.toRingHom) =
      RingHom.ker sourcePoint.toRingHom ∧
    ∀ (L : Type) [Field L] [Algebra ℚ L]
      (y : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] L),
      Set.Finite {z : source →ₐ[ℚ] L | z.comp h = y} ∧
        Set.ncard {z : source →ₐ[ℚ] L | z.comp h = y} ≤ d

/-- Existence of a rational linear projection which is finite and
birational onto a hypersurface and is an isomorphism above a neighbourhood
of the image of the marked point.

This is the standard *derived corollary* of generic projection used at the
external boundary.  Starting with Lemmas 43.23.1 and 43.23.2 of the Stacks
Project (Section 43.23, Tag `0B1N`), iterate projection from rational centres
until the ambient projective space has dimension `r+1`.  At each stage the
second lemma preserves an isomorphism over a neighbourhood of the marked
image.  The final image is an integral hypersurface; birationality and
preservation of degree give its irreducible equation of degree `d`.  The
last fibre-cardinality clause in
`IsMarkedFiniteBirationalLinearProjection` is the usual Bézout bound for
intersection with the linear spaces which are projection fibres.  Rational
centres exist because the relevant nonempty opens are defined over the
infinite field `ℚ`.

No finite universal menu, coefficient bound, or effective detector is
asserted here.  Those require a separate bounded-degree incidence
calculation followed by finite-grid avoidance and are not verbatim
consequences of Tag `0B1N`. -/
def MarkedFiniteBirationalLinearProjection : Prop :=
  ∀ (N r d : ℕ), r < N →
    ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
      (hI : I.IsPrime),
      GeometricallyPrimeMvPolynomialIdeal I →
      I.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
      ¬ Published.projectiveIrrelevantIdeal ℚ N ≤ I →
      Published.HasProjectiveDimensionDegree I r d →
      ∀ (x : Fin (N + 1) → ℚ)
        (_hx0 : x ≠ 0)
        (hx : I ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom),
        Algebra.FormallySmooth ℚ
          (AffineQuotientRationalPointLocalRing I x hx) →
          ∃ A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ,
          ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
            IsMarkedFiniteBirationalLinearProjection
              (d := d) I hI x hx A G

/-! ## Galois descent -/

/-- Every geometric minimal component of a finite-type affine scheme is
defined over a finite Galois subextension of the chosen algebraic closure.
The ideal over that subextension is required literally to extend back to
the given geometric prime.

This is the finite-coefficient argument over a perfect ground field: the
geometric prime is finitely generated because the polynomial ring is
Noetherian; finitely many algebraic coefficients lie in one finite separable
extension, and their normal closure is finite Galois.  The perfectness
hypothesis is essential in positive characteristic and is automatic for the
characteristic-zero function fields considered here.  Mathlib's
corresponding coefficient-field construction is
`FiniteGaloisIntermediateField.adjoin`; the specialized construction for
finite polynomial families is formalized in
`QbarFiniteCoefficientField.lean`. -/
def GeometricComponentFiniteGaloisField
    (K : Type u) [Field K] [PerfectField K] : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin N) K))
    (P : Ideal (MvPolynomial (Fin N) (AlgebraicClosure K))),
    P ∈ finiteMinimalPrimes
      (I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) →
      ∃ L : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      ∃ Q : Ideal (MvPolynomial (Fin N) L),
        Q ∈ finiteMinimalPrimes
          (I.map (MvPolynomial.map (algebraMap K L))) ∧
        Q.map (MvPolynomial.map L.val.toRingHom) = P

/-- A coefficientwise Galois-stable ideal over a finite Galois extension is
the scalar extension of its contraction.  Intersecting the conjugates of a
geometric component produces such a stable ideal, so this is the precise
algebraic operation which replaces a non-rational component by the reduced
union of its Galois orbit.

Reference: faithfully flat descent, Stacks Project Proposition 35.3.9
(`023N`).  For finite Galois extensions this exact polynomial-ideal formula
is the trace-dual argument formalized in `FiniteGaloisIdealDescent.lean`. -/
def FiniteGaloisInvariantIdealDescent
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop :=
  ∀ (N : ℕ) (J : Ideal (MvPolynomial (Fin N) L)),
    (∀ τ : L ≃ₐ[K] L, finiteGaloisConjugateIdeal τ J = J) →
      (J.comap (MvPolynomial.map (algebraMap K L))).map
        (MvPolynomial.map (algebraMap K L)) = J

/-- A coefficientwise Galois-stable ideal over an algebraic closure is the
extension of its rational contraction.  This formulation applies directly
to a reduced Galois-stable union of geometric components.

References: faithfully flat descent, Stacks Project Tag `023N` and Section
10.164 (`033D`); equivalently, finite coefficient descent followed by the
trace-dual argument over a finite Galois extension. -/
def QbarGaloisInvariantIdealDescent : Prop :=
  ∀ (N : ℕ)
    (P : Ideal (MvPolynomial (Fin N) GeometricRationals)),
    (∀ g : GeometricRationals ≃ₐ[ℚ] GeometricRationals,
      conjugateIdeal g P = P) →
      (P.comap
          (MvPolynomial.map (algebraMap ℚ GeometricRationals))).map
          (MvPolynomial.map (algebraMap ℚ GeometricRationals)) = P

end

end StandardAG
end TranslatedDepthSeven
