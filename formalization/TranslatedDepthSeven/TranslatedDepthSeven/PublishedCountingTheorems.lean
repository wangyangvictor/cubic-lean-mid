import Mathlib
import TranslatedDepthSeven.AbsoluteIrreducibility
import TranslatedDepthSeven.IntegerBoxCount
import TranslatedDepthSeven.PrimitiveRationalVectorHeight

/-!
# The permitted published counting theorems

This file is the entire external mathematical boundary for the counting
results used in the translated depth-seven argument.  It contains one
bibliographically named proposition for each permitted published theorem:

* J. Pila, *Density of integral and rational points on varieties*,
  Astérisque 228 (1995), Theorem A;
* P. Salberger, *On the density of rational and integral points on
  algebraic varieties*, J. Reine Angew. Math. 606 (2007), Corollary 3.7;
* P. Salberger, *Counting rational points on projective varieties*,
  Proc. Lond. Math. Soc. 126 (2023), Theorems 0.1 and 0.4.

There is deliberately no external statement for a surface, curve, line, star, packet,
projection, or terminal contribution.  In particular, none of the
declarations below contains a conclusion already tailored to a branch of the
manuscript proof.

The geometric vocabulary is kept literal wherever Mathlib already supplies
it: polynomial ideals, homogeneous and saturated ideals, prime/radical
ideals, Krull dimension, Hilbert functions, polynomial zero sets, primitive
projective height, and integer boxes.  Mathlib does not presently package
Hilbert--Samuel multiplicity of a point on a special fibre, so below it is
spelled out through the eventual Hilbert polynomial of the finite jet
quotients.  No theorem about those quotients is postulated here; every
application must prove the required multiplicity assertion for its concrete
model.
-/

namespace TranslatedDepthSeven
namespace Published

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization
open Finset MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-! ## Literal dimension and degree predicates -/

/-- The degree-at-most-`k` image in an affine coordinate ring. -/
def affineHilbertFiltration (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin N) K)) (k : ℕ) :
    Submodule K (MvPolynomial (Fin N) K ⧸ I) :=
  (MvPolynomial.restrictTotalDegree (Fin N) K k).map
    (Ideal.Quotient.mkₐ K I).toLinearMap

instance affineHilbertFiltration_finite (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin N) K)) (k : ℕ) :
    Module.Finite K (affineHilbertFiltration K N I k) :=
  Module.Finite.map _ _

/-- The degree-`k` image in a homogeneous coordinate ring. -/
def projectiveHilbertPiece (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (k : ℕ) :
    Submodule K (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K k).map
    (Ideal.Quotient.mkₐ K I).toLinearMap

instance homogeneousSubmodule_finite (K : Type u) [Field K] (N k : ℕ) :
    Module.Finite K
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K k) := by
  let inclusion :
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K k →ₗ[K]
        MvPolynomial.restrictTotalDegree (Fin (N + 1)) K k :=
    Submodule.inclusion fun f hf ↦
      (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (MvPolynomial.IsHomogeneous.totalDegree_le hf)
  exact Module.Finite.of_injective inclusion
    (Submodule.inclusion_injective _)

instance projectiveHilbertPiece_finite (K : Type u) [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (k : ℕ) :
    Module.Finite K (projectiveHilbertPiece K N I k) :=
  Module.Finite.map _ _

/-- The cumulative affine Hilbert function is eventually a polynomial of
degree `n` and leading coefficient `d/n!`, with `d > 0`.  Together with
primality and the displayed Krull-dimension equality, this is the standard
coordinate-ring meaning of an irreducible affine variety of dimension `n`
and degree `d`. -/
def HasAffineDimensionDegree {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) (n d : ℕ) : Prop :=
  I.IsPrime ∧
    ringKrullDim (MvPolynomial (Fin N) K ⧸ I) = n ∧
    0 < d ∧
    ∃ P : Polynomial ℚ,
      P.natDegree = n ∧
      P.leadingCoeff = (d : ℚ) / n.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank K (affineHilbertFiltration K N I k) : ℚ) =
          P.eval (k : ℚ)

/-- The Hilbert-polynomial formulation of affine dimension and degree.
This is the datum used by Pila's theorem: for an irreducible affine
variety, the degree of the cumulative Hilbert polynomial is its dimension.
The separate Krull-dimension equality in `HasAffineDimensionDegree` is
useful elsewhere in the internal algebra, but is redundant at this
published counting boundary. -/
def HasAffineHilbertDimensionDegree {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K)) (n d : ℕ) : Prop :=
  I.IsPrime ∧
    0 < d ∧
    ∃ P : Polynomial ℚ,
      P.natDegree = n ∧
      P.leadingCoeff = (d : ℚ) / n.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank K (affineHilbertFiltration K N I k) : ℚ) =
          P.eval (k : ℚ)

theorem HasAffineDimensionDegree.toHilbert
    {K : Type u} [Field K] {N n d : ℕ}
    {I : Ideal (MvPolynomial (Fin N) K)}
    (hI : HasAffineDimensionDegree I n d) :
    HasAffineHilbertDimensionDegree I n d :=
  ⟨hI.1, hI.2.2.1, hI.2.2.2⟩

/-- The homogeneous Hilbert function is eventually a polynomial of degree
`r` and leading coefficient `d/r!`, with `d > 0`; the quotient ring has
Krull dimension `r + 1`. -/
def HasProjectiveDimensionDegree {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (r d : ℕ) : Prop :=
  ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) = r + 1 ∧
    0 < d ∧
    ∃ P : Polynomial ℚ,
      P.natDegree = r ∧
      P.leadingCoeff = (d : ℚ) / r.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank K (projectiveHilbertPiece K N I k) : ℚ) =
          P.eval (k : ℚ)

/-- Projective dimension and degree encoded by the homogeneous Hilbert
polynomial alone. -/
def HasProjectiveHilbertDimensionDegree
    {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (r d : ℕ) : Prop :=
  0 < d ∧
    ∃ P : Polynomial ℚ,
      P.natDegree = r ∧
      P.leadingCoeff = (d : ℚ) / r.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank K (projectiveHilbertPiece K N I k) : ℚ) =
          P.eval (k : ℚ)

theorem HasProjectiveDimensionDegree.toHilbert
    {K : Type u} [Field K] {N r d : ℕ}
    {I : Ideal (MvPolynomial (Fin (N + 1)) K)}
    (hI : HasProjectiveDimensionDegree I r d) :
    HasProjectiveHilbertDimensionDegree I r d :=
  ⟨hI.2.1, hI.2.2⟩

/-- The irrelevant ideal `(X₀,\ldots,X_N)` in a homogeneous coordinate
ring. -/
def projectiveIrrelevantIdeal (K : Type u) [Field K] (N : ℕ) :
    Ideal (MvPolynomial (Fin (N + 1)) K) :=
  Ideal.span (Set.range (MvPolynomial.X :
    Fin (N + 1) → MvPolynomial (Fin (N + 1)) K))

/-- Literal saturation with respect to the irrelevant ideal.  The right
hand side is the usual union of the colon ideals
`I : (X₀,\ldots,X_N)^k`; it is an increasing union, represented by its
supremum in the ideal lattice. -/
def IsSaturatedByProjectiveIrrelevantIdeal {K : Type u} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) : Prop :=
  I = ⨆ k : ℕ, I.colon ((projectiveIrrelevantIdeal K N) ^ k)

/-- A literal homogeneous prime ideal with the specified projective
dimension and degree. -/
def IsIntegralProjectiveVariety {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (r d : ℕ) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
    IsSaturatedByProjectiveIrrelevantIdeal I ∧
    I.IsPrime ∧ HasProjectiveDimensionDegree I r d

/-- The ideal-theoretic form of a reduced equidimensional projective closed
subscheme.  Equidimensionality is stated on the actual minimal primes. -/
def IsReducedEquidimensionalProjectiveScheme {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (r d : ℕ) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
    IsSaturatedByProjectiveIrrelevantIdeal I ∧
    I.radical = I ∧
    (∀ P ∈ I.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P) = r + 1) ∧
    HasProjectiveDimensionDegree I r d

/-- The hyperplane `x₀ = 0` contains no irreducible component.  For an
equidimensional projective scheme this is exactly proper intersection with
that hyperplane. -/
def InfinityHyperplaneMeetsProperly {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) : Prop :=
  ∀ P ∈ I.minimalPrimes, MvPolynomial.X (0 : Fin (N + 1)) ∉ P

/-! ## Concrete point sets and heights -/

/-- Integer points of strict affine height `< H` on the real zero set of an
ideal.  The ambient box makes this an actual finite set, rather than a set
whose finiteness is hidden in a counting convention. -/
def pilaIntegralPoints {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℝ)) (H : ℝ) : Finset (IntVector N) :=
  by
    classical
    exact (integerSupNormBox N ⌈H⌉₊).filter fun x ↦
      (∀ i, |(x i : ℝ)| < H) ∧
        ∀ f ∈ I, MvPolynomial.eval (fun i ↦ (x i : ℝ)) f = 0

/-- Integer zeros in the closed box `[-B,B]^N`. -/
def affineHypersurfaceIntegerPoints {N : ℕ}
    (f : MvPolynomial (Fin N) ℤ) (B : ℝ) : Finset (IntVector N) :=
  by
    classical
    exact (integerSupNormBox N ⌈B⌉₊).filter fun x ↦
      (∀ i, |(x i : ℝ)| ≤ B) ∧ MvPolynomial.eval x f = 0

/-- Rational points on the projective zero set of a homogeneous ideal, with
the source's primitive-coordinate height at most `B`. -/
def rationalProjectivePoints {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (B : ℝ) :
    Set (Projectivization ℚ (Fin (N + 1) → ℚ)) :=
  {x | (∀ f ∈ I, MvPolynomial.eval x.rep f = 0) ∧
    (primitiveRationalVectorHeight x.rep : ℝ) ≤ B}

/-! ## Exact polynomial hypotheses in Salberger 2023, Theorem 0.4 -/

/-- `h` is the rational top homogeneous part of the integral polynomial `f`,
and its degree is exactly `d`.  This avoids any ambiguity from the
`WithBot`-valued `totalDegree` of the zero polynomial. -/
def IsTopHomogeneousPart {N : ℕ}
    (f : MvPolynomial (Fin N) ℤ)
    (h : MvPolynomial (Fin N) ℚ) (d : ℕ) : Prop :=
  h = MvPolynomial.map (Int.castRingHom ℚ)
      (MvPolynomial.homogeneousComponent d f) ∧
    h ≠ 0 ∧
    ∀ k, d < k → MvPolynomial.homogeneousComponent k f = 0

/-- The exponent printed in Salberger 2023, Theorem 0.4. -/
def salberger2023AffineExponent (N d : ℕ) (ε : ℝ) : ℝ :=
  if d = 3 then (N : ℝ) - 3 + 2 / Real.sqrt 3 + ε
  else (N : ℝ) - 2 + ε

/-! ## Literal Hilbert--Samuel multiplicity at a special-fibre point -/

/-- Dehomogenization on the standard projective chart `X₀ = 1`. -/
def dehomogenizeAtZeroHom {N p : ℕ} [Fact p.Prime] :
    MvPolynomial (Fin (N + 1)) (ZMod p) →+*
      MvPolynomial (Fin N) (ZMod p) :=
  by
    let assignment : Fin (N + 1) → MvPolynomial (Fin N) (ZMod p) :=
      Fin.cases 1 fun i ↦ MvPolynomial.X i
    exact (MvPolynomial.aeval assignment).toRingHom

/-- The ideal of the standard affine chart `X₀ = 1`. -/
def standardAffineChartIdeal {N p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p))) :
    Ideal (MvPolynomial (Fin N) (ZMod p)) :=
  J.map dehomogenizeAtZeroHom

/-- Affine coordinates of a projective point with nonzero zeroth
coordinate.  The formula remains defined when that coordinate is zero, but
Corollary 3.7 separately assumes it is nonzero. -/
def standardAffineChartPoint {N p : ℕ} [Fact p.Prime]
    (P : Fin (N + 1) → ZMod p) : Fin N → ZMod p :=
  fun i ↦ (P 0)⁻¹ * P i.succ

/-- Evaluation at a displayed special-fibre tuple. -/
def specialFiberEvaluation {M p : ℕ} [Fact p.Prime]
    (P : Fin M → ZMod p) :
    MvPolynomial (Fin M) (ZMod p) →+* ZMod p :=
  MvPolynomial.eval₂Hom (RingHom.id (ZMod p)) P

/-- The displayed tuple belongs to the affine cone cut out by `J`. -/
def IsPointOnSpecialFiber {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) : Prop :=
  J ≤ RingHom.ker (specialFiberEvaluation P)

/-- Evaluation descended to the special-fibre coordinate ring. -/
def specialFiberQuotientEvaluation {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (hP : IsPointOnSpecialFiber J P) :
    (MvPolynomial (Fin M) (ZMod p) ⧸ J) →+* ZMod p :=
  Ideal.Quotient.lift J (specialFiberEvaluation P) hP

/-- The maximal ideal of the displayed rational point in the quotient
coordinate ring. -/
def specialFiberPointIdeal {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (hP : IsPointOnSpecialFiber J P) :
    Ideal (MvPolynomial (Fin M) (ZMod p) ⧸ J) :=
  RingHom.ker (specialFiberQuotientEvaluation J P hP)

/-- The inverse image in the polynomial ring of the `(k+1)`-st power of the
point ideal in the special-fibre coordinate ring.  Because `J` is contained
in the evaluation kernel, this is `J + ker(ev_P)^(k+1)`. -/
def specialFiberJetIdeal {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (k : ℕ) :
    Ideal (MvPolynomial (Fin M) (ZMod p)) :=
  J ⊔ RingHom.ker (specialFiberEvaluation P) ^ (k + 1)

/-- The `k`-th infinitesimal neighbourhood of the point, regarded as a
vector space over its displayed residue field. -/
abbrev specialFiberJetSpace {M p : ℕ} [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin M) (ZMod p)))
    (P : Fin M → ZMod p) (k : ℕ) :=
  MvPolynomial (Fin M) (ZMod p) ⧸ specialFiberJetIdeal J P k

/-- Hilbert--Samuel multiplicity `mu` at the displayed special-fibre point.

For a maximal ideal `m`, the finite-dimensional quotients `A/m^(k+1)` have
the same lengths as their localizations at `m`.  Thus their eventual Hilbert
polynomial gives the ordinary local Hilbert--Samuel multiplicity, without
introducing an abstract local-scheme interface. -/
def HasHilbertSamuelMultiplicityAt {N p : ℕ} (hp : p.Prime)
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p) (r mu : ℕ) : Prop := by
  letI : Fact p.Prime := ⟨hp⟩
  let J₀ := standardAffineChartIdeal J
  let P₀ := standardAffineChartPoint P
  exact ∃ hP : IsPointOnSpecialFiber J₀ P₀,
    (∀ k : ℕ, Module.Finite (ZMod p)
      (specialFiberJetSpace J₀ P₀ k)) ∧
    ∃ Q : Polynomial ℚ,
      Q.natDegree = r ∧
      Q.leadingCoeff = (mu : ℚ) / r.factorial ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank (ZMod p) (specialFiberJetSpace J₀ P₀ k) : ℚ) =
          Q.eval (k : ℚ)

/-- Coefficient extension from integers to rationals. -/
def intPolynomialToRat {N : ℕ} :
    MvPolynomial (Fin (N + 1)) ℤ →+*
      MvPolynomial (Fin (N + 1)) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

/-- The contracted integral homogeneous ideal defining the
scheme-theoretic closure in projective space over `ℤ`. -/
def projectiveIntegralClosureIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin (N + 1)) ℤ) :=
  I.comap intPolynomialToRat

/-- The special-fibre ideal obtained from the contracted integral model. -/
def projectiveSpecialFiberIdeal {N p : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) :
    Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)) :=
  (projectiveIntegralClosureIdeal I).map
    (MvPolynomial.map (Int.castRingHom (ZMod p)))

/-- The affine-chart tuple `(1,x₁,…,x_N)` specialises to the displayed
projective point.  The scalar is required to be a unit, exactly expressing
equality of projective points in the chart `x₀ ≠ 0`. -/
def SpecializesToProjectivePoint {N p : ℕ}
    (x : Fin (N + 1) → ℤ) (P : Fin (N + 1) → ZMod p) : Prop :=
  ∃ u : (ZMod p)ˣ, ∀ i, (x i : ZMod p) = (u : ZMod p) * P i

/-- Literal membership in Salberger's set
`S₁(X;B;P₁,…,P_t)`. -/
def InSalbergerSOne {N : ℕ} {index : Type*} [Fintype index]
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (B : ℝ)
    (prime : index → ℕ)
    (point : ∀ i, Fin (N + 1) → ZMod (prime i))
    (x : Fin (N + 1) → ℤ) : Prop :=
  x 0 = 1 ∧
    (∀ i, |(x i : ℝ)| ≤ B) ∧
    (∀ f ∈ I, MvPolynomial.eval (fun i ↦ (x i : ℚ)) f = 0) ∧
    ∀ j, SpecializesToProjectivePoint x (point j)

/-! ## Permitted external theorem statements -/

/-- **Pila 1995, Theorem A.**  The constant is chosen before the affine
ideal and before `H`; hence it is uniform in the coefficients of the
variety.  The displayed exponential factor is the one printed in the
source. -/
def Pila1995TheoremA : Prop :=
    ∀ (n d N : ℕ), 1 ≤ d → ∃ c : ℝ, 0 < c ∧
      ∀ (I : Ideal (MvPolynomial (Fin N) ℝ)),
        HasAffineHilbertDimensionDegree I n d →
        ∀ H : ℝ, 1 < H →
          ((pilaIntegralPoints I H).card : ℝ) ≤
            c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
              Real.exp
                (12 * Real.sqrt
                  ((d : ℝ) * Real.log H * Real.log (Real.log H)))

/-- **Salberger 2007, Corollary 3.7.**  The bound `K` is chosen using only
the ambient dimension, degree and epsilon.  Local multiplicities and the
several-prime product are exposed exactly; the output form is merely not in
the defining radical ideal, i.e. it does not vanish at the generic point in
the sense used by the source's determinant construction. -/
def Salberger2007Corollary37 : Prop :=
    ∀ (N d : ℕ) (ε : ℝ), 0 < ε →
      ∃ K : ℕ, ∀ (r : ℕ), 1 ≤ r →
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
          IsReducedEquidimensionalProjectiveScheme I r d →
          InfinityHyperplaneMeetsProperly I →
          ∀ (B : ℝ), 1 ≤ B →
            ∀ (index : Type) (_ : Fintype index),
              ∀ (prime : index → ℕ),
                ∀ (hprime : ∀ i, (prime i).Prime), Function.Injective prime →
                ∀ (mu : index → ℕ), (∀ i, 0 < mu i) →
                  ∀ (point : ∀ i, Fin (N + 1) → ZMod (prime i)),
                    (∀ i, point i 0 ≠ 0) →
                    (∀ i, HasHilbertSamuelMultiplicityAt (hprime i)
                      (projectiveSpecialFiberIdeal I) (point i) r (mu i)) →
                    B ^ (1 + ε) ≤
                      ∏ i, (prime i : ℝ) ^
                        (((d : ℝ) / (mu i : ℝ)) ^ ((r : ℝ)⁻¹)) →
                    ∃ (k : ℕ) (G : MvPolynomial (Fin (N + 1)) ℚ),
                      k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
                        ∀ x, InSalbergerSOne I B prime point x →
                          MvPolynomial.eval (fun i ↦ (x i : ℚ)) G = 0

/-- **Salberger 2023, Theorem 0.1.**  This is deliberately the non-uniform
theorem: the constant is chosen after the projective ideal `I` and may
depend on the variety, as well as on epsilon. -/
def Salberger2023Theorem01 : Prop :=
    ∀ (N r d : ℕ)
      (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
      IsIntegralProjectiveVariety I r d → 2 ≤ d →
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
          (rationalProjectivePoints I B).Finite ∧
          ((rationalProjectivePoints I B).ncard : ℝ) ≤
            C * B ^ ((r : ℝ) + ε)

/-- **Salberger 2023, Theorem 0.4, with the corrected hypothesis.**
The leading form is absolutely irreducible, as required by its proof and
explicitly corrected by Cluckers--Dèbes--Hendel--Nguyen--Vermeulen,
*Improvements on dimension growth results and effective Hilbert's
irreducibility theorem*, Forum Math. Sigma 13 (2025), e153, paragraph
preceding Proposition 3.2 (DOI 10.1017/fms.2025.10096).
One coefficient-uniform constant is
chosen before `f` and `B`.  The two printed degree ranges are represented by
the literal piecewise exponent `salberger2023AffineExponent`. -/
def Salberger2023Theorem04 : Prop :=
    ∀ (N d : ℕ), 3 ≤ N → (d = 3 ∨ 4 ≤ d) →
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ (f : MvPolynomial (Fin N) ℤ)
            (h : MvPolynomial (Fin N) ℚ),
            IsTopHomogeneousPart f h d → IsAbsolutelyIrreducible h →
            ∀ B : ℝ, 1 ≤ B →
              ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
                C * B ^ salberger2023AffineExponent N d ε

end

end Published
end TranslatedDepthSeven
