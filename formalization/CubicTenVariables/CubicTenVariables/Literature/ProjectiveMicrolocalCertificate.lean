import CubicTenVariables.BihomogeneousIncidenceFamily
import CubicTenVariables.IntegralGeometricFiberDepth
import CubicTenVariables.FiniteConormalDepth
import CubicTenVariables.ProjectiveGysinTraceBound

/-!
An explicit UNPROVED generic derived literature corollary. No inhabitant or
global axiom is declared. This is not a verbatim numbered theorem of one
source, and none of the data below are claimed to be internally constructed
singular supports, cohomology groups, Frobenius operators or Gysin morphisms.

The same finite integral polynomial family witnesses BOTH the geometric and
trace fields. Independent existence statements would not suffice: arbitrary
conormal incidence satisfying the displayed containments need not control
Gysin cancellation. There is no opaque predicate called singular support.

Primary sources and the derivation intended for this boundary:

* Beilinson, Constructible sheaves are holonomic, arXiv:1505.06768v8,
  Section 1.3: existence/pure dimension; characteristic-zero Lagrangian
  remark and following conormal exercise (printed pp.3-4); Section 1.6.2:
  contact/Legendre identifications (p.5); Section 4.1: ordinary conormal
  inclusion. https://arxiv.org/pdf/1505.06768
  Apply to the unshifted constant F_ell sheaf on the projective hypersurface,
  pushed into projective (n-1)-space. Its projectivized singular support has
  dimension n-2. Its two-block affine cone, with the factors exchanged, has
  dimension n and is conormal over a nonempty open of every image base in
  characteristic zero. Adjoin the full x=0 axis. This is another dimension-n
  conormal component and changes no positive fiber depth. The restriction
  degree>=2 is intentional: only then do all first derivatives vanish at0,
  so this extra axis obeys the gradient-minor containment.
* Hu--Yang, Relative singular support and the semi-continuity of
  characteristic cycles, arXiv:1702.06752v1, Theorems 5.8-5.9, pp.20-21:
  https://arxiv.org/pdf/1702.06752
  The smooth ambient projective space over Spec Z[1/ell] satisfies their
  excellent-Noetherian-base hypotheses. One localization gives the common
  reduced-support model. Finite bihomogeneous equations and integral
  coefficients use Noetherian algebra and clearing denominators. Enlarge
  the excluded integer for their chosen equations and the support
  containments. No exact specialization of later depth-locus equations is
  asserted here, and positive-characteristic supports are not called
  conormal.
* Raskin--Smith, Exceptional loci in Lefschetz theory, arXiv:2106.10332v1,
  Theorem 1.2 and its Galois-equivariance remark; Section 2.1; Theorem 2.2
  and Corollary 2.3: https://arxiv.org/html/2106.10332v1
  Their actual incidence in the proof is PSS. For a closed hypersurface
  immersion, r=n-2; a projective incidence fiber has dimension e-1 when its
  affine cone has positive dimension e. Choosing c=e+1 gives Gysin
  isomorphisms in every degree k>n-1+e and surjectivity at equality.
* COEFFICIENT COMPATIBILITY IS PART OF THIS DERIVED BOUNDARY: the canonical
  integral purity/counit Gysin map must have derived mod-ell reduction
  equal to the finite-coefficient map of Raskin--Smith Section 2.1. For its
  cone, finite generation, the coefficient exact sequence and Nakayama
  lift the finite-coefficient vanishing; rationalization gives the adic
  isomorphisms. Milne, Lectures on Etale Cohomology v2.21, Theorem 19.2,
  p.125, gives finite generation and the coefficient sequence:
  https://www.jmilne.org/math/CourseNotes/LEC.pdf
  Laszlo--Olsson, Six operations II, author version, Lemma 8.1, pp.23-24,
  gives derived coefficient reduction for Rf_*:
  https://www.cmls.polytechnique.fr/perso/laszlo/articleweb/article-IIfin.pdf
  Neither is cited as a verbatim theorem about this particular Gysin cone;
  compatibility of that canonical map remains explicitly included here.
* Grothendieck--Lefschetz trace formula, SGA4 1/2, Rapport, Theorem 3.2;
  Deligne, Weil II, Theorem 3.3.1, supplies the constant-coefficient weights:
  https://www.numdam.org/item/PMIHES_1980__52__137_0.pdf
  Proper constructibility/base change and bounded cohomological dimension
  give one total rank bound for the fixed universal hyperplane family:
  Stacks Theorem63.14.5 (0GL0), Lemma59.92.3 (0F0C), Lemma63.10.2 (0G2A).
  https://stacks.math.columbia.edu/tag/0GL0
  https://stacks.math.columbia.edu/tag/0F0C
  https://stacks.math.columbia.edu/tag/0G2A
  Adic ranks are bounded by the dimensions with fixed mod-ell coefficients.

The trace arrays use generous ranges and zero padding: a hyperplane may
contain a component of a reducible hypersurface. Nilpotents do not change
the projective point counts. No smoothness, irreducibility, cubic degree or
anisotropy assumption is imposed on F. There is no bound on complexity as
F varies, no depth codimension, rational-locus gain, pointwise Fourier bound
or complete-sum estimate in this proposition. Actual numerical bounds must
be derived separately from the trace and cancellation fields.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ProjectiveMicrolocalData

open MvPolynomial HessianTheorem11
open TerminalFiberCoordinates FiniteIncidenceDepth
open BihomogeneousIncidenceFamily
open ProjectiveFourierIdentity ProjectiveGysinTraceBound
open scoped BigOperators

/-- The literal gradient, before any restriction to a nonsingular locus. -/
def gradient {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [CommRing K] (x : Fin n → K) : Fin n → K :=
  fun i => eval₂ (Int.castRingHom K) x (pderiv i F)

/-- Nonzero affine representatives of the actual projective Gauss graph.
The left block is the frequency and the right block the hypersurface point.
The gradient uses the supplied equation, including for repeated factors. -/
def gaussGraph {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] : Set ((Fin n ⊕ Fin n) → K) :=
  {z | (fun i => z (.inr i)) ≠ 0 ∧
    eval₂ (Int.castRingHom K) (fun i => z (.inr i)) F = 0 ∧
    gradient F K (fun i => z (.inr i)) ≠ 0 ∧
    ∃ a : K, a ≠ 0 ∧ (fun i => z (.inl i)) = a • gradient F K (fun i => z (.inr i))}

/-- Algebraic closure is taken in BOTH blocks before taking a fiber. The
fiber of the closed graph can be larger than closure of an ordinary fiber. -/
def gaussGraphClosure {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] : Set ((Fin n ⊕ Fin n) → K) :=
  zeroLocus K (vanishingIdeal K (gaussGraph F K))

/-- The actual fiber of the closed Gauss graph. Over an algebraically
closed field, for nonzero v this is the affine cone over its projective
graph fiber, with the zero-point convention supplied by the affine closure. -/
def gaussFiberClosure {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] (v : Fin n → K) : Set (Fin n → K) :=
  {x | Sum.elim v x ∈ gaussGraphClosure F K}

/-- Polynomial containments and actual Gauss-fiber closure inclusion. -/
structure IncidenceAndGauss {n t : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (f : Fin t → Polynomial n n) (K : Type*) [Field K] : Prop where
  incidence : ∀ (v x : Fin n → K), x ∈ fiber f K v →
    eval₂ (Int.castRingHom K) x F = 0 ∧ dotProduct v x = 0 ∧
      ∀ i j, v i * gradient F K x j - v j * gradient F K x i = 0
  gauss : ∀ v : Fin n → K, gaussFiberClosure F K v ⊆ fiber f K v

/-- Characteristic-zero geometry of the very same integral equations later
used in finite characteristic. Geometric components need not descend
individually to Q. The conormal field only asks for the inclusion needed
by the already proved finite-conormal depth argument. -/
structure Geometry {n t : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (f : Fin t → Polynomial n n) : Prop where
  bihomogeneous : ∃ (dx dv : Fin t → ℕ),
    (∀ i, 0 < dx i) ∧ (∀ i, (f i).IsHomogeneous (dx i)) ∧
      ∀ i s, (coeff s (f i)).IsHomogeneous (dv i)
  conormalCover : ∃ (c : ℕ) (Y : Fin c → Set (GeometricPoint (n+n)))
      (O : Fin c → Set (GeometricPoint n)),
    geometricIncidence f = ⋃ i, Y i ∧
    (∀ i, AlgebraicallyClosedSet (Y i)) ∧
    (∀ i, GeometricallyIrreducible (Y i)) ∧
    (∀ i, affineDimension (Y i) = (n : Dimension)) ∧
    (∀ i, RelativelyOpenSet (FiniteConormalDepth.base (Y i)) (O i)) ∧
    (∀ i, (O i).Nonempty) ∧
    ∀ i v, v ∈ O i →
      (coordinatePairing.orthogonal (affineTangentSpace (FiniteConormalDepth.base (Y i)) v) :
        Set (GeometricPoint n)) ⊆ pointFiber (Y i) v
  incidenceAndGauss : IncidenceAndGauss F f GeometricField

/-- Finite complex trace and natural rank arrays. Both point-count
identities refer to the actual quotient-projective point types. Nothing
here identifies these arrays with internally constructed cohomology. -/
def TraceData {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (K : Type*) [Field K] [Fintype K] (v : Fin n → K) (e B : ℕ) : Prop :=
  ∃ (tX tH : ℕ → ℂ) (bX bH : ℕ → ℕ),
    (Nat.card (zeroPoints (map (Int.castRingHom K) F)) : ℂ) =
      alternatingSum tX (2*n+3) ∧
    (Nat.card (sectionPoints (map (Int.castRingHom K) F) v) : ℂ) =
      alternatingSum tH (2*n+1) ∧
    (∀ k, ‖tX k‖ ≤ (bX k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2)) ∧
    (∀ k, ‖tH k‖ ≤ (bH k : ℝ) * (Fintype.card K : ℝ)^((k : ℝ)/2)) ∧
    (∑ k ∈ Finset.range (2*n+3), bX k) ≤ B ∧
    (∑ k ∈ Finset.range (2*n+1), bH k) ≤ B ∧
    ∀ k ∈ Finset.range (2*n+3), n-1+e < k →
      tX k = (Fintype.card K : ℂ) * tH (k-2)

/-- One prime exclusion and one rank bound, selected before every prime,
finite field and frequency. The threshold is tied to the actual geometric
fiber of f, not an arbitrary supplied numerical depth. -/
structure GoodReduction {n t : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (f : Fin t → Polynomial n n) (N B : ℕ) : Prop where
  incidenceAndGauss : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (K : Type) [Field K] [CharP K p], IncidenceAndGauss F f K
  trace : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ (K : Type) [Field K] [Fintype K] [CharP K p] (v : Fin n → K), v ≠ 0 →
      ∀ e : ℕ, IntegralGeometricFiberDepth.geometricFiberDimension f K v ≤ (e : Dimension) →
        TraceData F K v e B

end CubicTenVariables.ProjectiveMicrolocalData

namespace CubicTenVariables.Literature

/-- The joint, explicitly unproved generic literature corollary. The
geometry and all finite-field traces share the same finite integral
incidence equations. There is no cubic, anisotropy or desired estimate
among the hypotheses or conclusions. -/
def ProjectiveMicrolocalCertificate : Prop :=
  ∀ (n d : ℕ), 3 ≤ n → 2 ≤ d →
    ∀ (F : MvPolynomial (Fin n) ℤ), F ≠ 0 → F.IsHomogeneous d →
      ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n) (N B : ℕ),
        1 ≤ N ∧ 1 ≤ B ∧ ProjectiveMicrolocalData.Geometry F f ∧
          ProjectiveMicrolocalData.GoodReduction F f N B

end CubicTenVariables.Literature
