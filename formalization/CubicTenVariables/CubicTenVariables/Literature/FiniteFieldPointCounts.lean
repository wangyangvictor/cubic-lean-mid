import CubicTenVariables.ReducedCubicVertex
import CubicTenVariables.ReducedGaussSection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Two explicit, general finite-field point-count inputs. These are propositions
passed to applications; no inhabitant or global axiom is declared here.

* Hooley--Katz: C. Hooley, "On the number of points on a complete intersection
  over a finite field", J. Number Theory 38 (1991), 338--358, Theorem 1,
  with Katz's appendix; https://doi.org/10.1016/0022-314X(91)90023-5.
  The precise uniform version used here was verified in S. R. Ghorpade and
  G. Lachaud, "Etale cohomology, Lefschetz theorems and number of points of
  singular varieties over finite fields", corrected author version
  https://arxiv.org/pdf/0808.2169, Theorem 6.1, pp. 17--19. For an integral
  hypersurface in projective N-space of degree d and singular dimension at
  most s, it bounds the error from pi_(N-1)(q) by
  b'_(N-s-2)(N-s-1,d) q^((N+s)/2) + C_s q^((N+s-1)/2),
  with C_s <= 18*(d+3)^(N+1). Thus the constant is uniform in the finite
  field and the hypersurface. Theorem 6.1 has no resolution-of-singularities
  assumption; the later, stronger assertions in section 7 are not used.

* T. D. Browning, "The Lang--Weil estimate for cubic hypersurfaces",
  Canad. Math. Bull. 56 (2013), 500--502, main theorem on p. 501;
  https://doi.org/10.4153/CMB-2011-177-4. For a geometrically integral
  nonconical cubic in projective N-space, N >= 3, the error from q^(N-1)
  is at most C(N)*q^(N-2), uniformly in the field and cubic. Replacing
  q^(N-1) by pi_(N-1)(q) preserves this bound after enlarging C(N).
  The restriction away from characteristics 2 and 3 below is sufficient
  for our applications and permits the literal translation/Hessian test.

Both inputs are stated in equivalent affine-cone coordinates. If P is the
projective point count, its affine cone has 1+(q-1)*P points, while
1+(q-1)*pi_(n-2)(q)=q^(n-1). This explains the exact factor q-1 and all
exponents below. The singular-cone dimension is the dimension of its actual
geometric coordinate ring. The standard homogeneous-cone dimension relation
converts its bound s+1 into projective singular dimension at most s.
Only nonnegative upper bounds s are encoded; s=4 is sufficient in the
ten-variable application. There is no exponential-sum, anisotropy, selected
dimension, or supplied local-estimate premise in either interface.
-/

set_option autoImplicit false

noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11

/-- All actual affine zeros, including the origin, with no choice of
integer representatives or projective normalization. -/
def affineZeroCount {n : ℕ} {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin n) K) : ℕ :=
  Nat.card {x : Fin n → K // eval x F = 0}

theorem affineZeroCount_eq_filter_card {n : ℕ} {K : Type*}
    [CommRing K] [Fintype K] [DecidableEq K] (F : MvPolynomial (Fin n) K) :
    affineZeroCount F = (Finset.univ.filter fun x : Fin n → K => eval x F = 0).card := by
  classical
  simp only [affineZeroCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The original polynomial is nonzero, and its actual affine hypersurface
coordinate ring is a domain after extension to an algebraic closure. In the
positive homogeneous degrees below this says geometrically integral. -/
def GeometricallyIntegralForm {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) : Prop :=
  F ≠ 0 ∧ IsDomain (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
    Ideal.span {map (algebraMap K (AlgebraicClosure K)) F})

/-- The literal geometric singular cone. Keeping F=0 makes this correct
also in characteristics dividing the homogeneous degree. -/
def geometricSingularCone {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) : Set (Fin n → AlgebraicClosure K) :=
  {x | eval x (map (algebraMap K (AlgebraicClosure K)) F) = 0 ∧
    ∀ i, eval x (pderiv i (map (algebraMap K (AlgebraicClosure K)) F)) = 0}

/-- There is no nonzero geometric translation direction. The quantification
is over the algebraic closure, not only the finite field's rational points. -/
def GeometricallyNonconicalCubic {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ v : Fin n → AlgebraicClosure K,
    ReducedCubicVertex.TranslationDirection
      (map (algebraMap K (AlgebraicClosure K)) F) v → v = 0

/-- The nonconicality premise has an equivalent literal Hessian-kernel
test, proved here rather than supplied as another literature input. -/
theorem geometricallyNonconicalCubic_iff_hessian {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    GeometricallyNonconicalCubic F ↔
      ∀ v : Fin n → AlgebraicClosure K,
        hessian (map (algebraMap K (AlgebraicClosure K)) F) v = 0 → v = 0 := by
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr h2
  have h3' : (3 : AlgebraicClosure K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr h3
  constructor
  · intro h v hv
    exact h v (ReducedCubicVertex.translation_of_hessian_zero _ (hF.map _) h2' h3' v hv)
  · intro h v hv
    exact h v (ReducedCubicVertex.hessian_zero_of_translation _ (hF.map _) h2' v hv)

/-- The uniform Hooley--Katz bound, in literal affine-cone coordinates.
n counts variables, so the projective ambient dimension is n-1. The natural
number s is a nonnegative upper bound for projective singular dimension.
The one constant is chosen before every finite field and polynomial. -/
def HooleyKatzPointCount : Prop :=
  ∀ (n d s : ℕ), 0 < d → s + 3 ≤ n →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin n) K),
      F.IsHomogeneous d → GeometricallyIntegralForm F →
      ReducedGaussSection.coordinateDimension (geometricSingularCone F) ≤
        ((s+1 : ℕ) : WithBot ℕ∞) →
      |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (n-1)| ≤
        C * ((Fintype.card K : ℝ)-1) *
          (Fintype.card K : ℝ) ^ (((n : ℝ)-1+(s : ℝ))/2)

/-- Browning's nonconical cubic bound, in literal affine-cone coordinates.
It is deliberately restricted to the characteristics used by the application.
The constant depends on the number of variables, not on the finite field,
its characteristic, its cardinality, or the coefficients of the cubic. -/
def BrowningCubicPointCount : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin n) K),
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → F.IsHomogeneous 3 →
      GeometricallyIntegralForm F → GeometricallyNonconicalCubic F →
      |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (n-1)| ≤
        C * ((Fintype.card K : ℝ)-1) *
          (Fintype.card K : ℝ) ^ ((n : ℝ)-3)

end CubicTenVariables.Literature
