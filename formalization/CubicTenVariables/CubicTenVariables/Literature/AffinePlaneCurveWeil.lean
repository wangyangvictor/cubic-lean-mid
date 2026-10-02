import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
A degree-uniform Weil bound for actual affine plane curves. This is an
explicit proposition passed to applications: no inhabitant or axiom is declared.

Primary reference: Y. Aubry and M. Perret, "A Weil theorem for singular
curves", in Arithmetic, Geometry and Coding Theory (Luminy, 1993),
de Gruyter, Berlin, 1996, Corollary 2.5, p. 5. For an absolutely
irreducible projective plane curve of degree e, including singular curves,
that corollary gives

  |#C(F_q) - (q+1)| <= (e-1)(e-2) sqrt(q).

Corollary 2.4, p. 4, also states the point-count formula over every extension
F_(q^a). Author's copy:
https://www.math.univ-toulouse.fr/~perret/Fichiers/Scan-Weil.Singulier.pdf
Publication DOI: https://doi.org/10.1515/9783110811056.1

The displayed affine corollary follows by taking the projective closure
of the actual affine curve. Its intersection with the line at infinity
has at most e geometric points, by the elementary homogeneous binary
polynomial root bound. Thus the affine error is bounded by the projective
error plus e+1. Since q >= 2 and 1 <= e <= d, this is at most C(d)*sqrt(q);
squaring and enlarging the constant gives the interface below. No
smoothness, characteristic exclusion, rational-point assumption or fixed
prime-field restriction is needed.

The positive-degree condition and the domain quotient after extension to
an algebraic closure express geometric integrality of the actual plane
hypersurface, rather than an abstract point-count hypothesis. The bound
contains no cubic-family, exceptional-parameter, second-moment or sheaf
assumption. Its constant precedes both the finite field and its equation.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial

/-- The generic degree-uniform affine plane-curve Weil estimate, in squared
form convenient for finite second moments. All finite fields and all their
finite extensions are included in the quantification. -/
def AffinePlaneCurveWeil : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ B : ℝ, 1 ≤ B ∧
    ∀ (K : Type) [Field K] [Fintype K] (f : MvPolynomial (Fin 2) K),
      1 ≤ f.totalDegree → f.totalDegree ≤ d →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) f}) →
      ((Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
        (Fintype.card K : ℝ))^2 ≤ B*(Fintype.card K : ℝ)

/-- The smaller estimate actually needed by the ten-variable theorem.
Its binary slices have degree exactly three, and the finitely many excluded
primes may include two and three. The constant is still uniform in the field
and the equation. This is a proposition, not an asserted theorem. -/
def AffinePlaneCubicWeil : Prop :=
  ∃ B : ℝ, 1 ≤ B ∧
    ∀ (K : Type) [Field K] [Fintype K] (f : MvPolynomial (Fin 2) K),
      (2 : K) ≠ 0 → (3 : K) ≠ 0 → f.totalDegree = 3 →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K)) f}) →
      ((Nat.card {x : Fin 2 → K // eval x f = 0} : ℝ) -
        (Fintype.card K : ℝ))^2 ≤ B*(Fintype.card K : ℝ)

/-- Compatibility with the previous, stronger all-degree literature input. -/
theorem AffinePlaneCurveWeil.cubic (h : AffinePlaneCurveWeil) :
    AffinePlaneCubicWeil := by
  obtain ⟨B, hB, hbound⟩ := h 3 (by decide)
  refine ⟨B, hB, ?_⟩
  intro K _ _ f _ _ hd hgeo
  exact hbound K f (by omega) (by omega) hgeo

end CubicTenVariables.Literature
