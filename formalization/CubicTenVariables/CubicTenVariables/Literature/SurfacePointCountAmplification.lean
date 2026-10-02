import CubicTenVariables.Literature.FiniteFieldPointCounts
import CubicTenVariables.ProjectiveFourierIdentity
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
An explicit numerical literature premise for geometrically integral cubic
surfaces: potential square-root cancellation implies an absolute uniform
bound over the original finite field. This file defines a proposition to
be passed as an argument. It contains no axiom and does not formalize the
étale-cohomology realization or assert that the literature input is proved.

The narrower surface statement follows from this precise classical chain:
* Deligne, La conjecture de Weil I, §§1.3 and 1.5, especially (1.5.1),
  pp.274–275: finite-dimensional compact-support cohomology, vanishing above
  twice the dimension, and the geometric-Frobenius trace formula.
  https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf
* Poonen, Rational points on varieties, Corollary7.5.21, p.217 (PDFp.231):
  top compact-support cohomology, with the dimension twist, is the component
  permutation representation. For a proper geometrically integral surface,
  H^0=Q_l and H^4=Q_l(-2).
  https://math.mit.edu/~poonen/papers/Qpoints.pdf
* Deligne, La conjecture de Weil II, Theorem3.3.1 (also introductory
  Theorem1, p.138): weights of H_c^i with constant coefficients are at most i.
  https://publications.ias.edu/sites/default/files/Number40.pdf
* Katz, Sums of Betti numbers in arbitrary characteristic, Corollary of
  Theorem3, second inequality (author PDFp.4): for r equations of degree
  at most d in P^N, total Betti <= 9*2^r*(3+r*d)^(N+1). For a cubic surface
  this is 9*2*6^4=23328.
  https://web.math.princeton.edu/~nmk/BettiSum14.pdf

Indeed E_m=#X(F_(q^m))-(1+q^m+q^(2m)) has every root of modulus >q in H^3,
with the same negative sign. A bound over all extensions of one finite
extension excludes these roots by same-sign power-sum amplification; raising
roots to the extension degree cannot cancel positive multiplicities. Then
|E_m| <= (b1+b2+b3+1)*q^m <= totalBetti*q^m. Neither Frobenius semisimplicity,
isolated singularities, high-degree complete-intersection comparison, nor
Wang Proposition2.16 is used. Compare Wang, arXiv2202.10427v3, Lemma2.15 p.7
and the proof of Proposition2.7 pp.7–8: https://arxiv.org/pdf/2202.10427v3 .

All objects in the interface below are actual finite fields, literal
coefficient extensions, quotient projective points, and their cardinalities.
The finite intermediate field and every further field embedding are explicit.
No artificial trace arrays or unimplemented cohomology groups are substituted.
-/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial ProjectiveFourierIdentity

/-- A surface-only classical amplification input. The constant 23328 is
fixed before the field and cubic; the potential-goodness constant and finite
extension may depend on both. The exclusions 2,3 retain the intended scope
of the singular-point projection application. -/
def CubicSurfacePointCountAmplification : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (F : MvPolynomial (Fin 4) K),
    F.IsHomogeneous 3 → (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    GeometricallyIntegralForm F →
    (∃ C : ℝ, 0 ≤ C ∧
      ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ Finite E ∧
        ∀ (L : Type) [Field L] [Fintype L] (τ : E →+* L),
          |(Nat.card (zeroPoints (map (τ.comp (algebraMap K E)) F)) : ℝ) -
            ((Fintype.card L : ℝ)^2 + (Fintype.card L : ℝ) + 1)| ≤
              C * (Fintype.card L : ℝ)) →
    |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        23328 * (Fintype.card K : ℝ)

end CubicTenVariables.Literature
