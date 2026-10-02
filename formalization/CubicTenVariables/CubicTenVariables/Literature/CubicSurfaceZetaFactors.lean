import CubicTenVariables.Literature.FiniteFieldPointCounts
import CubicTenVariables.ProjectiveFourierIdentity
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Concrete numerical zeta-factor input for cubic surfaces.

This proposition records a consequence of classical etale cohomology, and is
an explicit literature argument rather than a proved theorem or a global
axiom. Its conclusion concerns the actual projective zero points of the
coefficient extension of one polynomial, over every finite field extension.
The three finite complex families are fixed before the extension is chosen.
They record reciprocal roots with their positive integral multiplicities;
repeated values are permitted. No synthetic cohomology object is introduced.
Rationality of the individual signed determinant factors, or independence
from the cohomology prime, is not required or asserted.

Precise inputs for the numerical statement:

* Deligne, La conjecture de Weil I, Publ. Math. IHES 43 (1974), Sections
  1.3 and 1.5, especially (1.5.1) and (1.5.4), printed pp. 274--276:
  finiteness, vanishing above twice the dimension, the trace formula for
  every Frobenius iterate, and its determinant factorization. Properness
  identifies ordinary and compact-support cohomology.
  https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf
  For a textbook account of the same factorization for arbitrary, possibly
  singular varieties, see Milne, Lectures on etale cohomology, Theorem 29.8,
  printed p. 166. For the connected-component term use the constant-sheaf
  definition in Section 6, printed p. 46, and H^0 = global sections in
  Section 9, printed p. 64.
  https://www.jmilne.org/math/CourseNotes/LEC.pdf
* Poonen, Rational points on varieties, Corollary 7.5.21, printed p. 217
  (PDF p. 231; zero-based page 230), following Lemma 7.5.20: top
  compact-support cohomology is the component permutation space with its
  dimension twist. Geometric integrality gives the single top term q^(2m)
  and the single connected-component term 1.
  https://math.mit.edu/~poonen/papers/Qpoints.pdf
* Deligne, La conjecture de Weil II, Publ. Math. IHES 52 (1980),
  Corollary 3.3.4, printed p. 206 (zero-based PDF page 69), applied to the
  constant sheaf of weight zero: the roots in degrees one and two have
  complex norm at most sqrt(q) and q, respectively. The interface weakens
  the first bound to q, which suffices for amplification.
  https://publications.ias.edu/sites/default/files/Number40.pdf
* Katz, Sums of Betti numbers in arbitrary characteristic, Finite Fields
  Appl. 7 (2001), 29--44, Corollary of Theorem 3, second inequality,
  author PDF p. 4: the total Betti number of a projective scheme cut out
  by r degree-at-most-d equations in P^N is at most
  9 * 2^r * (3 + r*d)^(N+1). Here it is at most 23328. Removing the
  two dimension-one groups in degrees zero and four leaves 23326.
  https://web.math.princeton.edu/~nmk/BettiSum14.pdf

No bound on the degree-three roots is assumed. The subsequent amplification
argument must prove their norm bound from the internally proved potential
point-count estimate. The named literature proposition does not itself
assert that those subsequent steps, or the classical inputs above, have
been formalized.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.Literature

open MvPolynomial ProjectiveFourierIdentity

/-- Concrete zeta-factor bounds tied to all actual finite-extension counts.
The coefficient field is finite, the polynomial is homogeneous of degree
three and geometrically integral, and characteristics two and three are
excluded. The families may contain repeated roots; each entry contributes
with coefficient one and the displayed cohomological sign. -/
def CubicSurfaceZetaFactorBounds : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (F : MvPolynomial (Fin 4) K),
    F.IsHomogeneous 3 → (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    GeometricallyIntegralForm F →
    ∃ (n₁ n₂ n₃ : ℕ) (a : Fin n₁ → ℂ) (b : Fin n₂ → ℂ) (c : Fin n₃ → ℂ),
      n₁ + n₂ + n₃ ≤ 23326 ∧
      (∀ i, ‖a i‖ ≤ (Fintype.card K : ℝ)) ∧
      (∀ i, ‖b i‖ ≤ (Fintype.card K : ℝ)) ∧
      ∀ (L : Type) [Field L] [Fintype L] [Algebra K L] [FiniteDimensional K L],
        (Nat.card (zeroPoints (map (algebraMap K L) F)) : ℂ) =
          1 + (Fintype.card K : ℂ) ^ (2 * Module.finrank K L) -
            ∑ i, a i ^ Module.finrank K L +
            ∑ i, b i ^ Module.finrank K L -
            ∑ i, c i ^ Module.finrank K L

end CubicTenVariables.Literature
