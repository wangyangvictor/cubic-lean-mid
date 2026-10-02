import HessianTheorem11.AffineGeometry
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Explicit general finite-field upper-bound input, not an axiom declaration.

Reference: G. Lachaud and R. Rolland, "On the Number of Points of Algebraic
Sets over Finite Fields", J. Pure Appl. Algebra 219 (2015), 5117--5136;
https://arxiv.org/pdf/1405.3027, printed pp. 3--4, Theorems 1.1 and 2.1,
Corollary 2.2. Cumulative degree includes components of every dimension.
Their bounds imply the uniform statement below (one may take C = d^t).
Zero equations are discarded; a nonzero constant makes the locus empty.
The empty equation family gives affine space. Passing from the equation
ideal to its radical leaves Krull dimension and geometric zeros unchanged.
Thus no reducedness, irreducibility, nonemptiness, or equidimensionality
assumption is needed. The input is a corollary in polynomial coordinates,
and contains no incidence, cubic, trace, or exceptional-locus conclusion.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial

/-- Dimension of the actual equation quotient over the algebraic closure.
In particular, an empty geometric zero set has dimension bottom. -/
def geometricEquationDimension {n t : ℕ} {K : Type*} [Field K]
    (g : Fin t → MvPolynomial (Fin n) K) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
    Ideal.span (Set.range (fun i => map (algebraMap K (AlgebraicClosure K)) (g i))))

/-- The constant depends only on the ambient dimension, number of equations,
and degree bound, and precedes the field, coefficients and dimension bound.
This proposition is an explicit unproved standard-literature premise. -/
def BoundedDegreeAffinePointCount : Prop :=
  ∀ (n t d : ℕ), 1 ≤ d → ∃ C : ℕ, 1 ≤ C ∧
    ∀ (K : Type) [Field K] [Fintype K] (g : Fin t → MvPolynomial (Fin n) K),
      (∀ i, (g i).totalDegree ≤ d) → ∀ j : ℕ,
      geometricEquationDimension g ≤ (j : WithBot ℕ∞) →
      Nat.card {x : Fin n → K // ∀ i, eval x (g i) = 0} ≤ C * (Fintype.card K)^j

end CubicTenVariables.Literature
