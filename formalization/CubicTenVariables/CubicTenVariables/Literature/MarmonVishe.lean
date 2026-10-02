import CubicTenVariables.ExponentialSums
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit Marmon--Vishe delta-method input

Reference: O. Marmon and P. Vishe, *On the Hasse principle for quartic
hypersurfaces*, arXiv:1712.07594v2 (24 April 2019), Proposition 1.2,
printed p. 3, with the kernel construction in Lemma 2.2, pp. 4--5.
https://arxiv.org/pdf/1712.07594v2
This edition is pinned because the proposition numbering differs from the
published paper cited by the manuscript.

Only the general integer delta identity is an input. The input has no
polynomial, dimension, rational-solubility, counting-asymptotic, or error-term
estimate for a cubic counting function. It is a proposition passed explicitly
to theorems, with no global axiom or supplied inhabitant.

We use natural Q >= 2 and positive integral decay orders, a restriction of
the cited result. The kernel is selected before every integer phase, truncation
parameter and decay order. The implied constants are explicit and uniform in
Q, q, and the integer phase. The integration domain is an open interval;
no compact-support assertion about the smooth kernel itself is imposed.
The source Q = 1 case is supplied by the checked zero-kernel extension in
`DeltaMethod`, not by strengthening this literature input.
-/

noncomputable section
namespace CubicTenVariables
namespace DeltaMethod
open MeasureTheory
open scoped BigOperators ContDiff

/-- The actual positive-sign additive exponential on the real line. -/
def realExponential (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- The integer Kronecker delta, with its values embedded in C. -/
def integerDelta (m : ℤ) : ℂ := if m = 0 then 1 else 0

/-- The exact truncation interval in Marmon--Vishe's proposition. -/
def arc (Q q : ℕ) (η : ℝ) : Set ℝ :=
  {θ | |θ| < ((q : ℝ) * (Q : ℝ)) ^ (-1 + η)}

/-- Integral over one actual major-arc window, with integer phase m. -/
def deltaArc (p : ℕ → ℕ → ℝ → ℂ) (Q q a : ℕ) (η : ℝ) (m : ℤ) : ℂ :=
  ∫ θ in arc Q q η, p Q q θ * realExponential (((a : ℝ) / (q : ℝ) + θ) * (m : ℝ))

/-- The numerator representatives are exactly 1,...,q, as in the cited
proposition; both sums are finite, and q=0 is never included. -/
def deltaApproximation (p : ℕ → ℕ → ℝ → ℂ) (Q : ℕ) (η : ℝ) (m : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ Finset.Icc 1 q,
    if Nat.Coprime a q then deltaArc p Q q a η m else 0

/-- All constants precede the varying Q, q, phase and arc coordinate.
Smoothness concerns the entire real line, and all integrals use ordinary
Lebesgue measure. Positive integral N suffices for arbitrary polynomial
error savings in the application. -/
structure KernelEstimates (Qmin : ℕ) (p : ℕ → ℕ → ℝ → ℂ) : Prop where
  smooth : ∀ Q, Qmin ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ContDiff ℝ ∞ (p Q q)
  bounded : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q, Qmin ≤ Q → ∀ q, 1 ≤ q → q ≤ Q →
    ∀ θ, ‖p Q q θ‖ ≤ C
  near_one : ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q, Qmin ≤ Q → ∀ q, 1 ≤ q → q ≤ Q → ∀ θ,
      |θ| ≤ (Q : ℝ) ^ (-(2 : ℝ)) →
      ‖p Q q θ - 1‖ ≤ C * ((q : ℝ) / (Q : ℝ)) ^ N
  delta : ∀ η : ℝ, 0 < η → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 1 ≤ C ∧
    ∀ Q, Qmin ≤ Q → ∀ m : ℤ,
      ‖integerDelta m - deltaApproximation p Q η m‖ ≤
        C * (Q : ℝ) ^ (-(N : ℝ) * η)

end DeltaMethod
namespace Literature

/-- Marmon--Vishe, arXiv:1712.07594v2, Proposition 1.2, in the restricted
natural-Q, integral-order form documented above. This is an explicit,
uninhabited-in-this-module literature premise, not a Lean axiom. -/
def MarmonVishe2019Proposition12 : Prop :=
  ∃ p : ℕ → ℕ → ℝ → ℂ, DeltaMethod.KernelEstimates 2 p

end Literature
end CubicTenVariables
