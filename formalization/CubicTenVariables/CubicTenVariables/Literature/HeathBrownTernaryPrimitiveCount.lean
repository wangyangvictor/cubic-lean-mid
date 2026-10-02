import TranslatedDepthSeven.AbsoluteIrreducibility
import TranslatedDepthSeven.IntegerBoxCount
import TranslatedDepthSeven.PrimitiveRationalVectorHeight

/-!
# Fixed ternary primitive-point counting input

Primary reference: D. R. Heath-Brown, *The density of rational points on
curves and surfaces*, Annals of Mathematics 155 (2002), 553–598 (including
the appendix), Theorem 3, equation (1.9), printed p. 555:
https://arxiv.org/pdf/math/0405392v1
Publisher record: https://doi.org/10.2307/3062125

That theorem gives `N(F;B) ≪_{d,η} B^(2/d+η)` for an integral homogeneous
ternary form irreducible over Q. No smoothness is required for (1.9), and
the constant is independent of the coefficients. The count on printed
p. 553 chooses primitive integer representatives with first nonzero
coordinate positive. Counting both signs changes the constant by two.
Browning–Heath-Brown–Salberger, *Counting rational points on algebraic
varieties*, Duke Math. J. 132 (2006), 545–578, Lemma 4, restates its
projective plane-curve consequence; arXiv:math/0410117v4, Section 2.

The proposition below deliberately asks for less: degree at least two,
absolute irreducibility, one fixed form before its constant, only integer
cutoffs R >= 1, and exponent `1+η`. The published bound implies this
because `2/d <= 1`. No coefficient-content normalization is required.
The polynomial zero, gcd-one condition, and closed integer box are literal.
This is an explicit input proposition, not an axiom or an asserted theorem.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.Literature

open MvPolynomial TranslatedDepthSeven TranslatedDepthSeven.Published

/-- All primitive integer zeros, with both signs, in the closed cube. -/
def primitiveTernaryZeros (k : MvPolynomial (Fin 3) ℤ) (R : ℕ) :
    Finset (Fin 3 → ℤ) := by
  classical
  exact (integerSupNormBox 3 R).filter
    (fun z ↦ IsPrimitiveIntVector z ∧ eval z k = 0)

/-- Fixed-form, integer-cutoff consequence of Heath-Brown 2002,
Theorem 3 (1.9). The constant depends on the fixed k and η, and precedes
every height cutoff. -/
def HeathBrown2002FixedTernaryPrimitiveCount : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (k : MvPolynomial (Fin 3) ℤ),
    k.IsHomogeneous d → IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k) →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ R : ℕ, 1 ≤ R →
        ((primitiveTernaryZeros k R).card : ℝ) ≤ C * (R : ℝ) ^ (1 + η)

end CubicTenVariables.Literature
