import CubicTenVariables.PolynomialExponentialFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
An explicit UNPROVED generic arithmetic corollary of the following literature.
It is a proposition passed as an argument, with no axiom or inhabitant declared.
It is not claimed to be a verbatim numbered theorem of any one source.

* Fouvry--Katz, A general stratification theorem for exponential sums, J. reine
  angew. Math. 540 (2001), 115--166, Theorem 2.1, printed p.121:
  https://web.math.princeton.edu/~nmk/katzFouvry.pdf
  Apply it to the family already restricted to Spec(Z[y]/(G)), not by an
  unjustified closed base change of a stratification of the ambient space.
  It supplies fixed integral strata with smooth equidimensional fibers and
  simultaneous adaptation and bounded total rank of the fieldwise complexes.
  The rank inequality in the printed theorem omits a factor C. This typo is
  explicitly corrected in Bonolis--Kowalski--Woo, Stratification theorems for
  exponential sums in families, author version 21 May 2026, Remark 5.2(1),
  printed p.28: https://people.math.ethz.ch/~kowalski/stratification.pdf
  Their Section 5.3 and Remark 5.2(2) also explain the fieldwise complexes.
* Grothendieck--Lefschetz trace formula, SGA 4 1/2, Rapport, Theorem 3.2
  (adic form; Theorem 4.10 is the finite-coefficient version), and Deligne,
  La conjecture de Weil II, Theorem 3.3.1: the compactly supported direct
  image of the rank-one Artin--Schreier system gives these literal sums and
  is mixed of integer weights. The Artin--Schreier system is constructed
  separately in each characteristic, not over characteristic zero.
* Xu, Stratification for multiplicative character sums, IMRN 2020(10),
  2881--2917, Theorem 3.5 and Remark 3.6; Section 3.3 gives the mixed virtual
  trace-function extension (arXiv:1709.01663, v1, printed pp.19--22).
  This is a general theorem on such trace functions despite the title.
* Stacks Project, Lemma 37.27.5, Tag 0559 (geometric irreducibility spreads).
  Together with the smooth equidimensional strata and a principal-open
  shrinking, this gives geometrically integral good fibers of dimension d.

Derivation of this interface: choose a dense smooth adapted stratum of the
geometrically integral rational base, intersect it with D(h), and choose an
integral principal open D(g) inside it, taking h as a factor of g. Remove
finitely many bad primes. The total rank is bounded by one fixed integer C.
For each prime and character, Xu's integer-weight alternative gives either
the weight-w pointwise bound on every finite extension or an extended limsup
at least one after division by q^(d+w+1). The latter implies the frequent
lower bound 1/2 encoded below. We deliberately do not use real-valued limsup,
which has the wrong default value for sequences unbounded above. Enlarge
N,C to positive integers. The same g,N,C precede p, the character, and w.
The interface only needs nonnegative integer thresholds w (a weakening of
Xu's integer-threshold statement).

This statement contains arbitrary integral equations and phases, with actual
finite sums. It contains no cubic, cone-degree, second-moment decay, desired
manuscript estimate, or arbitrary abstract numerical trace function. It
allows a NEW dense principal open, not every preselected open. No uniform
degree/height bound across varying input equations is asserted.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial Filter PolynomialExponentialFamily FiniteFieldTraceCharacter
open scoped BigOperators Topology Classical

/-- Generic polynomial-family weight dichotomy, on a fixed smaller principal
open, uniform in the good prime and its nontrivial additive character. -/
def PolynomialExponentialDichotomy : Prop :=
  ∀ (n m t s d : ℕ) (G : Fin t → ParameterPolynomial n)
    (H : Fin s → FamilyPolynomial n m) (P : FamilyPolynomial n m)
    (h : ParameterPolynomial n),
    (baseIdeal G).IsPrime →
    ((baseIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ baseIdeal G) = d →
    map (Int.castRingHom ℚ) h ∉ baseIdeal G →
    ∃ (g : ParameterPolynomial n) (N C : ℕ),
      map (Int.castRingHom ℚ) g ∉ baseIdeal G ∧ h ∣ g ∧ 1 ≤ N ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 → ∀ w : ℕ,
          (∀ (K : Type) [Field K] [Fintype K] [CharP K p]
            (y : Fin n → K), y ∈ parameterPoints G g K →
            ‖fiberSum H P (primeTraceCharacter p K ψ) y‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2)) ∨
          (∃ᶠ a : ℕ in atTop, (1/2 : ℝ) ≤
            (∑ y ∈ parameterPoints G g (Extension p a),
              ‖fiberSum H P (primeTraceCharacter p (Extension p a) ψ) y‖^2) /
              (p : ℝ)^(a*(d+w+1)))

end CubicTenVariables.Literature
