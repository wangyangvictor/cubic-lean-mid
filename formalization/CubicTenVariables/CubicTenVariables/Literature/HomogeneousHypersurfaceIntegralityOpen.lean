import CubicTenVariables.Literature.FiniteFieldPointCounts
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Principal-open spreading for a fixed-degree homogeneous hypersurface

This is the one standard algebraic-geometric input used to turn the
internally constructed Bertini section into an integral pencil over `Z`.
It is deliberately stated for the actual homogeneous equation and its
actual principal quotient.  It contains neither a surface point count nor a
Bertini existence assertion.

After inverting one degree-`d` coefficient, the corresponding projective
hypersurface is an effective Cartier divisor in projective space, hence a
flat proper family of finite presentation with constant Hilbert polynomial.
Geometrically reduced fibers form an open set by Stacks Project, Lemma
37.26.7 (tag 0C0E).  Geometric irreducibility spreads from the generic fiber
by Lemma 37.27.5 (tag 0559); equivalently one may use the constructibility of
the number of geometric components in Lemma 37.27.6.  Their intersection is
the geometrically integral locus.  A principal neighborhood of the supplied
good point, multiplied by the chosen degree coefficient, gives the element
`s` below.  Base change to an algebraic closure gives the displayed affine
cone quotient.  This is the standard projective-hypersurface coordinate-ring
corollary of those results.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.Literature

open MvPolynomial

/-- Geometric integrality of a fixed-degree homogeneous hypersurface persists
on one actual principal open through any nonzero geometrically integral fiber.
The explicit nonzero condition excludes the zero equation, whose principal
quotient is a domain but whose degree is not the displayed positive degree. -/
def HomogeneousHypersurfaceIntegralityOpen : Prop :=
  ∀ (R Ω : Type) [CommRing R] [Field Ω] [IsAlgClosed Ω]
    (n d : ℕ) (_hd : 1 ≤ d) (ρ : R →+* Ω)
    (F : MvPolynomial (Fin n) R),
    F.IsHomogeneous d →
    map ρ F ≠ 0 →
    IsDomain (MvPolynomial (Fin n) Ω ⧸ Ideal.span {map ρ F}) →
    ∃ s : R, ρ s ≠ 0 ∧
      ∀ (K : Type) [Field K] (τ : R →+* K), τ s ≠ 0 →
        (map τ F).totalDegree = d ∧
        IsDomain (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
          Ideal.span {map (algebraMap K (AlgebraicClosure K)) (map τ F)})

end CubicTenVariables.Literature
