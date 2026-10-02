import CubicTenVariables.Literature.FiniteFieldPointCounts

/-!
A numerical fragment of Weil I for smooth projective cubic hypersurfaces
of dimensions one, two and three. This file declares a proposition to be
passed explicitly, not an axiom or a proof of Weil I.

Precise primary reference: P. Deligne, La conjecture de Weil. I,
Publications Mathématiques de l'IHÉS 43 (1974), 273–307, Théorème (8.1),
pp. 301–302, https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf .
The primitive middle Betti numbers for smooth cubics in these three
dimensions are 2, 6, 10: D. Huybrechts, The Geometry of Cubic Hypersurfaces,
Cambridge Studies in Advanced Mathematics 206 (2023), Corollary 1.12
and its following table, p. 6 in the publisher's excerpt:
https://assets.cambridge.org/97810092/80006/excerpt/9781009280006_excerpt.pdf .
We use the common upper bound 10 and square the
inequality. For projective point count P and affine cone count A,
A = 1 + (q-1) P, so the exact cone-centred expression is A-q^(r+1).

Smoothness is expressed using the actual equation and all its partial
derivatives over the algebraic closure: their only common zero is the
origin. No supplied trace, cohomology, stratification or exceptional set
appears in the premise. Quantification includes every finite field.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial

/-- The geometric singular cone contains no nonzero point. -/
def ProjectivelySmooth {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin n) K) : Prop :=
  ∀ x, x ∈ geometricSingularCone F → x = 0

/-- Only the curve case is needed to replace the affine plane-curve input.
The common constant 10 is deliberately inessential; Hasse gives 2 here. -/
def SmoothPlaneCubicWeil : Prop :=
  ∀ (K : Type) [Field K] [Fintype K]
    (F : MvPolynomial (Fin 3) K),
    F ≠ 0 → F.IsHomogeneous 3 → ProjectivelySmooth F →
    ((affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^2)^2 ≤
      100 * ((Fintype.card K : ℝ)-1)^2 * (Fintype.card K : ℝ)

/-- Squared numerical Weil bound for smooth cubic curves, surfaces and
threefolds, with a single explicit constant. -/
def SmoothCubicWeil : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ 3 →
    ∀ (K : Type) [Field K] [Fintype K]
      (F : MvPolynomial (Fin (r+2)) K),
      F ≠ 0 → F.IsHomogeneous 3 → ProjectivelySmooth F →
      ((affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^(r+1))^2 ≤
        100 * ((Fintype.card K : ℝ)-1)^2 * (Fintype.card K : ℝ)^r

/-- The plane-cubic specialization has no cohomological objects in its
statement. It is still conditional on the explicitly displayed Weil input. -/
theorem SmoothCubicWeil.plane (h : SmoothCubicWeil) :
    SmoothPlaneCubicWeil := by
  intro K _ _ F hne hF hsmooth
  simpa using h 1 (by decide) (by decide) K F hne hF hsmooth

end CubicTenVariables.Literature
