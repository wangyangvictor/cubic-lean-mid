import HessianTheorem11.AffineGeometry

/-!
An explicit standard-literature corollary for finite integer polynomial
families on a principal parameter open. No inhabitant or global axiom is
declared; applications retain this proposition as a theorem argument.

Precise primary references:
* Stacks 0579, Lemma 37.26.5: geometrically reduced fibers form a locally
  constructible set for a quasi-compact, locally finitely presented morphism.
  https://stacks.math.columbia.edu/tag/0579
* Stacks 055B, Lemma 37.27.7: the number of geometric irreducible components
  has locally constructible level sets for a finitely presented morphism.
  The level one includes nonemptiness. https://stacks.math.columbia.edu/tag/055B
* Stacks 054K, Theorem 29.23.3, Chevalley (EGA IV, Theorem 1.8.4): images
  of constructible sets under these morphisms are constructible.
  https://stacks.math.columbia.edu/tag/054K
* Stacks 005K, Lemma 5.15.15: a constructible subset of an irreducible space
  missing its generic point is not dense. https://stacks.math.columbia.edu/tag/005K
* Stacks 00FV, Theorem 10.34.1, Hilbert's Nullstellensatz: nonempty locally
  closed finite-type Q-schemes have points over Qbar.
  https://stacks.math.columbia.edu/tag/00FV

Intersecting geometric reducedness with the one-component level gives the
geometrically integral locus. Its complement inside D(g) is constructible.
The Qbar hypothesis makes its generic fiber empty. Chevalley's theorem and
005K show that its image in Spec Z lies over finitely many primes. Removing
those primes proves the displayed assertion over every algebraically closed
field in each remaining characteristic. No properness, homogeneity, cubic,
hyperplane, dimension bound, or point-count statement is part of this input.
-/

set_option autoImplicit false

noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11

/-- Literal ideal obtained by specializing the parameter coefficients. -/
def integralityFiberIdeal {σ τ ι : Type*}
    (f : ι → MvPolynomial τ (MvPolynomial σ ℤ))
    (K : Type*) [CommRing K] (v : σ → K) : Ideal (MvPolynomial τ K) :=
  Ideal.span (Set.range (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i)))

/-- The generic integrality-spreading corollary is an explicit premise.
The exceptional integer precedes all primes, fields and parameter values. -/
def FiberGeometricIntegralitySpreading : Prop :=
  ∀ (σ τ ι : Type) [Fintype σ] [Fintype τ] [Fintype ι]
    (f : ι → MvPolynomial τ (MvPolynomial σ ℤ)) (g : MvPolynomial σ ℤ),
    (∀ v : σ → GeometricField,
      eval₂ (Int.castRingHom GeometricField) v g ≠ 0 →
      IsDomain (MvPolynomial τ GeometricField ⧸ integralityFiberIdeal f GeometricField v)) →
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p] (v : σ → K),
        eval₂ (Int.castRingHom K) v g ≠ 0 →
        IsDomain (MvPolynomial τ K ⧸ integralityFiberIdeal f K v)

end CubicTenVariables.Literature
