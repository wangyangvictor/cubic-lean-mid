import HessianTheorem11.AffineGeometry

/-! Explicit standard-literature input for uniform reduction of fiber-dimension
containments. This is a polynomial-coordinate corollary, not a verbatim lemma:

* Stacks 05F9, Lemma 37.30.3: constructibility of fiber-dimension level sets
  for a finitely presented morphism; https://stacks.math.columbia.edu/tag/05F9
* Stacks 054K, Theorem 29.23.3 (Chevalley): constructibility of images;
  https://stacks.math.columbia.edu/tag/054K
* Stacks 05F8, Lemma 37.30.2: invariance under arbitrary base change;
  https://stacks.math.columbia.edu/tag/05F8
* Stacks 005K, Lemma 5.15.15: a constructible subset missing the generic point
  of an irreducible space is not dense; https://stacks.math.columbia.edu/tag/005K
* Stacks 00FV (Nullstellensatz) supplies geometric points of nonempty locally
  closed subsets of affine space over Q; https://stacks.math.columbia.edu/tag/00FV

The bad parameters outside the fixed model form a constructible subset of
affine space over Z. Its generic fiber is empty by the displayed Qbar premise.
Its image in Spec Z is constructible and misses the generic point, hence is
supported on finitely many primes. Base change gives the assertion over every
field of each remaining characteristic. No properness or homogeneity is needed.

No inhabitant or global axiom is declared: applications take this proposition
as an explicit argument. This input assumes no cubic theorem, terminal model,
dimension bound, point-count estimate, or rational-zero conclusion.
-/

noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11

/-- The literal specialized ideal of an integer polynomial family. Outer
variables are fiber coordinates; coefficient variables are parameters. -/
def integralFamilyFiberIdeal {m n : ℕ} {ι : Type*}
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (K : Type*) [CommRing K] (v : Fin m → K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range (fun i => map (eval₂Hom (Int.castRingHom K) v) (f i)))

/-- The precise unproved literature corollary. The integer D is selected
before all primes, extension fields and parameters. The generic-fiber
containment is over every geometric parameter, not only rational points. -/
def FiberDimensionContainmentSpreading : Prop :=
  ∀ (m n r : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (f : ι → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
    (G : κ → MvPolynomial (Fin m) ℤ),
    (∀ v : GeometricPoint m,
      (r : Dimension) ≤ ringKrullDim (MvPolynomial (Fin n) GeometricField ⧸
        integralFamilyFiberIdeal f GeometricField v) →
      ∀ i, eval₂ (Int.castRingHom GeometricField) v (G i) = 0) →
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p] (v : Fin m → K),
        (r : Dimension) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸
          integralFamilyFiberIdeal f K v) →
        ∀ i, eval₂ (Int.castRingHom K) v (G i) = 0

end CubicTenVariables.Literature
