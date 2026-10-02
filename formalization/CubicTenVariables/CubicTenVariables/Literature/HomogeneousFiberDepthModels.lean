import CubicTenVariables.IntegralGeometricFiberDepth

/-! Generic coordinate interface, now proved internally: exact integral models
of positive geometric fiber-depth loci of bihomogeneous polynomial families.
The inhabitant is `HomogeneousFiberDepthModelsProved.proved`. The references
below give the original literature derivation; the internal proof uses finite
linear-cut determinants and integer zero-set spreading.

References and derivation:

* Stacks, Lemma 37.30.5 (0D4I), proper upper semicontinuity of fiber dimension:
  https://stacks.math.columbia.edu/tag/0D4I
* Stacks, Lemma 37.30.2 (05F8), invariance of fiber dimension under base change:
  https://stacks.math.columbia.edu/tag/05F8
* Stacks, Lemma 10.31.1 (00FN), Noetherianity of polynomial rings; homogeneous
  ideals have homogeneous generators, and Noetherianity makes a finite
  subset suffice (Definition 111.27.1 (0281)):
  https://stacks.math.columbia.edu/tag/00FN
  https://stacks.math.columbia.edu/tag/0281
* Stacks, Lemma 10.45.6 (00I4), a reduced algebra over a perfect field is
  geometrically reduced; applied to the reduced depth locus over Q:
  https://stacks.math.columbia.edu/tag/00I4
* Stacks, Theorem 29.23.3 (054K), Chevalley, and Lemma 5.15.15 (005K): a
  constructible subset of Spec Z missing its generic point lies over finitely
  many primes. These spread equality after denominators are cleared:
  https://stacks.math.columbia.edu/tag/054K
  https://stacks.math.columbia.edu/tag/005K

Projectivize the fiber variables. Positive outer degrees ensure every affine
fiber contains its vertex. For j=1 the condition is nonemptiness of the
projective fiber, so closedness follows from the proper image directly.
For j>=2 the condition is projective dimension at least j-1, to which proper
upper semicontinuity applies. Thus no convention assigning dimension zero
to the empty scheme is confused with a nonempty zero-dimensional fiber.
The projective incidence is proper over parameter space, so its depth locus is closed and its
underlying set commutes with extension fields. Homogeneity in the parameter
block makes this closed locus conical. Take its reduced ideal over Q,
choose finite homogeneous rational generators, and clear their denominators.
Perfectness of Q identifies the extended ideal with the actual Qbar
vanishing ideal, rather than merely an ideal having the same zero set.
The symmetric difference between this model and the proper depth locus is
constructible and has empty generic fiber; removing its finite set of image
primes gives the exact equality over every field of every remaining
characteristic. No reducedness assertion in positive characteristic is used.

This proposition supplies no dimension bound on the parameter locus, no
codimension gain, singular-support construction, cohomology or trace estimate.
No global axiom is declared. The proof is in a separate module to keep this
interface independent of its construction. -/

noncomputable section
namespace CubicTenVariables.Literature
open MvPolynomial HessianTheorem11 IntegralGeometricFiberDepth

/-- The precise generic interface, with an internally proved inhabitant. The finite integral model and positive
exceptional integer are chosen before all primes, fields, and parameters.
Characteristic-zero reducedness is asserted as an equality of actual ideals.
The other conclusion is equality of the actual geometric depth locus with
the zero set of the same fixed integer equations. -/
def HomogeneousFiberDepthModels : Prop :=
  ∀ (m n t j : ℕ), 0 < j →
    ∀ (f : Fin t → MvPolynomial (Fin n) (MvPolynomial (Fin m) ℤ))
      (dx dv : Fin t → ℕ),
      (∀ i, 0 < dx i) →
      (∀ i, (f i).IsHomogeneous (dx i)) →
      (∀ i s, (coeff s (f i)).IsHomogeneous (dv i)) →
      ∃ (u : ℕ) (G : Fin u → MvPolynomial (Fin m) ℤ)
        (d : Fin u → ℕ) (D : ℕ),
        (∀ i, (G i).IsHomogeneous (d i)) ∧ 1 ≤ D ∧
        Ideal.span (Set.range (fun i => map (Int.castRingHom GeometricField) (G i))) =
          vanishingIdeal GeometricField
            {v : GeometricPoint m | (j : Dimension) ≤
              ReducedGaussSection.coordinateDimension (fiber f GeometricField v)} ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ D →
          ∀ (K : Type) [Field K] [CharP K p] (v : Fin m → K),
            (∀ i, eval₂ (Int.castRingHom K) v (G i) = 0) ↔
              (j : WithBot ℕ∞) ≤ geometricFiberDimension f K v

end CubicTenVariables.Literature
