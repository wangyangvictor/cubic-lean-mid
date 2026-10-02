import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.PilaLowDimension

/-!
# Pila's theorem for affine translates of low-dimensional projective cones

A homogeneous prime ideal in `N + 1` variables defines both a projective
variety in `P^N` and its affine cone in `A^(N+1)`.  The projective Hilbert
polynomial has degree `r`; its cumulative Hilbert polynomial has degree
`r + 1`, with the same projective degree.  `HilbertAffineChange` proves this
comparison internally.

This file records the two applications needed for the packet argument.  The
first is the exact affine-dimension-and-degree certificate after an arbitrary
invertible scalar affine change of coordinates.  The second specializes the
change of coordinates to the literal packet substitution

`X i |-> x₀ i + m * X i`.

Finally, projective dimension at most three gives affine dimension at most
four, so the already derived low-dimensional specialization of Pila's
Theorem A applies with one coefficient-uniform constant.  No geometric
counting assertion is introduced as an additional hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

open Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine cone over a homogeneous prime projective variety retains its
dimension and degree after an invertible scalar affine change of coordinates.
The projective dimension `r` becomes affine dimension `r + 1`. -/
theorem hasAffineDimensionDegree_affineChange_of_projectiveCone
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℝ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ))
    (hprime : I.IsPrime)
    (hprojective : HasProjectiveDimensionDegree I r d)
    (y₀ : Fin (N + 1) → ℝ) (s : ℝ) (hs : s ≠ 0) :
    HasAffineDimensionDegree
      (I.map (affinePolynomialChangeAlgEquiv y₀ s hs)) (r + 1) d := by
  apply
    (hasAffineDimensionDegree_map_affinePolynomialChange_iff
      I y₀ s hs (r + 1) d).2
  exact
    hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
      I hhomogeneous hprime r d hprojective

/-- Exact specialization of the preceding certificate to the packet
coordinates `x = x₀ + m y`. -/
theorem hasAffineDimensionDegree_packetChange_of_projectiveCone
    {N r d m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℝ))
    (hhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ))
    (hprime : I.IsPrime)
    (hprojective : HasProjectiveDimensionDegree I r d)
    (x₀ : IntVector (N + 1)) :
    HasAffineDimensionDegree
      (I.map
        (affinePolynomialChangeAlgEquiv
          (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
          (by exact_mod_cast hm.ne'))) (r + 1) d := by
  exact hasAffineDimensionDegree_affineChange_of_projectiveCone
    I hhomogeneous hprime hprojective (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
      (by exact_mod_cast hm.ne')

/-- Pila's coefficient-uniform `B^(4 + epsilon)` estimate for every affine
change of the cone over a projective variety of dimension at most three and
bounded degree.  Positivity of the degree is a consequence of the prime
projective Hilbert data, rather than a separate hypothesis. -/
theorem pila1995_affineChanges_of_projectiveCones_dimensionAtMostThree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r d : ℕ), r ≤ 3 → d ≤ D →
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℝ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) →
          I.IsPrime →
          HasProjectiveDimensionDegree I r d →
          ∀ (y₀ : Fin (N + 1) → ℝ) (s : ℝ) (hs : s ≠ 0),
            ∀ B : ℝ, 1 < B →
              ((pilaIntegralPoints
                (I.map (affinePolynomialChangeAlgEquiv y₀ s hs))
                B).card : ℝ) ≤ C * B ^ ((4 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_dimensionAtMostFour_boundedDegree hPila (N + 1) D ε hε
  refine ⟨C, hC, ?_⟩
  intro r d hr hdD I hhomogeneous hprime hprojective y₀ s hs B hB
  have hd : 1 ≤ d :=
    projectiveDegree_pos_of_hasProjectiveDimensionDegree
      I r d hprojective
  exact hbound (r + 1) d (by omega) hd hdD
    (I.map (affinePolynomialChangeAlgEquiv y₀ s hs))
    (hasAffineDimensionDegree_affineChange_of_projectiveCone
      I hhomogeneous hprime hprojective y₀ s hs) B hB

/-- The same Pila estimate in the literal integral packet coordinates
`x = x₀ + m y`. -/
theorem pila1995_packetChanges_of_projectiveCones_dimensionAtMostThree
    (hPila : Pila1995TheoremA)
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r d m : ℕ), r ≤ 3 → d ≤ D → ∀ (hm : 0 < m),
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℝ)),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℝ) →
          I.IsPrime →
          HasProjectiveDimensionDegree I r d →
          ∀ (x₀ : IntVector (N + 1)) (B : ℝ), 1 < B →
            ((pilaIntegralPoints
              (I.map
                (affinePolynomialChangeAlgEquiv
                  (fun i ↦ (x₀ i : ℝ)) (m : ℝ)
                  (by exact_mod_cast hm.ne')))
              B).card : ℝ) ≤ C * B ^ ((4 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    pila1995_affineChanges_of_projectiveCones_dimensionAtMostThree
      hPila N D ε hε
  refine ⟨C, hC, ?_⟩
  intro r d m hr hdD hm I hhomogeneous hprime hprojective x₀ B hB
  exact hbound r d hr hdD I hhomogeneous hprime hprojective
    (fun i ↦ (x₀ i : ℝ)) (m : ℝ) (by exact_mod_cast hm.ne') B hB

end

end TranslatedDepthSeven
