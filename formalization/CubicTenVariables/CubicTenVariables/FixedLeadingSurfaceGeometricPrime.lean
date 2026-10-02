import CubicTenVariables.FixedLeadingSurfaceSingularCount

/-!
# Geometric primality of the actual normalized surface

The proof runs the existing lossless homogenization argument over an
algebraic closure, then identifies both literal coefficient maps. This
supplies the geometric-prime premise of the residual component argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceGeometricPrime

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateTransport

/-- An irreducible highest component makes the normalized homogenization
prime over the same coefficient field. -/
theorem isPrime_normalized_homogenize
    {K : Type*} [Field K] {d : ℕ} (a b : K) (g : MvPolynomial (Fin 3) K)
    (hdegree : g.totalDegree ≤ d)
    (htop : Irreducible (homogeneousComponent d g)) :
    (Ideal.span {projectiveEquiv a b (homogenize d g)}).IsPrime := by
  have hg := IrreducibleFromTopHomogeneousPart.irreducible_of_irreducible_homogeneousComponent
    g hdegree htop
  have hdegreeEq : g.totalDegree = d := by
    apply Nat.le_antisymm hdegree
    by_contra h
    exact htop.ne_zero (homogeneousComponent_eq_zero d g (Nat.lt_of_not_ge h))
  have hp : (Ideal.span {g}).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have hph := PrimeMultivariateHomogenization.isPrime g d hdegreeEq hp
  let e := renameEquiv K (_root_.finSuccEquiv 3).symm
  have hpFin : (Ideal.span {homogenize d g}).IsPrime := by
    letI := hph
    have h := Ideal.map_isPrime_of_equiv e
      (I := Ideal.span {multivariateHomogenization g d})
    simpa only [Ideal.map_span, Set.image_singleton, e,
      renameEquiv_apply, ← homogenize_eq_standard] using h
  letI := hpFin
  have h := Ideal.map_isPrime_of_equiv (projectiveEquiv a b)
    (I := Ideal.span {homogenize d g})
  simpa only [Ideal.map_span, Set.image_singleton] using h

/-- The exact rational principal ideal used by the determinant construction
is prime after its actual coefficient extension to Qbar. -/
theorem geometrically_prime_normalized_surface
    {d : ℕ} (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) (hc : c ≠ 0)
    (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (a b : ℤ) :
    ((Ideal.span {map (Int.castRingHom ℚ)
      (projectiveEquiv a b (homogenize d g))}).map
        (map (algebraMap ℚ Qbar))).IsPrime := by
  let gQ := map (Int.castRingHom ℚ) g
  let gA := map (algebraMap ℚ Qbar) gQ
  have hdegreeA : gA.totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans
      ((Finset.sup_mono (support_map_subset _ _)).trans hdegree)
  have hcomponentQ : homogeneousComponent d gQ =
      map (Int.castRingHom ℚ) (homogeneousComponent d g) := by
    ext μ
    simp only [gQ, coeff_homogeneousComponent, coeff_map]
    split_ifs <;> simp
  have hcomponentA : homogeneousComponent d gA =
      map (algebraMap ℚ Qbar) (homogeneousComponent d gQ) := by
    ext μ
    simp only [gA, coeff_homogeneousComponent, coeff_map]
    split_ifs <;> simp
  have hirrA : Irreducible (homogeneousComponent d gA) := by
    rw [hcomponentA, hcomponentQ, htop]
    exact hirr.const_mul c hc
  have h := isPrime_normalized_homogenize
    (algebraMap ℚ Qbar (a : ℚ)) (algebraMap ℚ Qbar (b : ℚ)) gA hdegreeA hirrA
  simpa only [Ideal.map_span, Set.image_singleton, map_projectiveEquiv,
    map_homogenize, gA, gQ] using h

end CubicTenVariables.FixedLeadingSurfaceGeometricPrime
