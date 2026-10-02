import CubicTenVariables.FixedLeadingSurfaceNormalizedPrimeCount
import CubicTenVariables.IrreducibleFromTopHomogeneousPart
import CubicTenVariables.PrimeMultivariateHomogenization
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal
import TranslatedDepthSeven.SurfaceGradientZeroProgressionCount

/-!
# Singular points of the actual fixed-leading surface

The principal prime and exact surface degree are derived from the displayed
leading form. The previously proved derivative-cut estimate then gives the
coefficient-uniform bound d(d-1)(2B+1), in the actual three affine variables.
There is no Pila, Salberger, or new point-count premise in this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceSingularCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateTransport

/-- A coefficient embedding between fields reflects polynomial units. -/
private theorem isUnit_of_field_map
    {σ K L : Type*} [Field K] [Field L] (ρ : K →+* L)
    (f : MvPolynomial σ K) (hf : IsUnit (map ρ f)) : IsUnit f := by
  have hzero := (isUnit_iff_totalDegree_of_isReduced.mp hf).2
  have heq : f = C (f.coeff 0) := by
    apply map_injective ρ ρ.injective
    simpa only [map_C, coeff_map] using totalDegree_eq_zero_iff_eq_C.mp hzero
  have hc : f.coeff 0 ≠ 0 := by
    intro hz
    apply hf.ne_zero
    rw [heq, hz, C_0, map_zero]
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- Absolute irreducibility in particular implies irreducibility over the
original field; the proof reflects units in a literal factorization. -/
theorem irreducible_of_field_map
    {σ K L : Type*} [Field K] [Field L] (ρ : K →+* L)
    (f : MvPolynomial σ K) (hf : Irreducible (map ρ f)) : Irreducible f := by
  refine ⟨fun hu => hf.not_isUnit (hu.map (map ρ)), ?_⟩
  intro a b hab
  have hfactor : map ρ f = map ρ a * map ρ b := by rw [hab, map_mul]
  exact (hf.isUnit_or_isUnit hfactor).imp
    (isUnit_of_field_map ρ a) (isUnit_of_field_map ρ b)

/-- The fixed rational leading form supplies irreducibility of the actual
highest component of every equation in its nonzero scalar family. -/
theorem irreducible_actual_top
    {d : ℕ} (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) (hc : c ≠ 0)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k) :
    Irreducible (homogeneousComponent d (map (Int.castRingHom ℚ) g)) := by
  have hmap : homogeneousComponent d (map (Int.castRingHom ℚ) g) =
      map (Int.castRingHom ℚ) (homogeneousComponent d g) := by
    ext μ
    simp only [coeff_homogeneousComponent, coeff_map]
    split_ifs <;> simp
  rw [hmap, htop]
  exact irreducible_of_field_map (algebraMap ℚ (AlgebraicClosure ℚ)) _
    (hirr.const_mul c hc)

/-- The normalized homogenization is the actual prime projective surface
of degree d. No Hilbert or prime-ideal certificate is an input. -/
theorem normalized_surface_certificate
    {d : ℕ} (hd : 0 < d) (a b : ℤ) (g : MvPolynomial (Fin 3) ℤ)
    (hdegree : g.totalDegree ≤ d)
    (htop : Irreducible (homogeneousComponent d (map (Int.castRingHom ℚ) g))) :
    let F := projectiveEquiv a b (homogenize d g)
    F ≠ 0 ∧ F.IsHomogeneous d ∧
      (Ideal.span {map (Int.castRingHom ℚ) F}).IsPrime ∧
      HasProjectiveDimensionDegree (Ideal.span {map (Int.castRingHom ℚ) F}) 2 d := by
  let gQ := map (Int.castRingHom ℚ) g
  have hdegreeQ : gQ.totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans hdegree
  have hg : Irreducible gQ :=
    IrreducibleFromTopHomogeneousPart.irreducible_of_irreducible_homogeneousComponent
      gQ hdegreeQ htop
  have hdegreeEq : gQ.totalDegree = d := by
    apply Nat.le_antisymm hdegreeQ
    by_contra h
    exact htop.ne_zero (homogeneousComponent_eq_zero d gQ (Nat.lt_of_not_ge h))
  have hp : (Ideal.span {gQ}).IsPrime :=
    (Ideal.span_singleton_prime hg.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hg)
  have hph := PrimeMultivariateHomogenization.isPrime gQ d hdegreeEq hp
  let e := renameEquiv ℚ (_root_.finSuccEquiv 3).symm
  have hpFin : (Ideal.span {homogenize d gQ}).IsPrime := by
    letI := hph
    have h := Ideal.map_isPrime_of_equiv e
      (I := Ideal.span {multivariateHomogenization gQ d})
    simpa only [Ideal.map_span, Set.image_singleton, e,
      renameEquiv_apply, ← homogenize_eq_standard] using h
  have hpNorm : (Ideal.span {projectiveEquiv (a : ℚ) (b : ℚ) (homogenize d gQ)}).IsPrime := by
    letI := hpFin
    have h := Ideal.map_isPrime_of_equiv (projectiveEquiv (a : ℚ) (b : ℚ))
      (I := Ideal.span {homogenize d gQ})
    simpa only [Ideal.map_span, Set.image_singleton] using h
  have hhom : (projectiveEquiv a b (homogenize d g)).IsHomogeneous d :=
    projectiveEquiv_isHomogeneous a b (homogenize_isHomogeneous d g)
  have hprime : (Ideal.span {map (Int.castRingHom ℚ)
      (projectiveEquiv a b (homogenize d g))}).IsPrime := by
    rw [map_projectiveEquiv, map_homogenize]
    exact hpNorm
  have hneQ : map (Int.castRingHom ℚ) (projectiveEquiv a b (homogenize d g)) ≠ 0 := by
    rw [map_projectiveEquiv, map_homogenize]
    intro hz
    have hhomzero : homogenize d gQ = 0 :=
      (projectiveEquiv (a : ℚ) (b : ℚ)).injective (by simpa using hz)
    have hdehom := congrArg (standardDehomogenizationHom ℚ 3) hhomzero
    rw [standardDehomogenizationHom_homogenize d gQ hdegreeQ, map_zero] at hdehom
    exact hg.ne_zero hdehom
  refine ⟨fun hz => hneQ (by rw [hz, map_zero]), hhom, hprime, ?_⟩
  exact hasProjectiveDimensionDegree_principal_homogeneous _ (hhom.map _) hneQ hd hprime

/-- Literal zero-gradient points in any progression on any member of the
fixed-leading family satisfy one common linear box bound. -/
theorem card_normalized_progression_gradientZero_le
    {d B m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (k g : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) (hc : c ≠ 0)
    (hdegree : g.totalDegree ≤ d)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k)
    (a b : ℤ) (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (hzero : ∀ z ∈ S,
      eval (progressionHomogeneousPoint u m z) (projectiveEquiv a b (homogenize d g)) = 0)
    (hgrad : ∀ z ∈ S, ∀ i : Fin 3,
      eval (fun j => u j + (m : ℤ) * z j)
        (pderiv i (surfaceHypersurfaceFirstChartDehomogenize
          (projectiveEquiv a b (homogenize d g)))) = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * (d - 1) * (2 * B + 1) := by
  obtain ⟨hne, hhom, hprime, hdim⟩ := normalized_surface_certificate hd a b g hdegree
    (irreducible_actual_top k g c hirr hc htop)
  exact card_surface_progression_integerGradientZero_le hm _ hne hhom hprime hdim
    u S hzero hgrad hbox

end CubicTenVariables.FixedLeadingSurfaceSingularCount
