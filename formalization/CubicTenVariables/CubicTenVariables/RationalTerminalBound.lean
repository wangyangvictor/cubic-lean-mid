import CubicTenVariables.TerminalSingularFamilyBound
import CubicTenVariables.TerminalFamilyOpen
import CubicTenVariables.TerminalBadNormals
import HessianTheorem11.ConeComponents

/-!
The dimension inequality for the actual rational closure of bad affine
normals. Both the nonsingular and wholly singular family branches are
proved, and a large dominating component is constructed from actual dense
large fibers. No supplied contact open, dominating family, generic-fiber
dimension, product decomposition, or rational frame is an input.

This file does not prove that the bad-normal set itself is closed, identify
its rational points with those of the closure, or supply reduction-mod-p
statements. The singular-dimension hypothesis is the explicit range of t
in the source proposition, expressed for the affine singular cone.
-/

noncomputable section
namespace CubicTenVariables.RationalTerminalBound
open MvPolynomial HessianTheorem11
open RationalConeClosure TerminalSectionIncidence TerminalFiberCoordinates
open TerminalIncidenceFamily TerminalBadNormals

/-- The two actual family branches give the terminal bound without a
supplied nonzero-gradient open or a wholly-singular/product alternative. -/
theorem terminal_bound_of_dominating_family {n z t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (Y : Set (GeometricPoint (n+n))) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hdom : geometricClosure (polynomialMap (normalProjection n) '' Y) = Z)
    (hcone : IsAffineCone Z)
    (hinc : ∀ y ∈ Y,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence (geometricPolynomial F.polynomial))
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension))
    (hdimZ : affineDimension Z = (z : Dimension))
    (hdimY : ((z+t+1 : ℕ) : Dimension) ≤ affineDimension Y) :
    z ≤ n - (3 * (t+2) + 1) / 2 := by
  by_cases hz : z = 0
  · subst z
    exact Nat.zero_le _
  by_cases hg : ∃ y ∈ Y,
      gradient (geometricPolynomial F.polynomial) (polynomialMap (pointProjection n) y) ≠ 0
  · obtain ⟨W, hW, hdW, _, hnW, hgW⟩ :=
      TerminalFamilyOpen.exists_nonsingular_normal_open (geometricPolynomial F.polynomial)
        Y hY hiY (TerminalFamilyOpen.exists_nonzero_normal Y Z hdom hdimZ (by omega)) hg
    exact TerminalFamilyBound.terminal_bound_of_dominating_contact_family F ht
      Y hY hiY C Z hC hZ hdom hcone hinc W hW hdW hnW hgW hdimZ hdimY
  · push_neg at hg
    exact TerminalSingularFamilyBound.terminal_bound_of_dominating_singular_family F ht
      Y hY hiY C Z hC hZ hdom hcone hinc hg hsing hdimZ hdimY

/-- Every actual component of the actual rational closure satisfies the
numerical terminal bound. The required incidence component is constructed. -/
theorem rational_badNormals_component_dimension_le {n z t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension))
    (hne : (badNormals (geometricPolynomial F.polynomial) t).Nonempty)
    (Z : Set (GeometricPoint n))
    (hZ : IsIrreducibleComponent
      (rationalConeClosure (badNormals (geometricPolynomial F.polynomial) t)) Z)
    (hz : affineDimension Z = (z : Dimension)) :
    z ≤ n - (3 * (t+2) + 1) / 2 := by
  let B := badNormals (geometricPolynomial F.polynomial) t
  obtain ⟨Y, hY, hdom, hdim⟩ := TerminalBadNormals.exists_large_incidence_component
    (geometricPolynomial F.polynomial) hne Z hZ hz
  have hcone : IsAffineCone Z := hZ.isAffineCone
    Unconditional.concentrationGeometry.toAffineComponentsInput
    (rationalConeClosure_closed B)
    (rationalConeClosure_isAffineCone B (badNormals_isAffineCone _ _))
  have hZ' := RationalClosureIdempotent.component_after_idempotence B Z hZ
  exact terminal_bound_of_dominating_family F ht Y hY.closed hY.irreducible
    (rationalConeClosure B) Z (rationalConeClosure_closed B) hZ' hdom hcone
    (fun y hy => (hY.subset hy).1) hsing hz hdim

/-- The actual rational closure of the literal bad-normal set has the
source's terminal dimension bound. Natural subtraction encodes max(0,−).
No closedness or proper-fiber theorem for the bad-normal set is assumed. -/
theorem rational_badNormals_dimension_le {n t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension)) :
    affineDimension (rationalConeClosure (badNormals (geometricPolynomial F.polynomial) t)) ≤
      ((n - (3 * (t+2) + 1) / 2 : ℕ) : Dimension) := by
  let B := badNormals (geometricPolynomial F.polynomial) t
  by_cases hne : B.Nonempty
  · obtain ⟨c, Z, hcover, hZ⟩ := ReducedMaximalComponent.finite_components
      (rationalConeClosure B) (rationalConeClosure_closed B)
    change affineDimension (rationalConeClosure B) ≤ _
    rw [hcover]
    apply affineDimension_fintype_union_le
    intro i
    obtain ⟨z, hz⟩ := ReducedComponentDimension.finite_dimension (Z i) (hZ i).irreducible.nonempty
    rw [hz]
    exact_mod_cast rational_badNormals_component_dimension_le F ht hsing hne (Z i) (hZ i) hz
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hR : rationalConeClosure B ⊆ ({0} : Set (GeometricPoint n)) := by
      have hB : AlgebraicallyClosedSet B := he ▸ ReducedBiconeComponent.closed_empty
      simpa only [he, Set.empty_union] using rationalConeClosure_subset B hB
    exact (affineDimension_mono hR).trans (by
      rw [affineDimension_origin]
      exact_mod_cast (Nat.zero_le (n - (3 * (t+2) + 1) / 2)))

end CubicTenVariables.RationalTerminalBound
