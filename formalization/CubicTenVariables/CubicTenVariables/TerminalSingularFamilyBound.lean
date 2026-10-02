import CubicTenVariables.SingularFamilyProduct
import CubicTenVariables.TerminalFamilyBound

/-!
# The wholly singular family numerical terminal bound

For a supplied closed irreducible dominating incidence family, the ambient
singular-dimension upper bound and the source-dimension lower bound force
that family to equal the actual product of its point and normal image
closures. The point factor has dimension at least t+1 and annihilates each
base tangent. A smooth rational point on the actual base component and a
rational frame of its tangent annihilator give an actual rational cubic
restriction whose singular dimension is at least t+1. The already proved
restriction bound yields the terminal codimension inequality.

No existence of a large dominating family is assumed implicitly, and no
external geometric input is used. No positive-dimensional-base or nonzero
rational-parameter premise is required by this wholly singular branch.
-/

noncomputable section
namespace CubicTenVariables.TerminalSingularFamilyBound

open MvPolynomial HessianTheorem11 Module PolynomialRestriction
open RationalConeClosure RationalConeComponents RationalComponentDescent
open TerminalSectionIncidence TerminalFiberCoordinates AffineProductGeometry SingularFamilyProduct

/-- The rational terminal bound for a sufficiently large actual dominating
family wholly inside the ambient gradient-zero locus. The singular-dimension
and family-dimension hypotheses are the explicit geometric inequalities. -/
theorem terminal_bound_of_dominating_singular_family {n z t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (Y : Set (GeometricPoint (n+n))) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hdom : geometricClosure (polynomialMap (normalProjection n) '' Y) = Z)
    (_hcone : IsAffineCone Z)
    (hinc : ∀ y ∈ Y,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence (geometricPolynomial F.polynomial))
    (hgradient : ∀ y ∈ Y,
      gradient (geometricPolynomial F.polynomial) (polynomialMap (pointProjection n) y) = 0)
    (hsing : singularDimension F.polynomial ≤ ((t+1 : ℕ) : Dimension))
    (hdimZ : affineDimension Z = (z : Dimension))
    (hdimY : ((z+t+1 : ℕ) : Dimension) ≤ affineDimension Y) :
    z ≤ n - (3 * (t+2) + 1) / 2 := by
  let D := geometricClosure (polynomialMap (pointProjection n) '' Y)
  have hD : AlgebraicallyClosedSet D := algebraicallyClosedSet_geometricClosure _
  have hiD : GeometricallyIrreducible D :=
    (geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image _)
  have hDsing : D ⊆ singularLocus F.polynomial := by
    intro x hx
    exact gradient_zero_on_image_closure (geometricPolynomial F.polynomial)
      (pointProjection n) Y hgradient x hx
  obtain ⟨c, hc⟩ := ReducedComponentDimension.finite_dimension D hiD.nonempty
  have hcupper : c ≤ t+1 := by
    have hh := (affineDimension_mono hDsing).trans hsing
    rw [hc] at hh
    exact_mod_cast hh
  have hproductDim : affineDimension (geometricClosure
      (polynomialMap (pointProjection n) '' Y)) +
      affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
      affineDimension Y := by
    have hh : affineDimension D +
        affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
        ((z+t+1 : ℕ) : Dimension) := by
      rw [hc, hdom, hdimZ]
      exact_mod_cast (show c+z ≤ z+t+1 by omega)
    exact hh.trans hdimY
  have hprod : Y = product D Z := by
    have he := eq_product_of_image_dimensions Y hY hiY hproductDim
    change Y = product D (geometricClosure (polynomialMap (normalProjection n) '' Y)) at he
    rwa [hdom] at he
  have hYdim : affineDimension Y = affineDimension D + affineDimension Z :=
    (congrArg affineDimension hprod).trans (product_dimension D Z hD hiD hZ.closed hZ.irreducible)
  have hclower : t+1 ≤ c := by
    have hh := hdimY
    rw [hYdim, hc, hdimZ] at hh
    have hnum : z+t+1 ≤ c+z := by exact_mod_cast hh
    omega
  obtain ⟨q, _, hqsmooth⟩ := exists_rational_smooth_point_in_component_open C Z hC hZ Z
    (FiniteDenseOpen.relativelyOpen_self Z) hZ.irreducible.nonempty
  obtain ⟨B, hB, hBG, hBrange⟩ := tangent_annihilator_rational_matrix_frame C Z hC hZ q
  let d := finrank GeometricField
    (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)))
  have htangent : finrank GeometricField
      (affineTangentSpace Z (rationalEmbedding q)) = z := by
    rw [hdimZ] at hqsmooth
    exact_mod_cast hqsmooth.symm
  have hzle : z ≤ n := by
    rw [← htangent]
    have hh := Submodule.finrank_le (affineTangentSpace Z (rationalEmbedding q))
    simpa only [finrank_pi, finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] using hh
  have hdz : d+z = n := by
    dsimp [d]
    rw [TerminalContactTangent.finrank_contact_annihilator, htangent]
    omega
  have hBrange' : LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin =
      coordinatePairing.orthogonal (affineTangentSpace
        (geometricClosure (polynomialMap (normalProjection n) '' Y)) (rationalEmbedding q)) := by
    rw [hdom]
    exact hBrange
  have hcontact := family_mem_restricted_singular_image (geometricPolynomial F.polynomial)
    (geometric_homogeneous F.homogeneous) Y hY hiY hproductDim
    (fun y hy => (hinc y hy).2.1) hgradient (rationalEmbedding q)
    (B.map (algebraMap ℚ GeometricField)) hBrange'
  have hrestriction : restrict (B.map (algebraMap ℚ GeometricField))
      (geometricPolynomial F.polynomial) = geometricPolynomial (restrict B F.polynomial) :=
    (map_restrict (algebraMap ℚ GeometricField) B F.polynomial).symm
  rw [hrestriction] at hcontact
  have hDrestricted : D ⊆ (B.map (algebraMap ℚ GeometricField)).mulVec ''
      singularLocus (restrict B F.polynomial) := by
    intro x hx
    obtain ⟨u, hu, he⟩ := hcontact hx
    exact ⟨u, hu.2, he⟩
  have hDdim : affineDimension D ≤ singularDimension (restrict B F.polynomial) :=
    (affineDimension_mono hDrestricted).trans_eq (affineDimension_linearMap_image
      (B.map (algebraMap ℚ GeometricField)).mulVecLin hBG _)
  have hcontactDim : ((t+1 : ℕ) : Dimension) ≤ singularDimension (restrict B F.polynomial) := by
    have hh : ((t+1 : ℕ) : Dimension) ≤ affineDimension D := by
      rw [hc]
      exact_mod_cast hclower
    exact hh.trans hDdim
  have hambient : singularDimension (restrict B F.polynomial) ≤ (d : Dimension) :=
    TerminalFamilyBound.affineDimension_le_ambient _
  have htd : t+1 ≤ d := by exact_mod_cast hcontactDim.trans hambient
  have hd2 : 2 ≤ d := by omega
  have hupper := TerminalRestrictionBounds.restriction_singularDimension_le F B hB (by omega)
  have hnum : t+1 ≤ (2*d-3)/3 := by exact_mod_cast hcontactDim.trans hupper
  exact TerminalRestrictionBounds.terminal_codimension_numerics hd2 hdz hnum

end CubicTenVariables.TerminalSingularFamilyBound
