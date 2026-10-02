import CubicTenVariables.TerminalFiberCoordinates
import CubicTenVariables.TerminalRestrictionBounds
import HessianTheorem11.UnconditionalPolynomialDimension

/-!
The nonsingular-family branch of the rational terminal bound is now assembled
for an actual supplied closed irreducible incidence component of sufficiently
large dimension. The rational parameter, contact fiber, rational frame,
fiber-to-point dimension transfer, and numerical bound are all constructed.
Existence of the required dominating component is still a separate obligation.
-/

noncomputable section
namespace CubicTenVariables.TerminalFamilyBound

open MvPolynomial HessianTheorem11 Module PolynomialRestriction
open RationalConeClosure TerminalSectionIncidence TerminalFiberCoordinates

/-- Every actual affine set has dimension at most its coordinate dimension. -/
theorem affineDimension_le_ambient {d : ℕ} (S : Set (GeometricPoint d)) :
    affineDimension S ≤ (d : Dimension) :=
  (ringKrullDim_quotient_le (vanishingIdeal GeometricField S)).trans
    (UnconditionalPolynomialDimension.polynomial_dimension_le d)

/-- The rational terminal bound for a supplied dominating incidence family
whose affine dimension is at least z+t+1 and whose nonzero-gradient locus
contains a dense source-open. No fiber-dimension lower bound is assumed. -/
theorem terminal_bound_of_dominating_contact_family {n z t : ℕ}
    (F : AnisotropicCubic n) (ht : 1 ≤ t)
    (Y : Set (GeometricPoint (n + n))) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hdom : geometricClosure (polynomialMap (normalProjection n) '' Y) = Z)
    (hcone : IsAffineCone Z)
    (hinc : ∀ y ∈ Y,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence (geometricPolynomial F.polynomial))
    (W : Set (GeometricPoint (n + n))) (hW : RelativelyOpenSet Y W)
    (hdW : geometricClosure W = Y)
    (hnormal : ∀ y ∈ W, polynomialMap (normalProjection n) y ≠ 0)
    (hgradient : ∀ y ∈ W,
      gradient (geometricPolynomial F.polynomial) (polynomialMap (pointProjection n) y) ≠ 0)
    (hdimZ : affineDimension Z = (z : Dimension))
    (hdimY : ((z + t + 1 : ℕ) : Dimension) ≤ affineDimension Y) :
    z ≤ n - (3 * (t + 2) + 1) / 2 := by
  obtain ⟨U, V, q, hU, _, _, _, _, _, _, _, _, _, hqsmooth,
      d, B, hd, hB, hBG, _, hne, hcontact⟩ :=
    TerminalRationalContact.exists_rational_contact_fiber F.polynomial
      (pointProjection n) (normalProjection n) Y hY hiY C Z hC hZ hdom hcone
      hinc W hW hdW hnormal hgradient
  have hsource := source_dimension_le_restriction F.polynomial Y U hY hiY hU
    (RationalConeClosure.rationalEmbedding q) hne B hBG hcontact
  have himage : affineDimension (polynomialMap (normalProjection n) '' Y) =
      (z : Dimension) := (affineDimension_closure _).symm.trans (hdom ▸ hdimZ)
  rw [himage] at hsource
  have htangent : finrank GeometricField
      (affineTangentSpace Z (rationalEmbedding q)) = z := by
    rw [hdimZ] at hqsmooth
    exact_mod_cast hqsmooth.symm
  have hzle : z ≤ n := by
    rw [← htangent]
    have hh := Submodule.finrank_le (affineTangentSpace Z (rationalEmbedding q))
    simpa only [finrank_pi, finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one] using hh
  have hdz : d + z = n := by
    rw [hd, TerminalContactTangent.finrank_contact_annihilator, htangent]
    omega
  have hambient : singularDimension (restrict B F.polynomial) ≤ (d : Dimension) :=
    affineDimension_le_ambient _
  have hdimd : ((z + t + 1 : ℕ) : Dimension) ≤ (z : Dimension) + (d : Dimension) :=
    hdimY.trans (hsource.trans (add_le_add_right hambient _))
  have htd : t + 1 ≤ d := by
    have hh : z + t + 1 ≤ z + d := by exact_mod_cast hdimd
    omega
  have hd2 : 2 ≤ d := by omega
  have hupper := TerminalRestrictionBounds.restriction_singularDimension_le F B hB (by omega)
  have hnumdim := hdimY.trans (hsource.trans (add_le_add_right hupper (z : Dimension)))
  have hnum : z + t + 1 ≤ z + (2 * d - 3) / 3 := by exact_mod_cast hnumdim
  exact TerminalRestrictionBounds.terminal_codimension_numerics hd2 hdz (by omega)

end CubicTenVariables.TerminalFamilyBound
