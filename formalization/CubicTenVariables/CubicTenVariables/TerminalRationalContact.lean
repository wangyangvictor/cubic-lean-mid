import CubicTenVariables.TerminalGenericContact
import CubicTenVariables.RationalComponentDescent
import HessianTheorem11.UnconditionalChevalleyOpen

/-!
# Rational contact fibers of a supplied actual incidence family

The proved generic contact open has an image containing a nonempty dense
base-open, by the proved point-set Chevalley theorem. If that base is an
actual component of the rational closure, its dense rational points give a
smooth rational parameter in this open. The tangent annihilator descends
to an injective rational matrix frame. Every point of the resulting
nonempty contact fiber maps into the actual singular locus of the rational
restriction, after coefficient extension, with the polynomial equation
retained as well as its partial derivatives.

The closed irreducible dominating incidence family and its dense open of
nonzero normals and nonzero gradients are explicit hypotheses. This file
does not construct that family or assert a dimension lower bound on its
fibers. In particular nonemptiness is not confused with dimension t+1.
-/

noncomputable section
namespace CubicTenVariables.TerminalRationalContact

open MvPolynomial HessianTheorem11 Module PolynomialRestriction
open RationalConeClosure RationalConeComponents RationalComponentDescent
open TerminalSectionIncidence TerminalGenericContact

/-- For a supplied actual dominating family, construct the contact source
open, a base-open in its image, a nonzero smooth rational parameter, and an
actual rational annihilator frame. The whole contact fiber at that
parameter maps into the actual restricted hypersurface singular locus. -/
theorem exists_rational_contact_fiber {m n : ℕ}
    (F : RationalPolynomial n) (P Q : Fin n → GeometricPolynomial m)
    (Y : Set (GeometricPoint m)) (hY : AlgebraicallyClosedSet Y)
    (hiY : GeometricallyIrreducible Y)
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (hdom : geometricClosure (polynomialMap Q '' Y) = Z)
    (hcone : IsAffineCone Z)
    (hinc : ∀ y ∈ Y, (polynomialMap P y, polynomialMap Q y) ∈
      affineSectionSingularIncidence (geometricPolynomial F))
    (W : Set (GeometricPoint m)) (hW : RelativelyOpenSet Y W)
    (hdW : geometricClosure W = Y)
    (hnormal : ∀ y ∈ W, polynomialMap Q y ≠ 0)
    (hgradient : ∀ y ∈ W, gradient (geometricPolynomial F) (polynomialMap P y) ≠ 0) :
    ∃ (U : Set (GeometricPoint m)) (V : Set (GeometricPoint n)) (q : Fin n → ℚ),
      RelativelyOpenSet Y U ∧ U ⊆ W ∧ geometricClosure U = Y ∧ U.Nonempty ∧
      RelativelyOpenSet Z V ∧ V.Nonempty ∧ geometricClosure V = Z ∧
      V ⊆ polynomialMap Q '' U ∧ q ≠ 0 ∧ rationalEmbedding q ∈ V ∧
      affineDimension Z =
        (finrank GeometricField (affineTangentSpace Z (rationalEmbedding q)) : Dimension) ∧
      ∃ (d : ℕ) (B : Matrix (Fin n) (Fin d) ℚ),
        d = finrank GeometricField
          (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q))) ∧
        Function.Injective B.mulVec ∧
        Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec ∧
        LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin =
          coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)) ∧
        {y | y ∈ U ∧ polynomialMap Q y = rationalEmbedding q}.Nonempty ∧
        ∀ y ∈ U, polynomialMap Q y = rationalEmbedding q →
          polynomialMap P y ∈ (B.map (algebraMap ℚ GeometricField)).mulVec ''
            hypersurfaceSingularLocus (geometricPolynomial (restrict B F)) := by
  obtain ⟨U, hU, hUW, hdU, hnU, hcontact⟩ :=
    exists_dense_open_restricted_singular_images (geometricPolynomial F) P Q Y hY hiY
      hinc W hW hdW hnormal hgradient (hdom ▸ hcone)
  obtain ⟨V, hV, hnV, hdV, hVimage⟩ :=
    UnconditionalChevalleyOpen.exists_dense_open_subset_image_of_open Q Y U hY hiY hU hnU
  rw [hdom] at hV hdV
  obtain ⟨q, hqV, hqsmooth⟩ :=
    exists_rational_smooth_point_in_component_open C Z hC hZ V hV hnV
  obtain ⟨y, hyU, hyq⟩ := hVimage hqV
  have hqne : q ≠ 0 := by
    intro hqzero
    apply hnormal y (hUW hyU)
    simpa only [hqzero, rationalEmbedding_zero] using hyq
  obtain ⟨B, hB, hBG, hBrange⟩ := tangent_annihilator_rational_matrix_frame C Z hC hZ q
  refine ⟨U, V, q, hU, hUW, hdU, hnU, hV, hnV, hdV, hVimage,
    hqne, hqV, hqsmooth, _, B, rfl, hB, hBG, hBrange, ⟨y, hyU, hyq⟩, ?_⟩
  intro z hz hzq
  have hBrange' : LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin =
      coordinatePairing.orthogonal
        (affineTangentSpace (geometricClosure (polynomialMap Q '' Y)) (polynomialMap Q z)) := by
    simpa only [hdom, hzq] using hBrange
  have hc := hcontact z hz _ (B.map (algebraMap ℚ GeometricField)) hBrange'
  have hrestriction : restrict (B.map (algebraMap ℚ GeometricField)) (geometricPolynomial F) =
      geometricPolynomial (restrict B F) :=
    (map_restrict (algebraMap ℚ GeometricField) B F).symm
  rwa [hrestriction] at hc

end CubicTenVariables.TerminalRationalContact
