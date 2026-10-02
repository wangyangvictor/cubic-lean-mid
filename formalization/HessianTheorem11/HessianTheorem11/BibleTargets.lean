import HessianTheorem11.BibleCore
import HessianTheorem11.BibleLowRank
import HessianTheorem11.BibleRestrictions
import HessianTheorem11.BibleVertex
import HessianTheorem11.BibleHyperplanes
import HessianTheorem11.BibleProjectiveGeometry

/-! Exact targets for every assertion of Theorem I.1.1 of bible.pdf,
printed page 1. Hyperplane sections are the actual restrictions along all
injective frames; exists_hyperplane_frame and frame_hypersurface_image
identify these with all actual projective hyperplanes. -/

noncomputable section
namespace HessianTheorem11.BibleTargets
open MvPolynomial Module PolynomialRestriction BibleHyperplanes
  BibleProjectiveGeometry BibleVertex BibleRestrictions

def sectionPolynomial (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) : GeometricPolynomial 11 :=
  restrict B (geometricPolynomial F.polynomial)

def sectionVertex (F : AnisotropicCubic 12)
    (B : Matrix (Fin 12) (Fin 11) GeometricField) :
    Submodule GeometricField (GeometricPoint 11) :=
  affineVertex (sectionPolynomial F B)
    (homogeneous_restrict B _ (geometric_homogeneous F.homogeneous))

/-- Nineteen separately tracked assertions, using actual polynomials,
coordinate rings, full Hessians, projective charts, subspaces and restrictions.
The universal vertex-descent assertion is stronger than its use for sections. -/
structure TheoremI11 (F : AnisotropicCubic 12) : Prop where
  geometricallyIntegral : IsDomain (cubicCoordinateRing F.polynomial)
  notProjectiveCone : ¬ IsProjectiveCone (geometricPolynomial F.polynomial)
  hessianInjective : Function.Injective (hessian (geometricPolynomial F.polynomial))
  determinantNonzero : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0
  rankOneLocus :
    {x ∈ cubicLocus F.polynomial | (hessian (geometricPolynomial F.polynomial) x).rank ≤ 1} = {0}
  rankTwoDimension :
    affineDimension {x ∈ cubicLocus F.polynomial |
      (hessian (geometricPolynomial F.polynomial) x).rank ≤ 2} ≤ 2
  incidenceDimension : HessianTheorem11.incidenceDimension F.polynomial ≤ 15
  singularDimension : HessianTheorem11.singularDimension F.polynomial ≤ 6
  genericRank : 8 ≤ genericHessianRank F.polynomial
  incidenceLowerBound :
    ((11 + (12 - genericHessianRank F.polynomial) : ℕ) : Dimension) ≤
      HessianTheorem11.incidenceDimension F.polynomial
  geometricSectionsIntegral :
    ∀ (B : Matrix (Fin 12) (Fin 11) GeometricField), Function.Injective B.mulVec →
      Irreducible (sectionPolynomial F B) ∧
      IsDomain (GeometricPolynomial 11 ⧸ Ideal.span {sectionPolynomial F B})
  geometricSectionsSingular :
    ∀ (B : Matrix (Fin 12) (Fin 11) GeometricField), Function.Injective B.mulVec →
      projectiveDimension (singularCone (sectionPolynomial F B)) ≤ 6
  rationalSectionsSingular :
    ∀ (B : Matrix (Fin 12) (Fin 11) ℚ), Function.Injective B.mulVec →
      projectiveDimension (singularLocus (restrict B F.polynomial)) ≤ 4
  sectionVertexDimension :
    ∀ (B : Matrix (Fin 12) (Fin 11) GeometricField), Function.Injective B.mulVec →
      finrank GeometricField (sectionVertex F B) ≤ 2 ∧
      projectiveDimension (sectionVertex F B : Set (GeometricPoint 11)) ≤ 1
  vertexDefinedOver :
    ∀ (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
      (p : MvPolynomial (Fin 11) K) (hp : p.IsHomogeneous 3),
      affineVertex (map (algebraMap K L) p) (hp.map _) =
        Submodule.span L ((fun v : Fin 11 → K => fun i => algebraMap K L (v i)) ''
          (affineVertex p hp : Set (Fin 11 → K)))
  restrictionsAnisotropic :
    ∀ M : Submodule ℚ (Fin 12 → ℚ), 4 ≤ finrank ℚ M →
      Anisotropic (subspaceCubic F M).polynomial
  restrictionsSingular :
    ∀ M : Submodule ℚ (Fin 12 → ℚ), 4 ≤ finrank ℚ M →
      HessianTheorem11.singularDimension (subspaceCubic F M).polynomial ≤
        ((2 * finrank ℚ M - 3) / 3 : ℕ)
  restrictionsSingularStrong :
    ∀ M : Submodule ℚ (Fin 12 → ℚ), 11 ≤ finrank ℚ M →
      HessianTheorem11.singularDimension (subspaceCubic F M).polynomial ≤
        (finrank ℚ M - 6 : ℕ)
  singularLinearSpaces :
    ∀ L : Submodule GeometricField (GeometricPoint 12),
      (L : Set (GeometricPoint 12)) ⊆ singularLocus F.polynomial →
      3 * finrank GeometricField L ≤ 12

end HessianTheorem11.BibleTargets
