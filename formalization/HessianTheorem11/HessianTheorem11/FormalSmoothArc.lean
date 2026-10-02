import HessianTheorem11.AffineGeometry
import HessianTheorem11.SingularLinearAlgebra
import Mathlib.RingTheory.PowerSeries.Basic

/-! The universal formal smoothness input used for local tangent jets.
It applies to arbitrary affine varieties and their actual vanishing ideals. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

def arcEval {n : ℕ} (γ : Fin n → PowerSeries GeometricField) :
    GeometricPolynomial n →+* PowerSeries GeometricField :=
  eval₂Hom PowerSeries.C γ

def arcCoefficient {K : Type*} [Semiring K] {n : ℕ}
    (γ : Fin n → PowerSeries K) (d : ℕ) : Fin n → K :=
  fun i => PowerSeries.coeff d (γ i)

/-- A tangent vector at a smooth point of an arbitrary reduced irreducible
affine variety lifts to a formal arc through that point. Smoothness at a
geometric closed point is expressed by equality of tangent and variety
dimension. Every actual equation of the variety vanishes on the arc. -/
structure FormalSmoothArcInput : Prop where
  lift : ∀ {n : ℕ} (Z : Set (GeometricPoint n)),
    AlgebraicallyClosedSet Z → GeometricallyIrreducible Z →
    ∀ x ∈ Z, affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension) →
    ∀ v ∈ affineTangentSpace Z x,
      ∃ γ : Fin n → PowerSeries GeometricField,
        arcCoefficient γ 0 = x ∧ arcCoefficient γ 1 = v ∧
        ∀ P ∈ vanishingIdeal GeometricField Z, arcEval γ P = 0

end HessianTheorem11
