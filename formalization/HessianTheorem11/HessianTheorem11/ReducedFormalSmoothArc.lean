import HessianTheorem11.ReducedSmoothVectorField
import HessianTheorem11.ReducedDerivationExponential

/-! The full former formal-smooth-arc input is proved from the retained
generic-rank theorem. A Jacobian adjugate extends the tangent vector to an
ideal-preserving polynomial derivation, whose exponential supplies the arc. -/

noncomputable section
namespace HessianTheorem11.ReducedFormalSmoothArc

/-- Fully proved replacement for SA. No formal implicit-function,
local-complete-intersection, or formal-smoothness input is used. -/
def formalSmoothArcInput (GR : GenericRankOpenInput) : FormalSmoothArcInput where
  lift := by
    intro n Z hZ hirred x hx hsmooth v hv
    obtain ⟨D, hI, hD⟩ := ReducedSmoothVectorField.exists_tangent_derivation
      GR Z hZ hirred x hx hsmooth v hv
    obtain ⟨γ, hγ0, hγ1, hγI⟩ :=
      ReducedDerivationExponential.exists_formal_arc_of_derivation D
        (MvPolynomial.vanishingIdeal GeometricField Z) hI x v
        (fun p hp => hp x hx) hD
    exact ⟨γ, hγ0, hγ1, hγI⟩

end HessianTheorem11.ReducedFormalSmoothArc
