import HessianTheorem11.SaturatedMixedRadical
import HessianTheorem11.SaturatedFourDimensionalData

/-! The scalar alternative's actual common normal radical, with every
mixed pairing identified with the original cubic's constructed map e. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

theorem fourE_common_normal_radical (GR : GenericRankOpenInput) (SA : FormalSmoothArcInput)
    (hF : F.IsHomogeneous 3)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (Z : Set (GeometricPoint 13)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hx : x ∈ Z)
    (hT : T = affineTangentSpace Z x)
    (hdim : affineDimension Z = (finrank GeometricField T : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)))
    (η : Fin 2) (hη : η ≠ D.radial)
    (he : finrank GeometricField (LinearMap.range (D.fourE hF η)) = 2) :
    ∀ z ∈ LinearMap.ker (D.fourE hF η), ∀ a y,
      polarization F (D.radicalMatrix.mulVec z) (D.radicalMatrix.mulVec a) y = 0 := by
  obtain ⟨G,hG⟩ := D.normalCross_full_rank_on_generic_open GR hF hker hann hdom
  obtain ⟨a₀,ha₀⟩ := G.nonempty
  exact D.common_normal_radical_of_pairing_rank_two SA hF hann hker Z hZ hirred hx hT hdim
    hmax η hη a₀ (hG a₀ ha₀) D.fourBeta D.fourBeta_symm D.fourBeta_nondegenerate
    (D.fourE hF η) he (D.fourE_pairing hF η)

end CoisotropicBasis.Data
end HessianTheorem11
