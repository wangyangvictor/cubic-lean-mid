import HessianTheorem11.SaturatedScalarCommonRadical
import HessianTheorem11.SaturatedScalarTangent
import HessianTheorem11.ScalarRadicalExclusion
import HessianTheorem11.ScalarZeroSubspace

/-! The scalar alternative is excluded for the actual cubic: the common
zero subspace is constructed from e and alpha, and both tensor vanishings
needed for the destabilizing weight are proved, not supplied as certificates. -/
noncomputable section
namespace HessianTheorem11
open Module
namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

theorem four_scalar_alternative_impossible
    (GR : GenericRankOpenInput) (SA : FormalSmoothArcInput)
    (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (Z : Set (GeometricPoint 13)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hx : x ∈ Z)
    (hT : T = affineTangentSpace Z x)
    (hdim : affineDimension Z = (finrank GeometricField T : Dimension))
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint 13))) =
      ((coordinatePairing (K := GeometricField) (n := 13)).orthogonal T : Set (GeometricPoint 13)))
    (hC : ∀ a ∈ LinearMap.ker (hessian F x).mulVecLin, D.isotropicGramAt a = 0)
    (η : Fin 2) (hη : η ≠ D.radial)
    (he : finrank GeometricField (LinearMap.range (D.fourE hF η)) = 2)
    (α : LinearMap.ker (D.fourE hF η) →ₗ[GeometricField] GeometricField)
    (hscalar : ∀ z : LinearMap.ker (D.fourE hF η),
      D.fourM hF z = α z • LinearMap.id) : False := by
  let U := scalarZeroSubspace (D.fourE hF η) α
  have hUker : U ≤ LinearMap.ker (D.fourE hF η) := scalarZeroSubspace_le_ker _ _
  have hUA := D.fourE_common_normal_radical GR SA hF hann hker Z hZ hirred hx hT hdim
    hmax hdom η hη he
  have hUT : ∀ z ∈ U, ∀ t ∈ T, ∀ u ∈ T,
      polarization F (D.radicalMatrix.mulVec z) t u = 0 := by
    intro z hz
    have hM : D.fourM hF z = 0 := by
      have hs := hscalar ⟨z,hUker hz⟩
      rw [scalarZeroSubspace_value _ _ z hz,zero_smul] at hs
      exact hs
    exact D.scalar_tangent_pair_zero hF hker η hη z (hUker hz) hM
      (hC _ (D.radicalMatrix_mem_kernel z)) (hUA z (hUker hz))
  have hz : U = ⊥ := D.scalar_common_radical_eq_bot hF hsemi hker hann U
    (fun z hz => hUA z (hUker hz)) hUT
  have hd := scalarZeroSubspace_finrank_ge_two (D.fourE hF η) α (by simp) he
  change 2 ≤ finrank GeometricField U at hd
  rw [hz] at hd
  simpa using hd

end CoisotropicBasis.Data
end HessianTheorem11
