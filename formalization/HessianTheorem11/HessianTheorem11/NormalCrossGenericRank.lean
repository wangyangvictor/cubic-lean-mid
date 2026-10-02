import HessianTheorem11.RadicalPencilCoordinates
import HessianTheorem11.KernelQuadraticDominance

/-! Dominance of the actual kernel-gradient map gives a dense open of
full-rank normal cross blocks, and extends polynomial identities from it. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module

theorem affineDimension_submodule_from_generic_rank (GR : GenericRankOpenInput)
    {n : ℕ} (S : Submodule GeometricField (GeometricPoint n)) :
    affineDimension (S : Set (GeometricPoint n)) = (finrank GeometricField S : Dimension) := by
  have h := affineDimension_linearMap_image (submoduleCoordinateMap S)
    (submoduleCoordinateMap_injective S) Set.univ
  rw [Set.image_univ, submoduleCoordinateMap_range,
    affineDimension_univ_from_generic_rank GR] at h
  exact h

namespace CoisotropicBasis.Data
variable {n m d q : ℕ} {F : GeometricPolynomial n} {x : GeometricPoint n}
  {T : Submodule GeometricField (GeometricPoint n)}
  (D : Data (hessianBilinear F x) T x m d q)

include D in
theorem conormal_finrank : finrank GeometricField
    ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T) = d := by
  have h := LinearMap.BilinForm.finrank_orthogonal
    (coordinatePairing_nondegenerate (K := GeometricField) (n := n))
    coordinatePairing_reflexive T
  have hc := D.codimension
  simp only [Module.finrank_pi, Fintype.card_fin] at h hc
  omega

theorem normalCross_full_rank_on_generic_open (GR : GenericRankOpenInput)
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n))) =
      ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T : Set (GeometricPoint n))) :
    ∃ G : GenericRankOpen Set.univ D.radicalGradient
        (quadraticJacobianLinearMap D.radicalGradient (D.radicalGradient_homogeneous hF)),
      ∀ a ∈ G.openSet, (D.normalCross (D.radicalMatrix.mulVec a)).rank = d := by
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    D.radicalGradient (quadraticJacobianLinearMap D.radicalGradient (D.radicalGradient_homogeneous hF))
  have hg : G.imageDimension = d := by
    have he := G.dimension_image
    rw [D.radicalGradient_image, hdom, affineDimension_submodule_from_generic_rank GR,
      D.conormal_finrank] at he
    exact_mod_cast he.symm
  refine ⟨G,?_⟩
  intro a ha
  rw [D.normalCross_rank_eq_radicalGradient_jacobian hF hker hann a,
    G.quadratic_rank_eq a ha, hg]

theorem polynomial_identity_of_full_normalCross_rank (GR : GenericRankOpenInput)
    (hF : F.IsHomogeneous 3)
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hann : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin, polarization F t u v = 0)
    (hdom : geometricClosure (gradient F ''
      (LinearMap.ker (hessian F x).mulVecLin : Set (GeometricPoint n))) =
      ((coordinatePairing (K := GeometricField) (n := n)).orthogonal T : Set (GeometricPoint n)))
    (p : GeometricPolynomial m)
    (hp : ∀ a, (D.normalCross (D.radicalMatrix.mulVec a)).rank = d → eval a p = 0) : p = 0 := by
  obtain ⟨G,hG⟩ := D.normalCross_full_rank_on_generic_open GR hF hker hann hdom
  by_contra hn
  obtain ⟨a,ha,hpa⟩ := G.exists_polynomial_ne_zero p hn
  exact hpa (hp a (hG a ha))

end CoisotropicBasis.Data
end HessianTheorem11
