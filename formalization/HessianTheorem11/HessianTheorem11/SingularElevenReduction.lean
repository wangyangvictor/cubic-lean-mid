import HessianTheorem11.IntrinsicTangentRank
import HessianTheorem11.SingularTangentUnion

/-! The final geometric contradiction for the six-dimensional singular
exception in eleven variables. The sole remaining local hypothesis is an
actual rank-four restricted Hessian witness; its construction is the
separate quadratic-map dominance and deficient-span argument. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

theorem six_dimensional_singular_component_impossible_of_rank_four
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    (AD : AffineHypersurfaceDimensionInput) (KI : KernelBundleInput)
    (MR : GenericMatrixRankInput)
    (F : GeometricPolynomial 11) (hF : F.IsHomogeneous 3) (hFi : Irreducible F)
    (hgeneric : 10 ≤ geometricCubicGenericRank F)
    (Z : Set (GeometricPoint 11)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hsing : ∀ z ∈ Z, gradient F z = 0)
    (hdim : affineDimension Z = 6)
    (G : GenericRankOpen Z (fun i => pderiv i F) (hessianLinearMap F hF))
    (hrank : ∀ x ∈ G.openSet, (hessian F x).rank = 5)
    (hfour : ∃ x ∈ G.openSet, ∃ v ∈ affineTangentSpace Z x,
      4 ≤ finrank GeometricField (LinearMap.range
        ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x)))) : False := by
  have hbase : G.baseDimension = 6 := by
    have he := G.dimension_base.symm.trans hdim
    exact_mod_cast he
  have ht (x : GeometricPoint 11) (hx : x ∈ G.openSet) :
      finrank GeometricField (affineTangentSpace Z x) = 6 := by
    rw [G.smooth x hx, hbase]
  have hsmooth (x : GeometricPoint 11) (hx : x ∈ G.openSet) :
      affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension) := by
    rw [ht x hx]
    exact hdim
  have hT (x : GeometricPoint 11) (hx : x ∈ G.openSet) :
      affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq (affineTangentSpace_le_hessian_ker F Z hsing x)
    have he := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
    change (hessian F x).rank + _ = finrank GeometricField (GeometricPoint 11) at he
    rw [hrank x hx, show finrank GeometricField (GeometricPoint 11) = 11 by simp] at he
    rw [ht x hx]
    omega
  obtain ⟨x, hx, v, hv, hv4⟩ := hfour
  have hr := generic_rank_le_of_singular_tangent_union KB SA AD KI MR F hF hFi Z G.openSet
    hZ hirred G.isOpen G.subset G.dense hsing hsmooth hT G.nullity G.kernel_dimension
    x hx v hv (by rw [ht x hx]; omega) 9 (by
      intro y hy w hw
      exact tangent_hessian_rank_le_nine_intrinsic SA MR F hF Z hZ hirred hsing
        y (G.subset hy) (hsmooth y hy) (ht y hy) (hrank y hy) w hw)
  omega

end HessianTheorem11
