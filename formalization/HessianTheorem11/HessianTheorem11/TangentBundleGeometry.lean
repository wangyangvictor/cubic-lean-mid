import HessianTheorem11.Concentration
import HessianTheorem11.SingularFormalArc
import HessianTheorem11.TangentBundleLinearAlgebra

/-! The general tangent formula for a constant-rank kernel bundle and the
dimension of the image of its actual projection. The cubic specialization
uses separately proved polarization and formal-arc identities. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module TangentBundleLinearAlgebra

def pencilVariation {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (v : GeometricPoint b) : GeometricPoint n →ₗ[GeometricField] GeometricPoint a where
  toFun u := (M u).mulVec v
  map_add' u w := by rw [map_add, Matrix.add_mulVec]
  map_smul' c u := by rw [LinearMap.map_smul, Matrix.smul_mulVec]; rfl

/-- General constant-rank kernel-bundle tangent geometry. At a smooth
point `(x,v)`, its tangent vectors are precisely `(u,w)` satisfying
`u∈T_x U` and `M(x)w+M(u)v=0`. The rank of the second projection on this
actual tangent space is at most the dimension of its image closure.
The base dimension, number of matrix rows, and number of columns are
independent, and no symmetry or cubic structure is required. -/
structure KernelBundleTangentImageInput : Prop where
  dimension_lower_bound : ∀ {n a b : ℕ}
    (M : GeometricPoint n →ₗ[GeometricField] Matrix (Fin a) (Fin b) GeometricField)
    (U O : Set (GeometricPoint n)),
    AlgebraicallyClosedSet U → GeometricallyIrreducible U →
    RelativelyOpenSet U O → geometricClosure O = U →
    ∀ ell : ℕ, (∀ y ∈ O, finrank GeometricField (LinearMap.ker (M y).mulVecLin) = ell) →
    ∀ x ∈ O, affineDimension U =
      (finrank GeometricField (affineTangentSpace U x) : Dimension) →
    ∀ v : GeometricPoint b, (M x).mulVec v = 0 →
      (finrank GeometricField (LinearMap.range
        (tangentProjection (M x).mulVecLin (pencilVariation M v) (affineTangentSpace U x))) : Dimension) ≤
      affineDimension (geometricClosure (pairRight '' kernelBundle M O))

theorem pencilVariation_hessian {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (v : GeometricPoint n) :
    pencilVariation (hessianLinearMap F hF) v = (hessian F v).mulVecLin := by
  apply LinearMap.ext
  intro u
  exact hessian_polarization hF u v

/-- The actual `dim T + rank(second normal differential)` lower bound
for the tangent-space union when T equals the Hessian kernel. -/
theorem tangent_union_dimension_lower_bound
    (KB : KernelBundleTangentImageInput) (SA : FormalSmoothArcInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z O : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z) (hO : RelativelyOpenSet Z O)
    (hdense : geometricClosure O = Z)
    (hsing : ∀ z ∈ Z, gradient F z = 0)
    (ell : ℕ) (hell : ∀ y ∈ O, finrank GeometricField (LinearMap.ker (hessian F y).mulVecLin) = ell)
    (x : GeometricPoint n) (hx : x ∈ O) (hxZ : x ∈ Z)
    (hdim : affineDimension Z = (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (hT : affineTangentSpace Z x = LinearMap.ker (hessian F x).mulVecLin)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    ((finrank GeometricField (affineTangentSpace Z x) +
      finrank GeometricField (LinearMap.range
        ((hessian F v).mulVecLin.domRestrict (affineTangentSpace Z x))) : ℕ) : Dimension) ≤
      affineDimension (geometricClosure (pairRight '' kernelBundle (hessianLinearMap F hF) O)) := by
  have hk : (hessian F x).mulVec v = 0 := by
    rw [hT] at hv
    exact hv
  have hbound := KB.dimension_lower_bound (hessianLinearMap F hF) Z O hZ hirred hO hdense
    ell hell x hx hdim v hk
  rw [pencilVariation_hessian] at hbound
  change (finrank GeometricField (LinearMap.range
    (tangentProjection (hessian F x).mulVecLin (hessian F v).mulVecLin
      (affineTangentSpace Z x))) : Dimension) ≤ _ at hbound
  have hA := SingularFormalArc.hessian_tangent_image_le_range SA F hF Z hZ hirred hsing
    x hxZ hdim v hv
  rw [hT] at hA
  have he := finrank_range_tangentProjection (hessian F x).mulVecLin (hessian F v).mulVecLin hA
  rw [hT, he] at hbound
  rw [hT]
  exact hbound

end HessianTheorem11
