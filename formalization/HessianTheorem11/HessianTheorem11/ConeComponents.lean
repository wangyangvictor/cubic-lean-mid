import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.KernelSaturation

/-! A component of an affine cone is a cone, derived from the existing
universal connected-torus component input by adjoining an empty block.
No additional geometric input is introduced. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem GeometricallyIrreducible.linearMap_image
    {Z : Set (σ → GeometricField)} (hZ : GeometricallyIrreducible Z)
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField)) :
    GeometricallyIrreducible (L '' Z) := by
  simpa only [polynomialMap_linearCoordinatePolynomials] using
    hZ.polynomialMap_image (linearCoordinatePolynomials L)

theorem IsIrreducibleComponent.linearEquiv_image
    {X Z : Set (σ → GeometricField)} (hZ : IsIrreducibleComponent X Z)
    (L : (σ → GeometricField) ≃ₗ[GeometricField] (τ → GeometricField)) :
    IsIrreducibleComponent (L '' X) (L '' Z) := by
  refine ⟨algebraicallyClosedSet_linearMap_image L.toLinearMap L.injective hZ.closed,
    hZ.irreducible.linearMap_image L.toLinearMap, Set.image_mono hZ.subset, ?_⟩
  intro W hW hi hsub hWX
  have hc : AlgebraicallyClosedSet (L.symm '' W) :=
    algebraicallyClosedSet_linearMap_image L.symm.toLinearMap L.symm.injective hW
  have hir := hi.linearMap_image L.symm.toLinearMap
  have hs : Z ⊆ L.symm '' W := by
    intro z hz
    exact ⟨L z, hsub ⟨z,hz,rfl⟩, L.symm_apply_apply z⟩
  have hx : L.symm '' W ⊆ X := by
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨x,hx,hxw⟩ := hWX hw
    rw [← hxw, L.symm_apply_apply]
    exact hx
  have he := hZ.maximal (L.symm '' W) hc hir hs hx
  have hh := congrArg (Set.image L) he
  simpa only [Set.image_image, LinearEquiv.apply_symm_apply,
    Set.image_id', Function.comp_def] using hh

/-- Add an empty second affine block, using an actual linear equivalence. -/
def emptyBlockEquiv (n : ℕ) : GeometricPoint n ≃ₗ[GeometricField] PairPoint n 0 where
  toFun x := pairPoint x 0
  invFun := pairLeft
  left_inv _ := rfl
  right_inv x := by
    ext i
    cases i with
    | inl i => rfl
    | inr i => exact Fin.elim0 i
  map_add' x y := by
    ext i
    cases i with
    | inl i => rfl
    | inr i => exact Fin.elim0 i
  map_smul' a x := by
    ext i
    cases i with
    | inl i => rfl
    | inr i => exact Fin.elim0 i

theorem emptyBlock_image_bicone {n : ℕ} {X : Set (GeometricPoint n)}
    (hX : IsAffineCone X) : IsBicone (emptyBlockEquiv n '' X) := by
  rintro p ⟨x,hx,rfl⟩ a b
  refine ⟨a • x, hX a x hx, ?_⟩
  ext i
  cases i with
  | inl i => rfl
  | inr i => exact Fin.elim0 i

/-- The general affine cone component theorem follows from the already
permitted bicone component theorem, with a zero-dimensional second block. -/
theorem IsIrreducibleComponent.isAffineCone
    (AG : AffineComponentsInput) {n : ℕ} {X Z : Set (GeometricPoint n)}
    (hZ : IsIrreducibleComponent X Z) (hX : AlgebraicallyClosedSet X)
    (hcone : IsAffineCone X) : IsAffineCone Z := by
  let E := emptyBlockEquiv n
  have hc : AlgebraicallyClosedSet (E '' X) :=
    algebraicallyClosedSet_linearMap_image E.toLinearMap E.injective hX
  have hi := hZ.linearEquiv_image E
  have hb := AG.bicone_component (E '' X) (E '' Z) hc (emptyBlock_image_bicone hcone) hi
  have hs := hb.isAffineCone.linear_image E.symm.toLinearMap
  have he : E.symm.toLinearMap '' (E '' Z) = Z := by
    ext z
    constructor
    · rintro ⟨w,⟨v,hv,rfl⟩,h⟩
      simpa using h ▸ hv
    · intro hz
      exact ⟨E z, ⟨z,hz,rfl⟩, E.symm_apply_apply z⟩
  rw [he] at hs
  exact hs

end HessianTheorem11
