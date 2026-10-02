import HessianTheorem11.AffineGeometry
import Mathlib.Algebra.MvPolynomial.Funext

/-! Polynomial changes of affine coordinates and their effects on actual
vanishing ideals, affine dimension, and algebraic closure. No external
geometric input is used. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

variable {σ τ υ : Type*}

/-- An invertible polynomial change from `σ`-coordinates to `τ`-coordinates. -/
structure PolynomialCoordinateEquiv (σ τ : Type*) where
  forward : τ → MvPolynomial σ GeometricField
  inverse : σ → MvPolynomial τ GeometricField
  forward_inverse : ∀ i, aeval forward (inverse i) = X i
  inverse_forward : ∀ j, aeval inverse (forward j) = X j

namespace PolynomialCoordinateEquiv

variable (e : PolynomialCoordinateEquiv σ τ)

def forwardMap : (σ → GeometricField) → (τ → GeometricField) :=
  polynomialMap e.forward

def inverseMap : (τ → GeometricField) → (σ → GeometricField) :=
  polynomialMap e.inverse

@[simp] theorem inverseMap_forwardMap (x : σ → GeometricField) :
    e.inverseMap (e.forwardMap x) = x := by
  funext i
  change eval (polynomialMap e.forward x) (e.inverse i) = x i
  rw [eval_polynomialMap, e.forward_inverse, eval_X]

@[simp] theorem forwardMap_inverseMap (y : τ → GeometricField) :
    e.forwardMap (e.inverseMap y) = y := by
  funext j
  change eval (polynomialMap e.inverse y) (e.forward j) = y j
  rw [eval_polynomialMap, e.inverse_forward, eval_X]

def pointEquiv : (σ → GeometricField) ≃ (τ → GeometricField) where
  toFun := e.forwardMap
  invFun := e.inverseMap
  left_inv := e.inverseMap_forwardMap
  right_inv := e.forwardMap_inverseMap

@[simp] theorem pointEquiv_apply (x : σ → GeometricField) :
    e.pointEquiv x = e.forwardMap x := rfl

def symm : PolynomialCoordinateEquiv τ σ where
  forward := e.inverse
  inverse := e.forward
  forward_inverse := e.inverse_forward
  inverse_forward := e.forward_inverse

@[simp] theorem symm_forwardMap : e.symm.forwardMap = e.inverseMap := rfl

@[simp] theorem inverseMap_image_forwardMap (Z : Set (σ → GeometricField)) :
    e.inverseMap '' (e.forwardMap '' Z) = Z := by
  rw [Set.image_image]
  simp only [inverseMap_forwardMap, Set.image_id']

@[simp] theorem forwardMap_image_inverseMap (Z : Set (τ → GeometricField)) :
    e.forwardMap '' (e.inverseMap '' Z) = Z := by
  rw [Set.image_image]
  simp only [forwardMap_inverseMap, Set.image_id']

/-- Pullback of polynomial functions, contravariant to the point map. -/
def pullbackAlgEquiv : MvPolynomial τ GeometricField ≃ₐ[GeometricField]
    MvPolynomial σ GeometricField :=
  AlgEquiv.ofAlgHom (aeval e.forward) (aeval e.inverse)
    (by apply MvPolynomial.algHom_ext; intro i; simpa using e.forward_inverse i)
    (by apply MvPolynomial.algHom_ext; intro j; simpa using e.inverse_forward j)

@[simp] theorem pullbackAlgEquiv_apply (F : MvPolynomial τ GeometricField) :
    e.pullbackAlgEquiv F = aeval e.forward F := rfl

@[simp] theorem pullbackAlgEquiv_symm_apply (F : MvPolynomial σ GeometricField) :
    e.pullbackAlgEquiv.symm F = aeval e.inverse F := rfl

theorem vanishingIdeal_image (Z : Set (σ → GeometricField)) :
    vanishingIdeal GeometricField (e.forwardMap '' Z) =
      (vanishingIdeal GeometricField Z).map e.pullbackAlgEquiv.symm.toRingHom := by
  exact (vanishingIdeal_polynomialMap_image e.forward Z).trans
    (Ideal.map_symm e.pullbackAlgEquiv.toRingEquiv).symm

theorem affineDimension_image (Z : Set (σ → GeometricField)) :
    affineDimension (e.forwardMap '' Z) = affineDimension Z := by
  exact (ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquiv (vanishingIdeal GeometricField Z)
      (vanishingIdeal GeometricField (e.forwardMap '' Z))
      e.pullbackAlgEquiv.symm.toRingEquiv (e.vanishingIdeal_image Z))).symm

theorem geometricClosure_image (Z : Set (σ → GeometricField)) :
    geometricClosure (e.forwardMap '' Z) = e.forwardMap '' geometricClosure Z := by
  apply le_antisymm
  · intro y hy
    refine ⟨e.inverseMap y, ?_, e.forwardMap_inverseMap y⟩
    have h := polynomialMap_image_closure_subset e.inverse (e.forwardMap '' Z)
    have hi := h (Set.mem_image_of_mem e.inverseMap hy)
    change e.inverseMap y ∈ geometricClosure (e.inverseMap '' (e.forwardMap '' Z)) at hi
    simpa only [inverseMap_image_forwardMap] using hi
  · exact polynomialMap_image_closure_subset e.forward Z

theorem algebraicallyClosedSet_image_iff (Z : Set (σ → GeometricField)) :
    AlgebraicallyClosedSet (e.forwardMap '' Z) ↔ AlgebraicallyClosedSet Z := by
  unfold AlgebraicallyClosedSet
  rw [e.geometricClosure_image]
  exact e.pointEquiv.injective.image_injective.eq_iff

theorem geometricallyIrreducible_image_iff (Z : Set (σ → GeometricField)) :
    GeometricallyIrreducible (e.forwardMap '' Z) ↔ GeometricallyIrreducible Z := by
  constructor
  · intro h
    have hi := h.polynomialMap_image e.inverse
    change GeometricallyIrreducible (e.inverseMap '' (e.forwardMap '' Z)) at hi
    simpa only [inverseMap_image_forwardMap] using hi
  · exact fun h => h.polynomialMap_image e.forward

end PolynomialCoordinateEquiv

/-- Coordinate polynomials of an arbitrary linear map between finite affine
coordinate spaces. Its coefficient in `X i` is the `j`-coordinate of the image
of the standard basis vector `i`. -/
def linearCoordinatePolynomials [Fintype σ]
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField)) :
    τ → MvPolynomial σ GeometricField :=
  fun j => ∑ i, C (L ((Pi.basisFun GeometricField σ) i) j) * X i

@[simp] theorem polynomialMap_linearCoordinatePolynomials [Fintype σ]
    (L : (σ → GeometricField) →ₗ[GeometricField] (τ → GeometricField))
    (x : σ → GeometricField) : polynomialMap (linearCoordinatePolynomials L) x = L x := by
  funext j
  change eval x (∑ i, C (L ((Pi.basisFun GeometricField σ) i) j) * X i) = L x j
  simp only [eval_sum, eval_mul, eval_C, eval_X]
  have h := congrArg (fun z => L z j) ((Pi.basisFun GeometricField σ).sum_repr x)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.basisFun_repr, mul_comm] using h

namespace PolynomialCoordinateEquiv

/-- Every actual linear equivalence of finite coordinate spaces induces an
invertible polynomial coordinate change. -/
def ofLinearEquiv [Fintype σ] [Fintype τ]
    (L : (σ → GeometricField) ≃ₗ[GeometricField] (τ → GeometricField)) :
    PolynomialCoordinateEquiv σ τ where
  forward := linearCoordinatePolynomials L.toLinearMap
  inverse := linearCoordinatePolynomials L.symm.toLinearMap
  forward_inverse := by
    intro i
    apply MvPolynomial.funext
    intro x
    rw [← eval_polynomialMap, polynomialMap_linearCoordinatePolynomials]
    change polynomialMap (linearCoordinatePolynomials L.symm.toLinearMap) (L x) i = eval x (X i)
    rw [polynomialMap_linearCoordinatePolynomials]
    simp
  inverse_forward := by
    intro j
    apply MvPolynomial.funext
    intro y
    rw [← eval_polynomialMap, polynomialMap_linearCoordinatePolynomials]
    change polynomialMap (linearCoordinatePolynomials L.toLinearMap) (L.symm y) j = eval y (X j)
    rw [polynomialMap_linearCoordinatePolynomials]
    simp

@[simp] theorem ofLinearEquiv_forwardMap [Fintype σ] [Fintype τ]
    (L : (σ → GeometricField) ≃ₗ[GeometricField] (τ → GeometricField)) :
    (ofLinearEquiv L).forwardMap = L := by
  funext x
  exact polynomialMap_linearCoordinatePolynomials L.toLinearMap x

@[simp] theorem ofLinearEquiv_inverseMap [Fintype σ] [Fintype τ]
    (L : (σ → GeometricField) ≃ₗ[GeometricField] (τ → GeometricField)) :
    (ofLinearEquiv L).inverseMap = L.symm := by
  funext y
  exact polynomialMap_linearCoordinatePolynomials L.symm.toLinearMap y

end PolynomialCoordinateEquiv
end HessianTheorem11
