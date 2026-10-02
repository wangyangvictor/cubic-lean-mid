import CubicTenVariables.RationalComponentDescent
import Mathlib.Algebra.MvPolynomial.Equiv

/-! Semilinear Galois transport of actual affine sets and coordinate rings. -/

noncomputable section
namespace CubicTenVariables.GaloisAffineTransport
open MvPolynomial HessianTheorem11 RationalComponentDescent

variable {n : ℕ}

/-- The coordinatewise Galois action is an equivalence of point sets. -/
def pointEquiv (σ : GeometricField ≃ₐ[ℚ] GeometricField) :
    GeometricPoint n ≃ GeometricPoint n where
  toFun := galoisPoint σ
  invFun := galoisPoint σ.symm
  left_inv := galoisPoint_symm_apply σ
  right_inv := galoisPoint_apply_symm σ

/-- Coefficient conjugation is a ring equivalence. It need not fix the
geometric coefficient field pointwise. -/
def coefficientRingEquiv (σ : GeometricField ≃ₐ[ℚ] GeometricField) :
    GeometricPolynomial n ≃+* GeometricPolynomial n :=
  MvPolynomial.mapEquiv (Fin n) σ.toRingEquiv

@[simp] theorem coefficientRingEquiv_apply
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (f : GeometricPolynomial n) :
    coefficientRingEquiv σ f = map σ.toRingHom f := rfl

@[simp] theorem coefficientRingEquiv_symm_apply
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (f : GeometricPolynomial n) :
    (coefficientRingEquiv σ).symm f = map σ.symm.toRingHom f := rfl

/-- A conjugated polynomial vanishes on the conjugated set exactly when
the original polynomial vanishes on the original set. -/
theorem coefficientMap_mem_vanishingIdeal_image_iff
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (Z : Set (GeometricPoint n))
    (f : GeometricPolynomial n) :
    map σ.toRingHom f ∈ vanishingIdeal GeometricField (galoisPoint σ '' Z) ↔
      f ∈ vanishingIdeal GeometricField Z := by
  constructor
  · intro hf x hx
    have hz := hf (galoisPoint σ x) ⟨x,hx,rfl⟩
    change eval (galoisPoint σ x) (map σ.toRingHom f) = 0 at hz
    rw [eval_coefficientMap] at hz
    exact σ.injective (hz.trans (map_zero σ).symm)
  · intro hf y hy
    obtain ⟨x,hx,rfl⟩ := hy
    change eval (galoisPoint σ x) (map σ.toRingHom f) = 0
    have hz := hf x hx
    change eval x f = 0 at hz
    rw [eval_coefficientMap, hz, map_zero]

/-- The actual vanishing ideal of a conjugated point set is the image
of its vanishing ideal under coefficient conjugation. -/
theorem vanishingIdeal_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    vanishingIdeal GeometricField (galoisPoint σ '' Z) =
      (vanishingIdeal GeometricField Z).map (map σ.toRingHom) := by
  ext f
  have hsurj : Function.Surjective
      (map σ.toRingHom : GeometricPolynomial n →+* GeometricPolynomial n) :=
    (coefficientRingEquiv σ).surjective
  rw [Ideal.mem_map_iff_of_surjective _ hsurj]
  constructor
  · intro hf
    refine ⟨map σ.symm.toRingHom f, ?_, coefficientMap_apply_symm σ f⟩
    apply (coefficientMap_mem_vanishingIdeal_image_iff σ Z _).1
    simpa only [coefficientMap_apply_symm] using hf
  · rintro ⟨g,hg,rfl⟩
    exact (coefficientMap_mem_vanishingIdeal_image_iff σ Z g).2 hg

/-- The reduced coordinate rings are genuinely isomorphic as rings.
No geometric-field algebra-linearity is claimed. -/
def coordinateRingEquiv (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    (GeometricPolynomial n ⧸ vanishingIdeal GeometricField Z) ≃+*
      (GeometricPolynomial n ⧸ vanishingIdeal GeometricField (galoisPoint σ '' Z)) :=
  Ideal.quotientEquiv (vanishingIdeal GeometricField Z)
    (vanishingIdeal GeometricField (galoisPoint σ '' Z))
    (coefficientRingEquiv σ) (vanishingIdeal_image σ Z)

@[simp] theorem coordinateRingEquiv_mk
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (Z : Set (GeometricPoint n))
    (f : GeometricPolynomial n) :
    coordinateRingEquiv σ Z (Ideal.Quotient.mk (vanishingIdeal GeometricField Z) f) =
      Ideal.Quotient.mk (vanishingIdeal GeometricField (galoisPoint σ '' Z))
        (map σ.toRingHom f) := rfl

@[simp] theorem coordinateRingEquiv_symm_mk
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (Z : Set (GeometricPoint n))
    (f : GeometricPolynomial n) :
    (coordinateRingEquiv σ Z).symm
      (Ideal.Quotient.mk (vanishingIdeal GeometricField (galoisPoint σ '' Z)) f) =
      Ideal.Quotient.mk (vanishingIdeal GeometricField Z) (map σ.symm.toRingHom f) := rfl

/-- Galois conjugation preserves the actual affine Krull dimension. -/
theorem affineDimension_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    affineDimension (galoisPoint σ '' Z) = affineDimension Z :=
  (ringKrullDim_eq_of_ringEquiv (coordinateRingEquiv σ Z)).symm

/-- Closure membership is transported along the actual point action. -/
theorem galoisPoint_mem_closure_iff (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n) :
    galoisPoint σ x ∈ geometricClosure (galoisPoint σ '' Z) ↔
      x ∈ geometricClosure Z := by
  constructor
  · intro hx f hf
    have hz := hx (map σ.toRingHom f)
      ((coefficientMap_mem_vanishingIdeal_image_iff σ Z f).2 hf)
    change eval (galoisPoint σ x) (map σ.toRingHom f) = 0 at hz
    rw [eval_coefficientMap] at hz
    exact σ.injective (hz.trans (map_zero σ).symm)
  · intro hx f hf
    have hfinv : map σ.symm.toRingHom f ∈ vanishingIdeal GeometricField Z := by
      apply (coefficientMap_mem_vanishingIdeal_image_iff σ Z _).1
      simpa only [coefficientMap_apply_symm] using hf
    have hz := hx (map σ.symm.toRingHom f) hfinv
    change eval x (map σ.symm.toRingHom f) = 0 at hz
    have heval := eval_coefficientMap σ (map σ.symm.toRingHom f) x
    rw [coefficientMap_apply_symm, hz, map_zero] at heval
    exact heval

/-- Galois conjugation commutes with the actual algebraic closure of
any point set, including sets that are not themselves closed. -/
theorem geometricClosure_image (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (Z : Set (GeometricPoint n)) :
    geometricClosure (galoisPoint σ '' Z) = galoisPoint σ '' geometricClosure Z := by
  ext y
  constructor
  · intro hy
    refine ⟨galoisPoint σ.symm y, ?_, galoisPoint_apply_symm σ y⟩
    apply (galoisPoint_mem_closure_iff σ Z _).1
    simpa only [galoisPoint_apply_symm] using hy
  · rintro ⟨x,hx,rfl⟩
    exact (galoisPoint_mem_closure_iff σ Z x).2 hx

/-- Being algebraically closed is invariant under the semilinear action. -/
theorem algebraicallyClosedSet_image_iff
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (Z : Set (GeometricPoint n)) :
    AlgebraicallyClosedSet (galoisPoint σ '' Z) ↔ AlgebraicallyClosedSet Z := by
  unfold AlgebraicallyClosedSet
  rw [geometricClosure_image]
  exact (pointEquiv σ).injective.image_injective.eq_iff

end CubicTenVariables.GaloisAffineTransport
