import HessianTheorem11.KernelGradientSpan
import HessianTheorem11.TwoPlaneRank

/-! Tangent containment of an actual vector subspace in a polynomial
image, and its application to the conormal space of a cubic-zero base. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n : ℕ}

theorem submodule_le_affineTangentSpace_of_subset
    (S : Submodule GeometricField (GeometricPoint n)) (Z : Set (GeometricPoint n))
    (hsub : (S : Set (GeometricPoint n)) ⊆ Z)
    (x : GeometricPoint n) (hx : x ∈ S) : S ≤ affineTangentSpace Z x := by
  intro v hv
  apply mem_affineTangentSpace.mpr
  intro P hP
  let B := twoPlaneMatrix x v
  have hzero : restrict B P = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [eval_restrict]
    apply hP
    apply hsub
    rw [show B = twoPlaneMatrix x v from rfl, twoPlaneMatrix_mulVec]
    exact S.add_mem (S.smul_mem _ hx) (S.smul_mem _ hv)
  have hd := congrArg (fun q : GeometricPolynomial 2 => eval ![1,0] (pderiv 1 q)) hzero
  dsimp only at hd
  rw [pderiv_restrict] at hd
  have hb : B.mulVec (![1,0] : GeometricPoint 2) = x := by simp [B, twoPlaneMatrix_mulVec]
  simp only [map_sum, map_mul, eval_restrict, eval_C, hb, map_zero] at hd
  simpa [B, twoPlaneMatrix, polynomialDifferential_apply] using hd

theorem gradient_mem_conormal_of_cubic_zero
    (F : GeometricPolynomial n) (Z : Set (GeometricPoint n))
    (hzero : ∀ y ∈ Z, eval y F = 0) (x : GeometricPoint n) :
    gradient F x ∈ (coordinatePairing (K := GeometricField) (n := n)).orthogonal
      (affineTangentSpace Z x) := by
  intro t ht
  have hh := (mem_affineTangentSpace.mp ht) F hzero
  change dotProduct t (gradient F x) = 0
  simpa [polynomialDifferential_apply, dotProduct, gradient, mul_comm] using hh

theorem gradient_coisotropic_of_conormal_contained_in_image
    (F : GeometricPolynomial n) (Z : Set (GeometricPoint n))
    (hzero : ∀ y ∈ Z, eval y F = 0) (x : GeometricPoint n)
    (hcontained : ((coordinatePairing (K := GeometricField) (n := n)).orthogonal
      (affineTangentSpace Z x) : Set (GeometricPoint n)) ⊆
        geometricClosure (gradient F '' Z))
    (himageTangent : affineTangentSpace (geometricClosure (gradient F '' Z)) (gradient F x) =
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x))) :
    (coordinatePairing (K := GeometricField) (n := n)).orthogonal (affineTangentSpace Z x) ≤
      LinearMap.range ((hessian F x).mulVecLin.domRestrict (affineTangentSpace Z x)) := by
  rw [← himageTangent]
  exact submodule_le_affineTangentSpace_of_subset _ _ hcontained _
    (gradient_mem_conormal_of_cubic_zero F Z hzero x)

end HessianTheorem11
