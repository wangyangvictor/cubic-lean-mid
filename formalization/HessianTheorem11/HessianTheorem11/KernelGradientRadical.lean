import HessianTheorem11.QuadraticCommonRadical
import HessianTheorem11.SubmoduleCoordinates
import HessianTheorem11.RadialSquareZeroSubspace

/-! A common radical of the actual gradient quadrics on a Hessian kernel
lifts to an actual tensor-square-zero subspace of the original cubic. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n a : ℕ}

theorem hessian_mulVec_zero_of_gradient_restriction_radical
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin n) (Fin a) GeometricField)
    (u : GeometricPoint a)
    (hu : u ∈ polynomialTupleDifferentialRadical (fun i => restrict B (pderiv i F)))
    (v : GeometricPoint a) :
    (hessian F (B.mulVec v)).mulVec (B.mulVec u) = 0 := by
  let P : Fin n → GeometricPolynomial n := fun i => pderiv i F
  have hP : ∀ i, (P i).IsHomogeneous 2 := fun i => hF.pderiv
  let Q : Fin n → GeometricPolynomial a := fun i => restrict B (P i)
  have hQ : ∀ i, (Q i).IsHomogeneous 2 := fun i => homogeneous_restrict B (P i) (hP i)
  have hz : (quadraticJacobianLinearMap Q hQ v).mulVec u = 0 := by
    change (quadraticJacobianLinearMap Q hQ v).mulVecLin u = 0
    rw [quadraticJacobian_mulVecLin]
    ext i
    exact (mem_polynomialTupleDifferentialRadical _ _).mp hu v i
  have he := quadraticJacobian_restrict P hP B v
  have hmatrix : quadraticJacobianLinearMap P hP (B.mulVec v) = hessian F (B.mulVec v) := rfl
  change (quadraticJacobianLinearMap (fun i => restrict B (P i)) hQ v).mulVec u = 0 at hz
  rw [he, hmatrix, ← Matrix.mulVec_mulVec] at hz
  exact hz

theorem lifted_gradient_radical_square_zero
    (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (B : Matrix (Fin n) (Fin a) GeometricField)
    (z : GeometricPoint n)
    (u : GeometricPoint a)
    (hu : u ∈ polynomialTupleDifferentialRadical (fun i => restrict B (pderiv i F)))
    (v : GeometricPoint a) :
    polarization F z (B.mulVec u) (B.mulVec v) = 0 := by
  change dotProduct z ((hessian F (B.mulVec v)).mulVec (B.mulVec u)) = 0
  rw [hessian_mulVec_zero_of_gradient_restriction_radical F hF B u hu v]
  simp

theorem thirteen_kernel_gradient_differential_radical_le_three
    (F : GeometricPolynomial 13) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : GeometricPoint 13) (hx : eval x F = 0)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin) :
    finrank GeometricField (polynomialTupleDifferentialRadical
      (fun i => restrict (submoduleCoordinateMatrix
        (LinearMap.ker (hessian F x).mulVecLin)) (pderiv i F))) ≤ 3 := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let B := submoduleCoordinateMatrix L
  let R := polynomialTupleDifferentialRadical (fun i => restrict B (pderiv i F))
  let S := R.map (submoduleCoordinateMap L)
  have hSL : S ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    have he : submoduleCoordinateMap L u ∈ Set.range (submoduleCoordinateMap L) := ⟨u,rfl⟩
    simpa only [submoduleCoordinateMap_range L] using he
  have hxS : x ∉ S := fun h => hxL (hSL h)
  have hzero : ∀ z : GeometricPoint 13, ∀ u ∈ S, ∀ v ∈ S, polarization F z u v = 0 := by
    intro z u hu v hv
    obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨v, hv, rfl⟩ := hv
    rw [← submoduleCoordinateMatrix_mulVec, ← submoduleCoordinateMatrix_mulVec]
    exact lifted_gradient_radical_square_zero F hF B z u hu v
  have hb := thirteen_radial_square_zero_finrank_le_three F hF hsemi x hx S hxS hSL hzero
  have hd : finrank GeometricField S = finrank GeometricField R :=
    (Submodule.equivMapOfInjective (submoduleCoordinateMap L)
      (submoduleCoordinateMap_injective L) R).finrank_eq.symm
  rwa [hd] at hb

end HessianTheorem11
