import CubicTenVariables.ProjectivePolynomialSectionVariance
import HessianTheorem11.PolynomialRestriction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual coordinate polynomials of linear sections

A chosen linear equivalence onto the common kernel of the equations
supplies the coordinate inclusion matrix and the actual restricted
polynomial. Its affine zeros are equivalent to the simultaneous zeros in
the ambient space. For a positive-degree homogeneous polynomial, the cone
identities give equality of the corresponding projective point counts.
No smoothness or independent cardinality-comparison premise occurs.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.ProjectiveLinearSectionCoordinates

open MvPolynomial HessianTheorem11.PolynomialRestriction
open ProjectiveFourierIdentity ProjectivePolynomialSectionVariance

variable {K : Type*} [Field K] {m n k d : ℕ}

/-- A vector lies in the kernel precisely when it satisfies every row equation. -/
theorem mem_equationKernel_iff (γ : Fin k → Fin n → K) (x : Fin n → K) :
    x ∈ LinearMap.ker (Matrix.mulVecLin γ) ↔ ∀ j, dotProduct (γ j) x = 0 := by
  change Matrix.mulVec γ x = 0 ↔ _
  exact funext_iff

/-- The literal matrix of the coordinate inclusion into the ambient vector space. -/
def sectionCoordinateMatrix (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    Matrix (Fin n) (Fin m) K :=
  LinearMap.toMatrix' ((LinearMap.ker (Matrix.mulVecLin γ)).subtype.comp e.toLinearMap)

@[simp]
theorem sectionCoordinateMatrix_mulVec (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) (z : Fin m → K) :
    (sectionCoordinateMatrix γ e).mulVec z = (e z : Fin n → K) := by
  exact LinearMap.toMatrix'_mulVec _ z

theorem sectionCoordinateMatrix_injective (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    Function.Injective (sectionCoordinateMatrix γ e).mulVec := by
  intro z w h
  apply e.injective
  apply Subtype.ext
  simpa only [sectionCoordinateMatrix_mulVec] using h

/-- Restriction along the chosen coordinates on the common kernel. -/
def sectionPolynomial (F : MvPolynomial (Fin n) K) (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    MvPolynomial (Fin m) K :=
  restrict (sectionCoordinateMatrix γ e) F

@[simp]
theorem eval_sectionPolynomial (F : MvPolynomial (Fin n) K)
    (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) (z : Fin m → K) :
    eval z (sectionPolynomial F γ e) = eval (e z : Fin n → K) F := by
  simp [sectionPolynomial]

theorem sectionPolynomial_isHomogeneous (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    (sectionPolynomial F γ e).IsHomogeneous d :=
  homogeneous_restrict (sectionCoordinateMatrix γ e) F hF

/-- An actual equivalence of affine zero sets, with both directions induced
by the displayed coordinate equivalence. -/
def affineSectionEquiv (F : MvPolynomial (Fin n) K) (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    {z : Fin m → K // eval z (sectionPolynomial F γ e) = 0} ≃
      {x : Fin n → K // eval x F = 0 ∧ ∀ j, dotProduct (γ j) x = 0} where
  toFun z := ⟨e z.val, by
    constructor
    · simpa only [eval_sectionPolynomial] using z.property
    · exact (mem_equationKernel_iff γ _).mp (e z.val).property⟩
  invFun x := ⟨e.symm ⟨x.val, (mem_equationKernel_iff γ x.val).mpr x.property.2⟩, by
    rw [eval_sectionPolynomial, e.apply_symm_apply]
    exact x.property.1⟩
  left_inv z := by
    apply Subtype.ext
    exact e.symm_apply_apply z.val
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun v : LinearMap.ker (Matrix.mulVecLin γ) => (v : Fin n → K))
      (e.apply_symm_apply ⟨x.val, (mem_equationKernel_iff γ x.val).mpr x.property.2⟩)

theorem affine_sectionPolynomial_card (F : MvPolynomial (Fin n) K)
    (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    Nat.card {z : Fin m → K // eval z (sectionPolynomial F γ e) = 0} =
      Nat.card {x : Fin n → K // eval x F = 0 ∧ ∀ j, dotProduct (γ j) x = 0} :=
  Nat.card_congr (affineSectionEquiv F γ e)

/-- Over a finite field, the literal coordinate hypersurface and the actual
projective linear section have the same number of rational points. -/
theorem projective_sectionPolynomial_card [Fintype K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (γ : Fin k → Fin n → K)
    (e : (Fin m → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ)) :
    Nat.card (zeroPoints (sectionPolynomial F γ e)) = Nat.card (linearSectionPoints F γ) := by
  have h := affine_sectionPolynomial_card F γ e
  rw [affine_zero_card _ (sectionPolynomial_isHomogeneous F hF γ e) hd,
    affine_linearSection_card F hF hd γ] at h
  have hq : 0 < Fintype.card K - 1 := by
    have hK : 1 < Fintype.card K := Fintype.one_lt_card
    omega
  exact Nat.eq_of_mul_eq_mul_right hq (Nat.add_right_cancel h)

end CubicTenVariables.ProjectiveLinearSectionCoordinates
