import CubicTenVariables.CubicNonconicalHyperplaneCertificate
import CubicTenVariables.ProjectiveLinearSectionCoordinates

/-! Coordinate identification for a hyperplane normal and its canonical frame.

The division-free frame used by the polynomial certificates is converted to
an actual linear equivalence onto the kernel of the one-row equation matrix.
Consequently its restricted polynomial counts the literal section appearing
in the projective variance identity.  This file is only linear algebra.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicNormalSectionCoordinates
open MvPolynomial HessianTheorem11.PolynomialRestriction
open ProjectiveFourierIdentity ProjectivePolynomialSectionVariance
open ProjectiveLinearSectionCoordinates
open CubicNonconicalHyperplaneCertificate

variable {K : Type*} [Field K] {n d : ℕ}

def equationTuple (u : Fin (n+1) → K) : Fin 1 → Fin (n+1) → K := fun _ => u

theorem equationTuple_zero (γ : Fin 1 → Fin (n+1) → K) :
    equationTuple (γ 0) = γ := by
  funext j i
  rw [show j = 0 from Subsingleton.elim _ _]
  rfl

theorem mem_equationTuple_kernel_iff (u : Fin (n+1) → K) (x : Fin (n+1) → K) :
    x ∈ LinearMap.ker (Matrix.mulVecLin (equationTuple u)) ↔
      x ∈ LinearMap.ker (GenericHyperplaneFrameKernel.normal u) := by
  change Matrix.mulVec (equationTuple u) x = 0 ↔
    (∑ i, u i * x i) = 0
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [equationTuple, Matrix.mulVec, dotProduct] using h0
  · intro h
    funext j
    rw [show j = 0 from Subsingleton.elim _ _]
    simpa [equationTuple, Matrix.mulVec, dotProduct] using h

def frameKernelMap (u : Fin (n+1) → K)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) :
    (Fin n → K) →ₗ[K] LinearMap.ker (Matrix.mulVecLin (equationTuple u)) :=
  (frame u).mulVecLin.codRestrict _ fun z =>
    (mem_equationTuple_kernel_iff u _).mpr
      (hrange ▸ (show (frame u).mulVec z ∈ LinearMap.range (frame u).mulVecLin from ⟨z, rfl⟩))

@[simp]
theorem frameKernelMap_coe (u : Fin (n+1) → K)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) (z : Fin n → K) :
    ((frameKernelMap u hrange z :
      LinearMap.ker (Matrix.mulVecLin (equationTuple u))) : Fin (n+1) → K) =
        (frame u).mulVec z := rfl

def frameEquiv (u : Fin (n+1) → K)
    (hinj : Function.Injective (frame u).mulVec)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) :
    (Fin n → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin (equationTuple u)) := by
  apply LinearEquiv.ofBijective (frameKernelMap u hrange)
  constructor
  · intro x y h
    apply hinj
    exact congrArg Subtype.val h
  · intro y
    have hy : (y : Fin (n+1) → K) ∈
        LinearMap.ker (GenericHyperplaneFrameKernel.normal u) :=
      (mem_equationTuple_kernel_iff u _).mp y.property
    rw [← hrange] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, Subtype.ext ?_⟩
    exact hx

@[simp]
theorem frameEquiv_coe (u : Fin (n+1) → K)
    (hinj : Function.Injective (frame u).mulVec)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) (z : Fin n → K) :
    ((frameEquiv u hinj hrange z :
      LinearMap.ker (Matrix.mulVecLin (equationTuple u))) : Fin (n+1) → K) =
        (frame u).mulVec z := rfl

theorem sectionCoordinateMatrix_frame (u : Fin (n+1) → K)
    (hinj : Function.Injective (frame u).mulVec)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) :
    sectionCoordinateMatrix (equationTuple u) (frameEquiv u hinj hrange) = frame u := by
  apply Matrix.mulVec_injective
  funext z
  rw [sectionCoordinateMatrix_mulVec]
  exact frameEquiv_coe u hinj hrange z

theorem sectionPolynomial_frame (F : MvPolynomial (Fin (n+1)) K)
    (u : Fin (n+1) → K) (hinj : Function.Injective (frame u).mulVec)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) :
    sectionPolynomial F (equationTuple u) (frameEquiv u hinj hrange) =
      restrict (frame u) F := by
  rw [sectionPolynomial, sectionCoordinateMatrix_frame]

/-- The canonical normal-chart restriction counts the literal projective
hyperplane section used in the variance identity. -/
theorem projective_frame_card [Fintype K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (u : Fin (n+1) → K) (hinj : Function.Injective (frame u).mulVec)
    (hrange : LinearMap.range (frame u).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal u)) :
    Nat.card (zeroPoints (restrict (frame u) F)) =
      Nat.card (linearSectionPoints F (equationTuple u)) := by
  rw [← sectionPolynomial_frame F u hinj hrange]
  exact projective_sectionPolynomial_card F hF hd _ _

/-- The same count identity for an arbitrary one-row tuple, which is
definitionally determined by its unique row. -/
theorem projective_frame_card_one_row [Fintype K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (γ : Fin 1 → Fin (n+1) → K)
    (hinj : Function.Injective (frame (γ 0)).mulVec)
    (hrange : LinearMap.range (frame (γ 0)).mulVecLin =
      LinearMap.ker (GenericHyperplaneFrameKernel.normal (γ 0))) :
    Nat.card (zeroPoints (restrict (frame (γ 0)) F)) =
      Nat.card (linearSectionPoints F γ) := by
  rw [← equationTuple_zero γ]
  exact projective_frame_card F hF hd (γ 0) hinj hrange

end CubicTenVariables.CubicNormalSectionCoordinates
