import CubicTenVariables.ProjectiveLinearSectionCoordinates
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Irreducibility is independent of the coordinates chosen on a literal
linear subspace. Both coordinate frames are actual injective matrices and
their ranges are required to be equal. No geometric section premise occurs.
-/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FrameRestrictionIrreducibility
open MvPolynomial HessianTheorem11.PolynomialRestriction

variable {K : Type*} [Field K] [Infinite K] {m n : ℕ}

def coordinateMatrix (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    Matrix (Fin m) (Fin m) K := LinearMap.toMatrix' e.toLinearMap

omit [Infinite K] in
@[simp] theorem coordinateMatrix_mulVec
    (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) (x : Fin m → K) :
    (coordinateMatrix e).mulVec x = e x := LinearMap.toMatrix'_mulVec _ _

private theorem restrict_inverse (e : (Fin m → K) ≃ₗ[K] (Fin m → K))
    (F : MvPolynomial (Fin m) K) :
    restrict (coordinateMatrix e) (restrict (coordinateMatrix e.symm) F) = F := by
  apply MvPolynomial.funext
  intro x
  rw [eval_restrict, coordinateMatrix_mulVec, eval_restrict,
    coordinateMatrix_mulVec, LinearEquiv.symm_apply_apply]

/-- The pullback by an invertible linear coordinate change is an actual
polynomial algebra equivalence. -/
def coordinateAlgEquiv (e : (Fin m → K) ≃ₗ[K] (Fin m → K)) :
    MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K :=
  AlgEquiv.ofAlgHom (aeval (linearForms (coordinateMatrix e)))
    (aeval (linearForms (coordinateMatrix e.symm)))
    (by apply MvPolynomial.algHom_ext; intro i; exact restrict_inverse e (X i))
    (by apply MvPolynomial.algHom_ext; intro i; exact restrict_inverse e.symm (X i))

theorem restrict_irreducible (e : (Fin m → K) ≃ₗ[K] (Fin m → K))
    (F : MvPolynomial (Fin m) K) (hF : Irreducible F) :
    Irreducible (restrict (coordinateMatrix e) F) :=
  hF.map (coordinateAlgEquiv e).toMulEquiv

/-- Any two actual injective coordinate frames for the same subspace give
the same answer to irreducibility of a restricted polynomial. -/
theorem irreducible_of_same_range
    (A B : Matrix (Fin n) (Fin m) K)
    (hA : Function.Injective A.mulVec) (hB : Function.Injective B.mulVec)
    (hAB : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (F : MvPolynomial (Fin n) K) (hF : Irreducible (restrict B F)) :
    Irreducible (restrict A F) := by
  let eA := LinearEquiv.ofInjective A.mulVecLin hA
  let eB := LinearEquiv.ofInjective B.mulVecLin hB
  let e : (Fin m → K) ≃ₗ[K] (Fin m → K) :=
    (eA.trans (LinearEquiv.ofEq _ _ hAB)).trans eB.symm
  have he (x : Fin m → K) : B.mulVec (e x) = A.mulVec x := by
    exact LinearEquiv.ofInjective_symm_apply B.mulVecLin (h := hB) _
  have hp : restrict A F = restrict (coordinateMatrix e) (restrict B F) := by
    apply MvPolynomial.funext
    intro x
    rw [eval_restrict, eval_restrict, coordinateMatrix_mulVec, eval_restrict, he]
  rw [hp]
  exact restrict_irreducible e _ hF

end CubicTenVariables.FrameRestrictionIrreducibility
