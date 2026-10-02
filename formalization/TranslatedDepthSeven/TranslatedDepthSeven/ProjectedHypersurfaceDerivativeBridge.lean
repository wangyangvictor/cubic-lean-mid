import TranslatedDepthSeven.ProjectedHypersurfaceSalbergerPullback
import TranslatedDepthSeven.HypersurfaceProperDerivative
import TranslatedDepthSeven.PrimitiveBoundedHypersurfaceAlternative

/-!
# Literal derivatives on the affine hypersurface image

The displayed one-equation Jacobian certificate is exactly a spatial
partial derivative of the homogeneous equation at `(1,z)`. No change of
integral model, exceptional denominator, or height estimate is involved
in this identification.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

@[simp]
theorem integralDehomogenizeAtZeroHom_C {N : ℕ} (c : ℤ) :
    (@integralDehomogenizeAtZeroHom N) (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [integralDehomogenizeAtZeroHom]

@[simp]
theorem integralDehomogenizeAtZeroHom_X_zero {N : ℕ} :
    (@integralDehomogenizeAtZeroHom N) (MvPolynomial.X 0) = 1 := by
  simp [integralDehomogenizeAtZeroHom]

@[simp]
theorem integralDehomogenizeAtZeroHom_X_succ {N : ℕ} (j : Fin N) :
    integralDehomogenizeAtZeroHom (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [integralDehomogenizeAtZeroHom]

theorem eval_integralDehomogenizeAtZeroHom
    {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℤ) (z : Fin N → ℤ) :
    MvPolynomial.eval z (integralDehomogenizeAtZeroHom P) =
      MvPolynomial.eval (integralAffineProjectivePoint z) P := by
  have h : (MvPolynomial.eval z).comp integralDehomogenizeAtZeroHom =
      MvPolynomial.eval (integralAffineProjectivePoint z) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  exact congrArg (fun f ↦ f P) h

theorem pderiv_integralDehomogenizeAtZeroHom
    {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℤ) (j : Fin N) :
    MvPolynomial.pderiv j (integralDehomogenizeAtZeroHom P) =
      integralDehomogenizeAtZeroHom (MvPolynomial.pderiv j.succ P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simp [Derivation.leibniz, hP, MvPolynomial.pderiv_X, Pi.single_apply]
    · by_cases hk : k = j <;>
        simp [Derivation.leibniz, hP, MvPolynomial.pderiv_X, Pi.single_apply,
          smul_eq_mul, hk]

theorem eval_pderiv_integralDehomogenizeAtZeroHom
    {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℤ)
    (z : Fin N → ℤ) (j : Fin N) :
    MvPolynomial.eval z
        (MvPolynomial.pderiv j (integralDehomogenizeAtZeroHom P)) =
      MvPolynomial.eval (integralAffineProjectivePoint z)
        (MvPolynomial.pderiv j.succ P) := by
  rw [pderiv_integralDehomogenizeAtZeroHom, eval_integralDehomogenizeAtZeroHom]

theorem projectedHypersurfaceJacobian_eq_pderiv
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℤ) (j : Fin (r + 1)) :
    selectedJacobianDeterminant (projectedHypersurfaceAffineEquation P)
        (projectedHypersurfaceSelectedVariable j) =
      MvPolynomial.pderiv j (integralDehomogenizeAtZeroHom P) := by
  simp [selectedJacobianDeterminant, Matrix.det_unique,
    projectedHypersurfaceAffineEquation, projectedHypersurfaceSelectedVariable]

theorem eval_projectedHypersurfaceJacobian_eq_spatial_partial
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℤ)
    (z : Fin (r + 1) → ℤ) (j : Fin (r + 1)) :
    MvPolynomial.eval z
        (selectedJacobianDeterminant (projectedHypersurfaceAffineEquation P)
          (projectedHypersurfaceSelectedVariable j)) =
      MvPolynomial.eval (integralAffineProjectivePoint z)
        (MvPolynomial.pderiv j.succ P) := by
  rw [projectedHypersurfaceJacobian_eq_pderiv,
    eval_pderiv_integralDehomogenizeAtZeroHom]

end

end TranslatedDepthSeven
