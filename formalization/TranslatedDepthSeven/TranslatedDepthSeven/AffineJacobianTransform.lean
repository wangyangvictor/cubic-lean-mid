import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.ConcreteIntegralCountRescaling
import TranslatedDepthSeven.JacobianCertificate
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Jacobians under the integral affine normalization

The translated depth-seven argument works with the normalized variables
`x = x₀ + m z`.  This file records the literal chain rule for that
substitution.  At a prime not dividing `m`, the normalized and original
Jacobian matrices differ only by multiplication by the nonzero scalar `m`;
in particular they have exactly the same rank.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Formal chain rule for the scalar affine substitution
`X i ↦ x₀ i + m X i`. -/
theorem pderiv_integralAffineTransform
    {n : ℕ} (x₀ : IntVector n) (m : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (j : Fin n) :
    MvPolynomial.pderiv j (integralAffineTransform x₀ m f) =
      MvPolynomial.C (m : ℤ) *
        integralAffineTransform x₀ m (MvPolynomial.pderiv j f) := by
  classical
  let φ : MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ :=
    MvPolynomial.aeval fun i ↦
      MvPolynomial.C (x₀ i) + MvPolynomial.C (m : ℤ) * MvPolynomial.X i
  change MvPolynomial.pderiv j (φ f) =
    MvPolynomial.C (m : ℤ) * φ (MvPolynomial.pderiv j f)
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp [φ]
  | add f g hf hg =>
      rw [map_add, Derivation.map_add, hf, hg, Derivation.map_add, map_add]
      ring
  | mul_X f i hf =>
      rw [map_mul, Derivation.leibniz, hf, Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      by_cases hij : i = j
      · subst i
        simp [φ]
        ring
      · simp [φ, hij]
        ring

/-- Evaluated form of the chain rule. -/
theorem eval_pderiv_integralAffineTransform
    {n : ℕ} (x₀ z : IntVector n) (m : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (j : Fin n) :
    MvPolynomial.eval z
        (MvPolynomial.pderiv j (integralAffineTransform x₀ m f)) =
      (m : ℤ) *
        MvPolynomial.eval (integralAffineMap x₀ z m)
          (MvPolynomial.pderiv j f) := by
  rw [pderiv_integralAffineTransform, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_integralAffineTransform]

/-- Transform a finite indexed equation family coefficientwise. -/
def integralAffineTransformFamily
    {r n : ℕ} (x₀ : IntVector n) (m : ℕ)
    (F : Fin r → MvPolynomial (Fin n) ℤ) :
    Fin r → MvPolynomial (Fin n) ℤ :=
  fun i ↦ integralAffineTransform x₀ m (F i)

/-- The normalized Jacobian is the original Jacobian at `x₀+mz`, multiplied
entrywise by the scalar `m`. -/
theorem integralJacobianMatrix_transform
    {r n : ℕ} (x₀ z : IntVector n) (m : ℕ)
    (F : Fin r → MvPolynomial (Fin n) ℤ) :
    integralJacobianMatrix (integralAffineTransformFamily x₀ m F) z =
      (m : ℤ) • integralJacobianMatrix F (integralAffineMap x₀ z m) := by
  ext i j
  simp [integralJacobianMatrix, integralAffineTransformFamily,
    eval_pderiv_integralAffineTransform, Matrix.smul_apply]

/-- Every selected normalized Jacobian minor is the corresponding original
minor multiplied by the expected power of the affine scale. -/
theorem integralJacobianMinor_transform
    {r n k : ℕ} (x₀ z : IntVector n) (m : ℕ)
    (F : Fin r → MvPolynomial (Fin n) ℤ)
    (rows : Fin k → Fin r) (cols : Fin k → Fin n) :
    integralJacobianMinor (integralAffineTransformFamily x₀ m F) z
        rows cols =
      (m : ℤ) ^ k *
        integralJacobianMinor F (integralAffineMap x₀ z m) rows cols := by
  rw [integralJacobianMinor, integralJacobianMinor,
    integralJacobianMatrix_transform]
  change Matrix.det ((m : ℤ) •
      (integralJacobianMatrix F (integralAffineMap x₀ z m)).submatrix
        rows cols) = _
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]

/-- Reduction modulo `p` of the preceding matrix identity. -/
theorem jacobianMatrix_transform
    {r n p : ℕ} (x₀ z : IntVector n) (m : ℕ)
    (F : Fin r → MvPolynomial (Fin n) ℤ) :
    jacobianMatrix (integralAffineTransformFamily x₀ m F) z p =
      (m : ZMod p) • jacobianMatrix F (integralAffineMap x₀ z m) p := by
  ext i j
  simp [jacobianMatrix, integralAffineTransformFamily,
    eval_pderiv_integralAffineTransform, Matrix.smul_apply]

/-- Multiplication of every matrix entry by a nonzero scalar preserves rank.
This elementary statement is kept separate because it is also useful for
other scalar normalizations. -/
theorem Matrix.rank_smul_eq_of_ne_zero
    {K : Type*} [Field K] {r n : ℕ}
    (c : K) (hc : c ≠ 0) (A : Matrix (Fin r) (Fin n) K) :
    (c • A).rank = A.rank := by
  classical
  rw [Matrix.smul_eq_diagonal_mul]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hc)

/-- Away from primes dividing the normalization scale, the transformed and
original Jacobians have equal rank. -/
theorem jacobianMatrix_transform_rank_eq
    {r n p : ℕ} (hp : p.Prime) {m : ℕ} (hpm : ¬ p ∣ m)
    (x₀ z : IntVector n)
    (F : Fin r → MvPolynomial (Fin n) ℤ) :
    (jacobianMatrix (integralAffineTransformFamily x₀ m F) z p).rank =
      (jacobianMatrix F (integralAffineMap x₀ z m) p).rank := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [jacobianMatrix_transform]
  apply Matrix.rank_smul_eq_of_ne_zero
  exact (ZMod.natCast_eq_zero_iff m p).not.mpr hpm

end

end TranslatedDepthSeven
