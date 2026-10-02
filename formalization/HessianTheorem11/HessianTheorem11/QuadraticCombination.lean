import HessianTheorem11.IsotropicJacobianRank
import HessianTheorem11.HessianLinearity

/-! Euler identities for the actual Hessian pencil of a tuple of quadrics. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix
variable {K : Type*} [Field K] {s r : ℕ}

@[simp] theorem normalCombination_zero
    (p : Fin r → MvPolynomial (Fin s) K) (a : Fin s → K) :
    normalCombination p a 0 = 0 := by
  ext i j
  simp [normalCombination]

theorem normalCombination_add
    (p : Fin r → MvPolynomial (Fin s) K) (a : Fin s → K) (d e : Fin r → K) :
    normalCombination p a (d + e) = normalCombination p a d + normalCombination p a e := by
  ext i j
  simp [normalCombination, add_mul, Finset.sum_add_distrib]

theorem normalCombination_smul
    (p : Fin r → MvPolynomial (Fin s) K) (a : Fin s → K) (c : K) (d : Fin r → K) :
    normalCombination p a (c • d) = c • normalCombination p a d := by
  ext i j
  simp [normalCombination, mul_assoc, Finset.mul_sum]

theorem normalCombination_symmetric
    (p : Fin r → MvPolynomial (Fin s) K) (a : Fin s → K) (d : Fin r → K) :
    (normalCombination p a d).IsSymm := by
  ext i j
  simp only [normalCombination, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [partials_commute]

theorem normalCombination_constant
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (a b : Fin s → K) (d : Fin r → K) :
    normalCombination p a d = normalCombination p b d := by
  ext i j
  simp only [normalCombination]
  apply Finset.sum_congr rfl
  intro k _
  rw [homogeneous_zero_eq_constant (hp k).pderiv.pderiv]
  simp

theorem normalCombination_mulVec
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (a : Fin s → K) (d : Fin r → K) :
    (normalCombination p a d).mulVec a =
      (TangentHessianRank.polynomialJacobian p a).transpose.mulVec d := by
  ext i
  have he (k : Fin r) :
      (∑ j, a j * eval a (pderiv j (pderiv i (p k)))) = eval a (pderiv i (p k)) := by
    have hi : (pderiv i (p k)).IsHomogeneous 1 := (hp k).pderiv
    have h := congrArg (eval a) hi.sum_X_mul_pderiv
    simpa only [map_sum, map_mul, eval_X, one_smul] using h
  simp only [normalCombination, Matrix.mulVec, dotProduct,
    TangentHessianRank.polynomialJacobian, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (∑ j, d k * eval a (pderiv j (pderiv i (p k))) * a j) =
    d k * ∑ j, a j * eval a (pderiv j (pderiv i (p k))) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring, he]
  ring

theorem quadraticJacobian_mulVec
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (a : Fin s → K) :
    (TangentHessianRank.polynomialJacobian p a).mulVec a =
      (2 : K) • (fun i => eval a (p i)) := by
  ext i
  have hh := congrArg (eval a) (hp i).sum_X_mul_pderiv
  simpa only [TangentHessianRank.polynomialJacobian, Matrix.mulVec, dotProduct,
    map_sum, map_mul, eval_X, map_nsmul, Pi.smul_apply, smul_eq_mul,
    two_nsmul, two_mul, mul_comm, map_add] using hh

theorem normalCombination_quadratic
    (p : Fin r → MvPolynomial (Fin s) K) (hp : ∀ i, (p i).IsHomogeneous 2)
    (a : Fin s → K) (d : Fin r → K) :
    dotProduct a ((normalCombination p a d).mulVec a) =
      2 * dotProduct d (fun i => eval a (p i)) := by
  rw [normalCombination_mulVec p hp]
  have he : dotProduct a ((TangentHessianRank.polynomialJacobian p a).transpose.mulVec d) =
      dotProduct d ((TangentHessianRank.polynomialJacobian p a).mulVec a) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, quadraticJacobian_mulVec p hp]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end HessianTheorem11
