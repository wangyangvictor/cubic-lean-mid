import HessianTheorem11.SingularLinearAlgebra
import HessianTheorem11.PolynomialRestriction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Elementary directional differentiation of a determinant at a zero column. -/
noncomputable section
namespace HessianTheorem11.ReducedDeterminantal
open MvPolynomial Matrix

variable {K : Type*} [Field K] {n : ℕ}

def differentialAt (x t : Fin n → K) : MvPolynomial (Fin n) K →ₗ[K] K where
  toFun p := polynomialDifferential p x t
  map_add' p q := by
    simp [polynomialDifferential_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by
    simp [polynomialDifferential_apply, Finset.mul_sum, mul_assoc]

theorem differentialAt_apply (x t : Fin n → K) (p : MvPolynomial (Fin n) K) :
    differentialAt x t p = polynomialDifferential p x t := rfl

@[simp] theorem differentialAt_C (x t : Fin n → K) (a : K) :
    differentialAt x t (C a) = 0 := by
  simp [differentialAt, polynomialDifferential_apply]

theorem differentialAt_mul (x t : Fin n → K) (p q : MvPolynomial (Fin n) K) :
    differentialAt x t (p*q) =
      differentialAt x t p * eval x q + eval x p * differentialAt x t q := by
  simp only [differentialAt_apply, polynomialDifferential_apply,
    Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem differentialAt_det_zero_column
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial (Fin n) K)) (x t : Fin n → K) (j : ι)
    (hz : ∀ i, eval x (N i j) = 0) :
    differentialAt x t N.det =
      Matrix.det (fun i k => if k = j then differentialAt x t (N i k)
        else eval x (N i k)) := by
  classical
  rw [det_apply', map_sum, det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : differentialAt x t (∏ i, N (σ i) i) =
      ∏ i, if i = j then differentialAt x t (N (σ i) i)
        else eval x (N (σ i) i) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => N (σ i) i) (Finset.mem_univ j),
      differentialAt_mul, hz, zero_mul, add_zero]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => if i = j then differentialAt x t (N (σ i) i)
        else eval x (N (σ i) i)) (Finset.mem_univ j)]
    simp only [if_true, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.ne_of_mem_erase hi]
  rw [differentialAt_mul, hprod]
  have hsign : (↑(Equiv.Perm.sign σ) : MvPolynomial (Fin n) K) =
      C (↑(Equiv.Perm.sign σ) : K) := by simp
  rw [hsign, differentialAt_C, zero_mul, zero_add, eval_C]

def pencilPolynomial {ι κ : Type*}
    (M : (Fin n → K) →ₗ[K] Matrix ι κ K) : Matrix ι κ (MvPolynomial (Fin n) K) :=
  fun i j => ∑ k, C (M ((Pi.basisFun K (Fin n)) k) i j) * X k

@[simp] theorem eval_pencilPolynomial {ι κ : Type*}
    (M : (Fin n → K) →ₗ[K] Matrix ι κ K) (x : Fin n → K) (i : ι) (j : κ) :
    eval x (pencilPolynomial M i j) = M x i j := by
  simp only [pencilPolynomial, eval_sum, eval_mul, eval_C, eval_X]
  have h := congrArg (fun z => M z i j) ((Pi.basisFun K (Fin n)).sum_repr x)
  simpa only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.basisFun_repr, mul_comm] using h

@[simp] theorem differentialAt_pencilPolynomial {ι κ : Type*}
    (M : (Fin n → K) →ₗ[K] Matrix ι κ K) (x t : Fin n → K) (i : ι) (j : κ) :
    differentialAt x t (pencilPolynomial M i j) = M t i j := by
  change polynomialDifferential
    (PolynomialRestriction.linearForms (fun (_ : Unit) k => M ((Pi.basisFun K (Fin n)) k) i j) ()) x t = _
  simp only [polynomialDifferential_apply, PolynomialRestriction.pderiv_linearForms, eval_C]
  have h := eval_pencilPolynomial M t i j
  simpa only [pencilPolynomial, eval_sum, eval_mul, eval_C, eval_X] using h

end HessianTheorem11.ReducedDeterminantal
