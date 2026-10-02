import TranslatedDepthSeven.AlgebraicallyClosedTensorDomain
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IsTensorProduct

/-!
# Primality after extending an algebraically closed coefficient field

We promote the existing quotient base-change linear equivalence to an
algebra equivalence, checking multiplication on pure tensors.  The domain
theorem proved from the Nullstellensatz then applies to the finite-type
polynomial quotient.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

universe u v w

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

noncomputable local instance coefficientPrimePolynomialAlgebra
    {σ : Type w} : Algebra (MvPolynomial σ K) (MvPolynomial σ L) :=
  MvPolynomial.algebraMvPolynomial

/-- The existing polynomial-quotient base-change equivalence also preserves
multiplication. -/
def polynomialQuotientTensorAlgEquiv {σ : Type w}
    (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L))) ≃ₐ[L]
      L ⊗[K] (MvPolynomial σ K ⧸ I) := by
  let e := Algebra.IsPushout.cancelBaseChange K L
    (MvPolynomial σ K) (MvPolynomial σ L) (MvPolynomial σ K ⧸ I)
  have hone : e.symm 1 = 1 := by
    simp [e, Algebra.TensorProduct.one_def,
      Algebra.IsPushout.cancelBaseChange_symm_tmul]
  have hmul : ∀ x y, e.symm (x * y) = e.symm x * e.symm y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp [add_mul, hx, hx']
    | tmul l q =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' hy hy' => simp [mul_add, hy, hy']
        | tmul l' q' =>
            simp [e, Algebra.IsPushout.cancelBaseChange_symm_tmul,
              Algebra.TensorProduct.tmul_mul_tmul]
  let ealg := AlgEquiv.ofLinearEquiv e.symm hone hmul
  exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (MvPolynomial σ L) I).restrictScalars L).trans ealg.symm

/-- A prime polynomial ideal over an algebraically closed field remains
prime over every extension field. -/
theorem coefficientExtension_isPrime_of_isAlgClosed
    [IsAlgClosed K] {σ : Type w} [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime) :
    (I.map (MvPolynomial.map (algebraMap K L))).IsPrime := by
  letI : I.IsPrime := hI
  letI : IsDomain ((MvPolynomial σ K ⧸ I) ⊗[K] L) :=
    tensorProduct_isDomain_of_algebraicallyClosed_of_finiteType
      (K := K) (A := L) (B := MvPolynomial σ K ⧸ I)
  letI : IsDomain (L ⊗[K] (MvPolynomial σ K ⧸ I)) :=
    (Algebra.TensorProduct.comm K L (MvPolynomial σ K ⧸ I)).toMulEquiv.isDomain _
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact (polynomialQuotientTensorAlgEquiv (L := L) I).toMulEquiv.isDomain _

end

end TranslatedDepthSeven
