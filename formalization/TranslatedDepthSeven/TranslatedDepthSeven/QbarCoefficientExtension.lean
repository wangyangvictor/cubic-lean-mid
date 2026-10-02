import TranslatedDepthSeven.ConcreteExceptionalLocus
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Faithful flatness and minimal-prime contraction for Qbar coefficients

The coefficient extension `Q[X] -> Qbar[X]` is a faithfully flat base
change.  Consequently every minimal prime over the extension of a rational
prime contracts to that original prime.  This is the exact going-down fact
needed in the geometric-component split.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1000000

noncomputable local instance qbarMvPolynomialCoefficientAlgebra
    {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ Qbar) :=
  MvPolynomial.algebraMvPolynomial

/-- The explicit polynomial-base-linear tensor description of Qbar
coefficient extension. -/
noncomputable def qbarMvPolynomialTensorLinearEquiv
    {σ : Type*} :
    MvPolynomial σ Qbar ≃ₗ[MvPolynomial σ ℚ]
      ((MvPolynomial σ ℚ) ⊗[ℚ] Qbar) := by
  let eAlg : ((MvPolynomial σ ℚ) ⊗[ℚ] Qbar) ≃ₐ[ℚ]
      MvPolynomial σ Qbar :=
    (Algebra.TensorProduct.comm ℚ (MvPolynomial σ ℚ) Qbar).trans
      ((MvPolynomial.algebraTensorAlgEquiv ℚ Qbar
        (σ := σ)).restrictScalars ℚ)
  exact
    { eAlg.symm.toEquiv with
      map_add' := eAlg.symm.map_add
      map_smul' := by
        intro a b
        simp [eAlg, Algebra.smul_def]
        change (algebraMap (MvPolynomial σ ℚ)
          ((MvPolynomial σ ℚ) ⊗[ℚ] Qbar)) a *
            (Algebra.TensorProduct.comm ℚ (MvPolynomial σ ℚ) Qbar).symm
              ((MvPolynomial.algebraTensorAlgEquiv ℚ Qbar
                (σ := σ)).symm b) = _
        exact (Algebra.smul_def a _).symm }

/-- Qbar multivariate polynomials are faithfully flat over rational
multivariate polynomials under coefficient extension. -/
noncomputable instance qbarMvPolynomial_faithfullyFlat
    {σ : Type*} :
    Module.FaithfullyFlat (MvPolynomial σ ℚ) (MvPolynomial σ Qbar) := by
  letI : Module.FaithfullyFlat ℚ Qbar := inferInstance
  letI : Module.FaithfullyFlat (MvPolynomial σ ℚ)
      ((MvPolynomial σ ℚ) ⊗[ℚ] Qbar) := inferInstance
  exact Module.FaithfullyFlat.of_linearEquiv
    (MvPolynomial σ ℚ) ((MvPolynomial σ ℚ) ⊗[ℚ] Qbar)
      qbarMvPolynomialTensorLinearEquiv

/-- A minimal geometric component of the coefficient extension of a
rational prime contracts to the original prime. -/
theorem comap_qbar_minimalPrime_map_eq_of_isPrime
    {σ : Type*}
    (I : Ideal (MvPolynomial σ ℚ)) (hIprime : I.IsPrime)
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P ∈
      (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).minimalPrimes) :
    P.comap (MvPolynomial.map (algebraMap ℚ Qbar)) = I := by
  let R := MvPolynomial σ ℚ
  let S := MvPolynomial σ Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  let Q : Ideal R := P.comap f
  have hQprime : Q.IsPrime := hPprime.comap f
  have hIQ : I ≤ Q := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hP.1.2
  by_contra hne
  have hIQstrict : I < Q := lt_of_le_of_ne hIQ (Ne.symm hne)
  letI : I.IsPrime := hIprime
  letI : Q.IsPrime := hQprime
  letI : P.IsPrime := hPprime
  letI : P.LiesOver Q := ⟨rfl⟩
  obtain ⟨P', hP'P, hP'prime, hP'over⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt
      (R := R) (S := S) P hIQstrict
  have hIP' : I.map f ≤ P' := by
    rw [Ideal.map_le_iff_le_comap]
    rw [hP'over.over]
    exact le_rfl
  have hPP' : P ≤ P' := hP.2 ⟨hP'prime, hIP'⟩ hP'P.le
  exact hP'P.not_ge hPP'

end

end TranslatedDepthSeven
