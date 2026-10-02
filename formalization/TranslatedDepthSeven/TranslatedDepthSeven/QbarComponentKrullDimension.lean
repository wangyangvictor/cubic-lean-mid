import TranslatedDepthSeven.QbarCoefficientExtension
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import TranslatedDepthSeven.RationalPrimeGeometricFrontier
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Krull dimension of a geometric component over a rational prime

The coefficient map `Q[X] → Qbar[X]` is integral. Its induced map from
the quotient by a contracted prime to the geometric-prime quotient is
integral and injective, hence preserves Krull dimension. Going down
identifies that contracted prime with the original rational prime when
the geometric prime is a minimal component of its coefficient extension.
No algebraic-geometric dimension statement is an external hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

local instance {σ : Type*} :
    Algebra (MvPolynomial σ ℚ) (MvPolynomial σ Qbar) :=
  MvPolynomial.algebraMvPolynomial

/-- Dimension invariance for the integral coefficient extension on the
quotient by any prime, with its exact contraction as the source ideal. -/
theorem qbar_primeQuotient_ringKrullDim_eq_comap
    {σ : Type*} (P : Ideal (MvPolynomial σ Qbar)) (hP : P.IsPrime) :
    ringKrullDim (MvPolynomial σ Qbar ⧸ P) =
      ringKrullDim (MvPolynomial σ ℚ ⧸
        P.comap (MvPolynomial.map (algebraMap ℚ Qbar))) := by
  let R := MvPolynomial σ ℚ
  let S := MvPolynomial σ Qbar
  let f : R →+* S := MvPolynomial.map (algebraMap ℚ Qbar)
  letI : P.IsPrime := hP
  letI : (P.comap f).IsPrime := hP.comap f
  have hf : f.IsIntegral := by
    change (algebraMap R S).IsIntegral
    exact Algebra.IsIntegral.isIntegral
  let g : (R ⧸ P.comap f) →+* (S ⧸ P) := Ideal.quotientMap P f le_rfl
  letI : Algebra (R ⧸ P.comap f) (S ⧸ P) := g.toAlgebra
  letI : Algebra.IsIntegral (R ⧸ P.comap f) (S ⧸ P) :=
    ⟨RingHom.IsIntegral.quotient f hf⟩
  exact ringKrullDim_eq_of_isIntegral_injective
    (show Function.Injective g from Ideal.quotientMap_injective)

/-- Every geometric minimal component of the coefficient extension of a
rational prime has the original quotient's Krull dimension. -/
theorem qbar_minimalComponent_ringKrullDim_eq
    {σ : Type*} [Fintype σ]
    (Q : Ideal (MvPolynomial σ ℚ)) (hQ : Q.IsPrime)
    (P : Ideal (MvPolynomial σ Qbar))
    (hP : P ∈ finiteMinimalPrimes (qbarCoefficientExtensionIdeal Q)) :
    ringKrullDim (MvPolynomial σ Qbar ⧸ P) =
      ringKrullDim (MvPolynomial σ ℚ ⧸ Q) := by
  have hPmin := (mem_finiteMinimalPrimes_iff _ _).mp hP
  have hcontract : P.comap (MvPolynomial.map (algebraMap ℚ Qbar)) = Q :=
    comap_qbar_minimalPrime_map_eq_of_isPrime Q hQ P hPmin
  rw [qbar_primeQuotient_ringKrullDim_eq_comap P
    (Ideal.minimalPrimes_isPrime hPmin), hcontract]

end

end TranslatedDepthSeven
