import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.HomogeneousIdealBridge
import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Minimal components of a homogeneous ideal are homogeneous

The homogeneous core of a prime ideal in an ordered graded commutative ring
is prime.  If the prime is minimal over a homogeneous ideal, its homogeneous
core still contains that ideal; minimality therefore forces equality.  This
shows that extracting a minimal-prime component and giving it the reduced
integral structure preserves homogeneity in the same step.

The result does not prove projective saturation, exclude the irrelevant
ideal, or bound component degrees and equations.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

/-- Every minimal prime over a homogeneous ideal is homogeneous. -/
theorem isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    {ι : Type u} {σ : Type v} {A : Type w}
    [CommRing A]
    [AddCommMonoid ι] [LinearOrder ι] [IsOrderedCancelAddMonoid ι]
    [SetLike σ A] [AddSubmonoidClass σ A]
    {𝒜 : ι → σ} [GradedRing 𝒜]
    {I P : Ideal A}
    (hI : I.IsHomogeneous 𝒜)
    (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous 𝒜 := by
  have hPprime : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hIcore : I ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono 𝒜 hP.1.2)
  have hcoreP : (P.homogeneousCore 𝒜).toIdeal ≤ P :=
    Ideal.toIdeal_homogeneousCore_le 𝒜 P
  have hPcore : P ≤ (P.homogeneousCore 𝒜).toIdeal :=
    hP.2 ⟨hPprime.homogeneousCore, hIcore⟩ hcoreP
  rw [Ideal.IsHomogeneous.iff_eq]
  exact le_antisymm hcoreP hPcore

variable {K : Type u} {ν : Type v} [Field K]

local instance mvPolynomialMinimalComponentsGradedAlgebra :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule ν K) :=
  MvPolynomial.gradedAlgebra

/-- Concrete finite-equation specialization for the standard total-degree
grading of a multivariable polynomial ring. -/
theorem finiteEquationMinimalPrime_isHomogeneous
    [Fintype ν]
    (equations : Finset (MvPolynomial ν K))
    (hhom : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    {P : Ideal (MvPolynomial ν K)}
    (hP : P ∈ finiteEquationMinimalPrimes equations) :
    P.IsHomogeneous (MvPolynomial.homogeneousSubmodule ν K) := by
  have hI : (finiteEquationIdeal equations).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule ν K) := by
    apply Ideal.homogeneous_span
    intro f hf
    exact hhom f hf
  apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hI
  exact (mem_finiteEquationMinimalPrimes_iff equations P).mp hP

/-- The same selected ideal is prime, so its quotient is the integral
coordinate ring of the reduced irreducible component. -/
theorem finiteEquationMinimalPrime_isPrime
    [Fintype ν]
    (equations : Finset (MvPolynomial ν K))
    {P : Ideal (MvPolynomial ν K)}
    (hP : P ∈ finiteEquationMinimalPrimes equations) :
    P.IsPrime := by
  apply isPrime_of_mem_finiteMinimalPrimes
  exact hP

/-- Reduction and irreducible-component extraction occur in one step:
quotienting by a selected minimal prime gives a reduced ring (indeed, a
domain). -/
theorem finiteEquationMinimalPrime_quotient_isReduced
    [Fintype ν]
    (equations : Finset (MvPolynomial ν K))
    {P : Ideal (MvPolynomial ν K)}
    (hP : P ∈ finiteEquationMinimalPrimes equations) :
    IsReduced (MvPolynomial ν K ⧸ P) := by
  letI : P.IsPrime := finiteEquationMinimalPrime_isPrime equations hP
  infer_instance

end

end TranslatedDepthSeven
