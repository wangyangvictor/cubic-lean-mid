import TranslatedDepthSeven.FiniteTorsionFreeBaseChangeInternal
import TranslatedDepthSeven.PrimeAffineNoetherNormalization
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Dimension of components of a finite torsion-free algebra

Every minimal prime avoids nonzero elements of the base domain. The
induced algebra on each reduced component is therefore finite and
injective, so integral-extension dimension gives exactly the dimension
of the base. This remains true after any flat extension to a domain.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem ringKrullDim_quotient_eq_of_finite_torsionFree_minimalPrime
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [NoZeroSMulDivisors R A]
    (P : Ideal A) (hP : P ∈ minimalPrimes A) :
    ringKrullDim (A ⧸ P) = ringKrullDim R := by
  letI : P.IsPrime := hP.1.1
  haveI : Module.Finite R (A ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral R (A ⧸ P) := Algebra.IsIntegral.of_finite R (A ⧸ P)
  exact ringKrullDim_eq_of_isIntegral_injective
    (algebraMap_quotient_injective_of_torsionFree_minimalPrime R A P hP)

theorem ringKrullDim_baseChange_component_eq_of_finite_torsionFree
    (R S A : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Flat R S]
    [CommRing A] [Algebra R A] [Module.Finite R A] [NoZeroSMulDivisors R A]
    (P : Ideal (S ⊗[R] A)) (hP : P ∈ minimalPrimes (S ⊗[R] A)) :
    ringKrullDim ((S ⊗[R] A) ⧸ P) = ringKrullDim S := by
  letI := noZeroSMulDivisors_baseChange_of_finite_torsionFree R S A
  exact ringKrullDim_quotient_eq_of_finite_torsionFree_minimalPrime S (S ⊗[R] A) P hP

end
end TranslatedDepthSeven
