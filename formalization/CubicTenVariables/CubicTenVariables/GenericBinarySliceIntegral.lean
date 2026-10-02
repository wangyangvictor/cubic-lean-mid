import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import CubicTenVariables.BinarySliceGeometry

/-! Passing an irreducible multivariate polynomial to the fraction field
of its coefficient ring preserves an integral principal quotient whenever
the polynomial has positive degree in the retained variables. The proof
localizes the prime principal ideal and checks disjointness by total degree.
This proves integrality, not geometric integrality after further extension. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GenericBinarySliceIntegral
open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A positive-degree polynomial cannot divide a nonzero coefficient
constant. Therefore its principal ideal avoids every denominator used
when passing to the fraction field of the coefficient ring. -/
theorem span_disjoint_coefficient_nonZeroDivisors
    {R σ : Type*} [CommRing R] [IsDomain R]
    (f : MvPolynomial σ R) (hdegree : 0 < f.totalDegree) :
    Disjoint (((nonZeroDivisors R).map (C (σ := σ))) : Set (MvPolynomial σ R))
      (Ideal.span ({f} : Set (MvPolynomial σ R)) : Set (MvPolynomial σ R)) := by
  apply Set.disjoint_left.mpr
  intro g hg hgf
  obtain ⟨r,hr,rfl⟩ := Submonoid.mem_map.mp hg
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hdiv : f ∣ C r := Ideal.mem_span_singleton.mp hgf
  have hle := totalDegree_le_of_dvd_of_isDomain hdiv (C_ne_zero.mpr hr0)
  rw [totalDegree_C] at hle
  omega

/-- The actual mapped principal ideal is prime, with no primitivity or
irreducibility of the fraction-field polynomial assumed as an input. -/
theorem isPrime_span_map
    {R σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : MvPolynomial σ R) (hf : Irreducible f) (hdegree : 0 < f.totalDegree) :
    (Ideal.span ({map (algebraMap R (FractionRing R)) f} :
      Set (MvPolynomial σ (FractionRing R)))).IsPrime := by
  have hprime : (Ideal.span ({f} : Set (MvPolynomial σ R))).IsPrime :=
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf.prime
  have hmap := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors R).map (C (σ := σ))) (MvPolynomial σ (FractionRing R))
    (Ideal.span ({f} : Set (MvPolynomial σ R))) hprime
    (span_disjoint_coefficient_nonZeroDivisors f hdegree)
  simpa only [Ideal.map_span,Set.image_singleton,MvPolynomial.algebraMap_def] using hmap

/-- The generic hypersurface over the coefficient fraction field is
integral. Positive degree excludes the case where localization makes f a unit. -/
theorem isDomain_quotient_map
    {R σ : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : MvPolynomial σ R) (hf : Irreducible f) (hdegree : 0 < f.totalDegree) :
    IsDomain (MvPolynomial σ (FractionRing R) ⧸
      Ideal.span ({map (algebraMap R (FractionRing R)) f} :
        Set (MvPolynomial σ (FractionRing R)))) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (isPrime_span_map f hf hdegree)

/-- The actual selected-coordinate family has an integral generic binary
fiber. Its irreducibility comes from the original ambient polynomial
through the proved variable-splitting equivalence. -/
theorem isDomain_generic_family {K : Type*} [Field K] {n : ℕ}
    (e : Fin 2 ↪ Fin n) (F : MvPolynomial (Fin n) K) (hF : Irreducible F)
    (hdegree : 0 < (BinarySliceGeometry.family e F).totalDegree) :
    IsDomain (MvPolynomial (Fin 2)
        (FractionRing (MvPolynomial (BinarySliceCounting.Complement e) K)) ⧸
      Ideal.span ({map
        (algebraMap (MvPolynomial (BinarySliceCounting.Complement e) K)
          (FractionRing (MvPolynomial (BinarySliceCounting.Complement e) K)))
        (BinarySliceGeometry.family e F)} : Set (MvPolynomial (Fin 2)
          (FractionRing (MvPolynomial (BinarySliceCounting.Complement e) K))))) := by
  have hfamily : Irreducible (BinarySliceGeometry.family e F) :=
    (MulEquiv.irreducible_iff (BinarySliceGeometry.familyEquiv K e)).mpr hF
  exact isDomain_quotient_map (BinarySliceGeometry.family e F) hfamily hdegree

end CubicTenVariables.GenericBinarySliceIntegral
