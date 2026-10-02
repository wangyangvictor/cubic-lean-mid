import TranslatedDepthSeven.FiniteIntegralMonicRelationInternal
import Mathlib.FieldTheory.Separable

/-!
# Minimal-polynomial degree and derivative at the generic point

Separability is used over the fraction field, not over the normal
parameter ring.  Over that ring the minimal polynomial need not be
coprime to its derivative.  The conclusion below is only that the
derivative has nonzero value in the domain, exactly as needed for a
generic conormal calculation.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

universe u

/-- The actual minimal polynomial, not just some annihilator, has degree
at most the generic rank of the finite module. -/
theorem minpoly_natDegree_le_localized_rank
    {B A : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [FaithfulSMul B A] [Module.Finite B A] (x : A) :
    (minpoly B x).natDegree ≤ Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
  obtain ⟨p, hpmonic, hpdegree, hproot⟩ :=
    exists_monic_annihilator_natDegree_le_localized_rank (B := B) x
  exact (Polynomial.natDegree_le_natDegree (minpoly.min B x hpmonic hproot)).trans hpdegree

/-- Characteristic zero makes the generic minimal polynomial separable.
Its derivative therefore has nonzero value in the original domain. -/
theorem minpoly_aeval_derivative_ne_zero_of_finite_normal_domain
    {B A : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [CharZero B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [FaithfulSMul B A] [Module.Finite B A] (x : A) :
    Polynomial.aeval x (Polynomial.derivative (minpoly B x)) ≠ 0 := by
  let F := FractionRing B
  let L := FractionRing A
  letI : Algebra F L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B F L := FractionRing.isScalarTower_liftAlgebra B L
  have hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  have hnonzero : Polynomial.aeval (algebraMap A L x)
      (Polynomial.derivative (minpoly F (algebraMap A L x))) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable F (algebraMap A L x)).aeval_derivative_ne_zero
      (minpoly.aeval F (algebraMap A L x))
  have hmap : algebraMap A L
      (Polynomial.aeval x (Polynomial.derivative (minpoly B x))) ≠ 0 := by
    rwa [minpoly.isIntegrallyClosed_eq_field_fractions F L hx,
      Polynomial.derivative_map, Polynomial.aeval_map_algebraMap,
      Polynomial.aeval_algebraMap_apply] at hnonzero
  intro hzero
  apply hmap
  rw [hzero, map_zero]

end

end TranslatedDepthSeven
