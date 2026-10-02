import TranslatedDepthSeven.FiniteNormalDomainMinpolyDerivativeInternal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# A primitive integral coordinate has minimal-polynomial degree equal to rank

This records the exact equality over the original normal domain, not just
over its fraction field. It is used with an actual bounded primitive linear
coordinate, not assumed as a geometric projection property.
-/

namespace TranslatedDepthSeven
noncomputable section
open scoped nonZeroDivisors
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
universe u

theorem minpoly_natDegree_eq_localized_rank_of_primitive
    {B A : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [FaithfulSMul B A] [Module.Finite B A] (x : A)
    (hprimitive :
      letI : Algebra (FractionRing B) (FractionRing A) :=
        FractionRing.liftAlgebra B (FractionRing A)
      IntermediateField.adjoin (FractionRing B)
        ({algebraMap A (FractionRing A) x} : Set (FractionRing A)) = ⊤) :
    (minpoly B x).natDegree = Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A) := by
  let F := FractionRing B
  let L := FractionRing A
  letI : Algebra F L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B F L := FractionRing.isScalarTower_liftAlgebra B L
  have hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  have hFx : IsIntegral F (algebraMap A L x) := hx.algebraMap.tower_top
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions F L hx
  calc
    (minpoly B x).natDegree =
        ((minpoly B x).map (algebraMap B F)).natDegree :=
      ((minpoly.monic hx).natDegree_map (algebraMap B F)).symm
    _ = (minpoly F (algebraMap A L x)).natDegree :=
      congrArg Polynomial.natDegree hmap.symm
    _ = Module.finrank F
        (IntermediateField.adjoin F ({algebraMap A L x} : Set L)) :=
      (IntermediateField.adjoin.finrank hFx).symm
    _ = Module.finrank F L := by
      rw [hprimitive]
      exact IntermediateField.finrank_top'
    _ = Module.finrank F (LocalizedModule (nonZeroDivisors B) A) :=
      (localizedModule_finrank_eq_fractionRing_finrank (B := B) (A := A)).symm

end
end TranslatedDepthSeven
