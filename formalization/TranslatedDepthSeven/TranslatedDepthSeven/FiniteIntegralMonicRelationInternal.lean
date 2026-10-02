import TranslatedDepthSeven.ProjectiveDegreeTwoAlgebra
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Monic relations bounded by the generic module rank

For a finite extension of domains over an integrally closed base, the
minimal polynomial over the base is the minimal polynomial over its
fraction field.  Its degree is therefore at most the generic module rank.
This is ordinary commutative algebra and contains no geometric degree
or counting premise.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped nonZeroDivisors

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

universe u

/-- A monic annihilator over the original normal domain has degree at most
the rank of the finite module at the generic point. -/
theorem exists_monic_annihilator_natDegree_le_localized_rank
    {B A : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [CommRing A] [IsDomain A] [Algebra B A]
    [FaithfulSMul B A] [Module.Finite B A] (x : A) :
    ∃ p : Polynomial B, p.Monic ∧
      p.natDegree ≤ Module.finrank (FractionRing B)
        (LocalizedModule (nonZeroDivisors B) A) ∧
      Polynomial.aeval x p = 0 := by
  let F := FractionRing B
  let L := FractionRing A
  letI : Algebra F L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B F L := FractionRing.isScalarTower_liftAlgebra B L
  have hx : IsIntegral B x := Algebra.IsIntegral.isIntegral x
  have hEq : Module.finrank F (LocalizedModule (nonZeroDivisors B) A) =
      Module.finrank F L :=
    localizedModule_finrank_eq_fractionRing_finrank (B := B) (A := A)
  have hpositive : 0 < Module.finrank F (LocalizedModule (nonZeroDivisors B) A) := by
    let f := LocalizedModule.mkLinearMap (nonZeroDivisors B) A
    have hf : Function.Injective f := by
      apply (IsLocalizedModule.injective_iff_isRegular
        (S := nonZeroDivisors B) (f := f)).mpr
      intro c a b hab
      change (c : B) • a = (c : B) • b at hab
      rw [Algebra.smul_def, Algebra.smul_def] at hab
      exact mul_left_cancel₀
        (map_ne_zero_of_mem_nonZeroDivisors (algebraMap B A)
          (FaithfulSMul.algebraMap_injective B A) c.property) hab
    letI : Nontrivial (LocalizedModule (nonZeroDivisors B) A) := hf.nontrivial
    exact Module.finrank_pos
  haveI : FiniteDimensional F L :=
    FiniteDimensional.of_finrank_pos (by rw [← hEq]; exact hpositive)
  refine ⟨minpoly B x, minpoly.monic hx, ?_, minpoly.aeval B x⟩
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions F L hx
  calc
    (minpoly B x).natDegree =
        ((minpoly B x).map (algebraMap B F)).natDegree :=
      ((minpoly.monic hx).natDegree_map (algebraMap B F)).symm
    _ = (minpoly F (algebraMap A L x)).natDegree := congrArg Polynomial.natDegree hmap.symm
    _ ≤ Module.finrank F L := minpoly.natDegree_le (algebraMap A L x)
    _ = Module.finrank F (LocalizedModule (nonZeroDivisors B) A) := hEq.symm

end

end TranslatedDepthSeven
