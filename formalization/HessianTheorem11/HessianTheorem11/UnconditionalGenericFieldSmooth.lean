import HessianTheorem11.UnconditionalGenericDifferentials
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Algebraic.Integral

/-! Field extensions in characteristic zero are formally smooth. The proof
chooses an actual transcendence basis, uses the fraction field of its
polynomial algebra, and applies the proved separable-extension theorem. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open MvPolynomial
open scoped nonZeroDivisors

/-- No finite-generation hypothesis is required here. -/
theorem field_formallySmooth (K L : Type*) [Field K] [CharZero K]
    [Field L] [Algebra K L] : Algebra.FormallySmooth K L := by
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis K L
  let x : s → L := Subtype.val
  let P := MvPolynomial s K
  let Q := FractionRing P
  let S := IntermediateField.adjoin K (Set.range x)
  have hx : AlgebraicIndependent K x := hs.1
  letI : Algebra P L := (aeval x).toAlgebra
  letI : IsScalarTower K P L := IsScalarTower.of_algHom (aeval x)
  letI : FaithfulSMul P L :=
    (faithfulSMul_iff_algebraMap_injective P L).mpr hx
  letI : Algebra Q L := FractionRing.liftAlgebra P L
  letI : IsScalarTower P Q L := FractionRing.isScalarTower_liftAlgebra P L
  let e : Q ≃ₐ[K] S := hx.aevalEquivField
  letI : Algebra Q S := e.toAlgHom.toAlgebra
  letI : IsScalarTower Q S L := IsScalarTower.of_algebraMap_eq (fun q => by
    change IsFractionRing.lift (FaithfulSMul.algebraMap_injective P L) q = (e q : L)
    exact (hx.aevalEquivField_apply_coe q).symm)
  letI : Algebra.IsIntegral Q S := Algebra.isIntegral_of_surjective e.surjective
  letI : Algebra.IsAlgebraic S L := hs.isAlgebraic_field
  letI : Algebra.IsAlgebraic Q L := Algebra.IsAlgebraic.trans Q S L
  letI : Algebra.FormallyEtale P Q := Algebra.FormallyEtale.of_isLocalization P⁰
  letI : Algebra.FormallyEtale Q L := Algebra.FormallyEtale.of_isSeparable Q L
  letI : Algebra.FormallyEtale P L := Algebra.FormallyEtale.comp P Q L
  exact Algebra.FormallySmooth.comp K P L

/-- In characteristic zero, differentials from a subfield remain linearly
independent after extending scalars to the larger field. -/
theorem field_differentials_injective (K E L : Type*) [Field K]
    [Field E] [Field L] [CharZero E]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] :
    Function.Injective (KaehlerDifferential.mapBaseChange K E L) := by
  letI : Algebra.FormallySmooth E L := field_formallySmooth E L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y,rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange K E L x).mp hx
  rw [Subsingleton.elim y 0,map_zero]

end HessianTheorem11.UnconditionalGeneric
