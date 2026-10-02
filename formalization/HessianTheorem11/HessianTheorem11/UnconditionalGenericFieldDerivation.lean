import HessianTheorem11.UnconditionalGenericFieldSmooth
import HessianTheorem11.UnconditionalGenericDerivation

/-! Extension and dimension of derivations with values in a larger field. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open Module
open scoped TensorProduct nonZeroDivisors

section Dual
variable (K E L : Type*) [CommRing K] [CommRing E] [CommRing L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

def valuedDifferentialDualEquiv :
    Module.Dual L (L ⊗[E] KaehlerDifferential K E) ≃ₗ[L] Derivation K E L := by
  let e := KaehlerDifferential.linearMapEquivDerivation K E (M := L)
  let e' : (KaehlerDifferential K E →ₗ[E] L) ≃ₗ[L] Derivation K E L :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := fun a f => by apply Derivation.ext; intro x; rfl }
  exact (LinearMap.liftBaseChangeEquiv L).symm.trans e'

@[simp] theorem valuedDifferentialDualEquiv_apply
    (l : Module.Dual L (L ⊗[E] KaehlerDifferential K E)) (a : E) :
    valuedDifferentialDualEquiv K E L l a = l (1 ⊗ₜ KaehlerDifferential.D K E a) := rfl

end Dual

section Fields
variable (K E L : Type*) [Field K] [Field E] [Field L] [CharZero E]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]

/-- Every derivation of a characteristic-zero subfield extends to a larger
field, with values in that larger field. This is dual to the proved injection
on Kähler differentials. -/
theorem field_derivation_restriction_surjective :
    Function.Surjective (Derivation.compAlgebraMapL K E L L) := by
  intro d
  let e := valuedDifferentialDualEquiv K E L
  obtain ⟨l,hl⟩ := LinearMap.dualMap_surjective_of_injective
    (field_differentials_injective K E L) (e.symm d)
  refine ⟨l.compDer (KaehlerDifferential.D K L), ?_⟩
  apply Derivation.ext
  intro a
  have he := LinearMap.congr_fun hl (1 ⊗ₜ KaehlerDifferential.D K E a)
  change l (KaehlerDifferential.D K L (algebraMap E L a)) = d a
  calc
    _ = e (e.symm d) a := by
      simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply,
        KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
        ← valuedDifferentialDualEquiv_apply] using he
    _ = d a := congrArg (fun d : Derivation K E L => d a) (e.apply_symm_apply d)

omit [CharZero E] in
theorem valued_field_derivation_finrank
    [FiniteDimensional E (KaehlerDifferential K E)] :
    finrank L (Derivation K E L) = finrank E (KaehlerDifferential K E) := by
  rw [← (valuedDifferentialDualEquiv K E L).finrank_eq,
    Subspace.dual_finrank_eq, Module.finrank_baseChange]

end Fields

section Fractions
variable (K A E L : Type*) [CommRing K] [CommRing A] [Field E] [Field L]
  [Algebra K A] [Algebra K E] [Algebra K L]
  [Algebra A E] [Algebra A L] [Algebra E L]
  [IsScalarTower K A E] [IsScalarTower K A L]
  [IsScalarTower K E L] [IsScalarTower A E L] [IsFractionRing A E]

/-- Fraction-field extension for derivations taking values in a field beyond
the fraction field. -/
theorem valued_fraction_derivation_restriction_bijective :
    Function.Bijective (fun d : Derivation K E L => d.compAlgebraMap A) := by
  constructor
  · intro d e h
    apply Derivation.ext
    intro x
    obtain ⟨a,b,rfl⟩ := IsLocalization.exists_mk'_eq A⁰ x
    rw [IsFractionRing.mk'_eq_div,d.leibniz_div,e.leibniz_div]
    have ha := Derivation.congr_fun h a
    have hb := Derivation.congr_fun h (b : A)
    change d (algebraMap A E a) = e (algebraMap A E a) at ha
    change d (algebraMap A E b) = e (algebraMap A E b) at hb
    rw [ha,hb]
  · intro d
    letI : Algebra.FormallyEtale A E := Algebra.FormallyEtale.of_isLocalization A⁰
    let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A E
    let l : KaehlerDifferential K E →ₗ[E] L :=
      (d.liftKaehlerDifferential.liftBaseChange E).comp e.symm.toLinearMap
    refine ⟨l.compDer (KaehlerDifferential.D K E), ?_⟩
    apply Derivation.ext
    intro a
    change d.liftKaehlerDifferential.liftBaseChange E
      (e.symm (KaehlerDifferential.D K E (algebraMap A E a))) = d a
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
    simp

def valuedFractionDerivationEquiv :
    Derivation K E L ≃ₗ[L] Derivation K A L :=
  LinearEquiv.ofBijective
    { toFun := fun d => d.compAlgebraMap A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (valued_fraction_derivation_restriction_bijective K A E L)

end Fractions
end HessianTheorem11.UnconditionalGeneric
