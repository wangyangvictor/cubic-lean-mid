import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Actual descent of a derivation through a quotient ideal, including
a linear equivalence with the ideal-annihilating derivations upstairs. -/

noncomputable section
namespace HessianTheorem11.UnconditionalGeneric

variable (K A F : Type*) [CommRing K] [CommRing A] [CommRing F]
  [Algebra K A] [Algebra K F] [Algebra A F] [IsScalarTower K A F]
  (I : Ideal A) [Algebra (A ⧸ I) F] [IsScalarTower A (A ⧸ I) F]
  [IsScalarTower K (A ⧸ I) F]

def annihilatingDerivations : Submodule F (Derivation K A F) where
  carrier := {D | ∀p∈I,D p=0}
  zero_mem' := by simp
  add_mem' := by intro D E hD hE p hp; simp [hD p hp,hE p hp]
  smul_mem' := by intro a D hD p hp; simp [hD p hp]

/-- The construction descends the underlying linear map and proves the
Leibniz rule on representatives; no quotient differential theorem is assumed. -/
def quotientDerivation (D : Derivation K A F) (hD : ∀p∈I,D p=0) :
    Derivation K (A ⧸ I) F where
  toLinearMap := (I.restrictScalars K).liftQ D.toLinearMap hD
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' a b := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
    change D (a*b) = (Ideal.Quotient.mk I a) • D b + (Ideal.Quotient.mk I b) • D a
    rw [D.leibniz]
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply A (A ⧸ I) F]
    rfl

@[simp] theorem quotientDerivation_mk (D : Derivation K A F) (hD : ∀p∈I,D p=0)
    (a : A) : quotientDerivation K A F I D hD (Ideal.Quotient.mk I a) = D a := rfl

/-- Restriction to representatives, as a map linear over the coefficient
algebra in which the derivations take their values. -/
def quotientDerivationRestriction :
    Derivation K (A ⧸ I) F →ₗ[F] annihilatingDerivations K A F I where
  toFun D := ⟨D.compAlgebraMap A, by
    intro p hp
    change D (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quotient_derivation_restriction_bijective :
    Function.Bijective (quotientDerivationRestriction K A F I) := by
  constructor
  · intro D E h
    apply Derivation.ext
    intro a
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Derivation.congr_fun (congrArg Subtype.val h) a
  · intro D
    refine ⟨quotientDerivation K A F I D.val D.property, ?_⟩
    apply Subtype.ext
    apply Derivation.ext
    intro a
    rfl

def quotientDerivationEquiv :
    Derivation K (A ⧸ I) F ≃ₗ[F] annihilatingDerivations K A F I :=
  LinearEquiv.ofBijective (quotientDerivationRestriction K A F I)
    (quotient_derivation_restriction_bijective K A F I)

end HessianTheorem11.UnconditionalGeneric
