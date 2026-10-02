import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import TranslatedDepthSeven.QbarPrimeAlgebraicCoefficientExtension

/-! An empty generic polynomial fiber stays empty on one base principal
open.  Localization membership of `1` supplies a literal nonzero constant
in the equation ideal.  This needs neither a Noetherian base nor finitely
many variables.  Extension from the fraction field to an arbitrary field,
including its algebraic closure, is removed by faithful-flat contraction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CubicTenVariables.GenericEmptyFiberSpreading

open MvPolynomial TranslatedDepthSeven
open scoped nonZeroDivisors

/-- An ideal which becomes the unit ideal over the fraction field contains
an actual nonzero constant from the base. -/
theorem exists_nonzero_constant_mem
    {B K σ : Type*} [CommRing B] [IsDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial σ B))
    (hgeneric : I.map (MvPolynomial.map (algebraMap B K)) = ⊤) :
    ∃ s : B, s ≠ 0 ∧ C s ∈ I := by
  letI : Algebra (MvPolynomial σ B) (MvPolynomial σ K) :=
    MvPolynomial.algebraMvPolynomial
  have hone : algebraMap (MvPolynomial σ B) (MvPolynomial σ K) 1 ∈
      I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ K)) := by
    change (MvPolynomial.map (algebraMap B K)) 1 ∈
      I.map (MvPolynomial.map (algebraMap B K))
    rw [hgeneric]
    trivial
  obtain ⟨e, he, heI⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((nonZeroDivisors B).map (C (σ := σ))) (MvPolynomial σ K) I 1).mp hone
  obtain ⟨s, hs, hse⟩ := Submonoid.mem_map.mp he
  refine ⟨s, mem_nonZeroDivisors_iff_ne_zero.mp hs, ?_⟩
  rw [← hse] at heI
  simpa only [mul_one] using heI

/-- A constant certificate survives every coefficient map which sends it
to a unit.  The target may be any commutative ring. -/
theorem map_eq_top_of_constant_mem
    {B L σ : Type*} [CommRing B] [CommRing L]
    (I : Ideal (MvPolynomial σ B)) (s : B) (hs : C s ∈ I)
    (ρ : B →+* L) (hρ : IsUnit (ρ s)) :
    I.map (MvPolynomial.map ρ) = ⊤ := by
  apply (I.map (MvPolynomial.map ρ)).eq_top_of_isUnit_mem
    (Ideal.mem_map_of_mem (MvPolynomial.map ρ) hs)
  simpa only [MvPolynomial.map_C] using hρ.map (C : L →+* MvPolynomial σ L)

/-- One nonzero base element is selected before every field specialization. -/
theorem exists_nonzero_open
    {B K σ : Type*} [CommRing B] [IsDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (I : Ideal (MvPolynomial σ B))
    (hgeneric : I.map (MvPolynomial.map (algebraMap B K)) = ⊤) :
    ∃ s : B, s ≠ 0 ∧
      ∀ (L : Type*) [Field L] (ρ : B →+* L), ρ s ≠ 0 →
        I.map (MvPolynomial.map ρ) = ⊤ := by
  obtain ⟨s, hs, hmem⟩ := exists_nonzero_constant_mem I hgeneric
  exact ⟨s, hs, fun L _ ρ hρ ↦
    map_eq_top_of_constant_mem I s hmem ρ (isUnit_iff_ne_zero.mpr hρ)⟩

/-- Emptiness after any extension of the fraction field descends to that
fraction field.  The extension need not be algebraic. -/
theorem fraction_map_eq_top_of_field_extension
    {B K Ω σ : Type*} [CommRing B] [Field K] [Field Ω]
    [Algebra B K] [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω]
    (I : Ideal (MvPolynomial σ B))
    (hgeneric : I.map (MvPolynomial.map (algebraMap B Ω)) = ⊤) :
    I.map (MvPolynomial.map (algebraMap B K)) = ⊤ := by
  have hcomp : (MvPolynomial.map (σ := σ) (algebraMap K Ω)).comp
      (MvPolynomial.map (algebraMap B K)) = MvPolynomial.map (algebraMap B Ω) := by
    apply RingHom.ext
    intro f
    simp only [RingHom.comp_apply, MvPolynomial.map_map,
      ← IsScalarTower.algebraMap_eq B K Ω]
  have htop : (I.map (MvPolynomial.map (algebraMap B K))).map
      (MvPolynomial.map (algebraMap K Ω)) = ⊤ := by
    rw [Ideal.map_map, hcomp]
    exact hgeneric
  letI : Algebra (MvPolynomial σ K) (MvPolynomial σ Ω) :=
    MvPolynomial.algebraMvPolynomial
  letI : Module.FaithfullyFlat (MvPolynomial σ K) (MvPolynomial σ Ω) :=
    mvPolynomial_faithfullyFlat
  have hcontract : ((I.map (MvPolynomial.map (algebraMap B K))).map
      (MvPolynomial.map (algebraMap K Ω))).comap
      (MvPolynomial.map (algebraMap K Ω)) = I.map (MvPolynomial.map (algebraMap B K)) :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [htop, Ideal.comap_top] at hcontract
  exact hcontract.symm

/-- The same base open can be obtained from an empty geometric generic
fiber, without an additional geometric spreading premise. -/
theorem exists_nonzero_open_of_field_extension
    {B K Ω σ : Type*} [CommRing B] [IsDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Field Ω] [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω]
    (I : Ideal (MvPolynomial σ B))
    (hgeneric : I.map (MvPolynomial.map (algebraMap B Ω)) = ⊤) :
    ∃ s : B, s ≠ 0 ∧
      ∀ (L : Type*) [Field L] (ρ : B →+* L), ρ s ≠ 0 →
        I.map (MvPolynomial.map ρ) = ⊤ :=
  exists_nonzero_open (K := K) I
    (fraction_map_eq_top_of_field_extension (K := K) I hgeneric)

/-- Caller-facing form: an arbitrary injective map into a field is enough.
The proof constructs its fraction-field factorization, so no particular
generic field or scalar-tower instances need to be supplied by the caller. -/
theorem exists_nonzero_open_of_injective
    {B Ω σ : Type*} [CommRing B] [IsDomain B] [Field Ω]
    (I : Ideal (MvPolynomial σ B)) (ι : B →+* Ω)
    (hι : Function.Injective ι)
    (hgeneric : I.map (MvPolynomial.map ι) = ⊤) :
    ∃ s : B, s ≠ 0 ∧
      ∀ (L : Type*) [Field L] (ρ : B →+* L), ρ s ≠ 0 →
        I.map (MvPolynomial.map ρ) = ⊤ := by
  let K := FractionRing B
  let κ : K →+* Ω := IsFractionRing.lift hι
  letI : Algebra B Ω := ι.toAlgebra
  letI : Algebra K Ω := κ.toAlgebra
  letI : IsScalarTower B K Ω := IsScalarTower.of_algebraMap_eq fun b ↦
    (IsFractionRing.lift_algebraMap hι b).symm
  exact exists_nonzero_open_of_field_extension (K := K) I hgeneric

end CubicTenVariables.GenericEmptyFiberSpreading
