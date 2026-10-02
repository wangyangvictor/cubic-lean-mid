import TranslatedDepthSeven.ParameterLocalizationMaximalPrime
import TranslatedDepthSeven.AffineDomainMaximalHeightInternal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Height and transcendence degree after parameter localization

The localization is the canonical tensor product `Frac(B) ⊗[B] A`.
Its field-algebra and finite-type structures come from base change.
The prime is maximal by integral incomparability, not by an assumed
dimension formula.  The already proved closed-point height theorem and
transcendence-degree addition then give the altitude identity.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe u

/-- Finite-type domains have matching finite dimension and transcendence
degree, obtained from the same actual normalization map. -/
theorem affineDomain_exists_dimension_trdeg
    (K A : Type u) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧
      Algebra.trdeg K A = (n : Cardinal) := by
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K A
  have htrdeg := trdeg_eq_nat_of_integral_injective_polynomial g hginj hgint
  let R := MvPolynomial (Fin n) K
  letI : Algebra R A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral R A := ⟨hgint⟩
  refine ⟨n, ?_, htrdeg⟩
  exact (ringKrullDim_eq_of_isIntegral_injective hginj).trans
    (ringKrullDim_mvPolynomial_fin_eq_of_field K n)

/-- An integral normalization of the quotient determines the height of its
prime via localization.  The parameter and source transcendence degrees
are displayed natural numbers; no dimension or catenarity premise occurs. -/
theorem prime_height_add_parameter_trdeg_eq
    (K B A : Type u) [Field K] [CharZero K]
    [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra K B] [Algebra K A] [Algebra B A] [IsScalarTower K B A]
    [Algebra.FiniteType B A]
    (P : Ideal A) [P.IsPrime] [Algebra.IsIntegral B (A ⧸ P)]
    (hPzero : P.comap (algebraMap B A) = ⊥)
    {r a : ℕ} (hBtrdeg : Algebra.trdeg K B = (r : Cardinal))
    (hAtrdeg : Algebra.trdeg K A = (a : Cardinal)) :
    ∃ h : ℕ, P.height = (h : ℕ∞) ∧ r + h = a := by
  have hinj : Function.Injective (algebraMap B A) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    intro b hb
    have hbP : b ∈ P.comap (algebraMap B A) := by
      change algebraMap B A b ∈ P
      change algebraMap B A b = 0 at hb
      rw [hb]
      exact P.zero_mem
    simpa only [hPzero] using hbP
  let T := (nonZeroDivisors B).map (algebraMap B A)
  have hT : T ≤ nonZeroDivisors A := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hx
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    have hb0 : b = 0 := hinj (by simpa only [map_zero] using hz)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hb0
  let L := FractionRing B
  let S := L ⊗[B] A
  letI : IsLocalization T S := IsLocalization.tensorRight L (nonZeroDivisors B)
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hT
  letI : FaithfulSMul A S :=
    (faithfulSMul_iff_algebraMap_injective A S).mpr (IsLocalization.injective S hT)
  letI : Algebra.FiniteType L S := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing L S
  letI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  letI : Algebra.IsAlgebraic A S := IsLocalization.isAlgebraic S T
  letI : IsScalarTower K A S := IsScalarTower.to₁₃₄ K B A S
  letI : CharZero L := Algebra.charZero_of_charZero K L
  have hLtrdeg : Algebra.trdeg K L = (r : Cardinal) := by
    have h := trdeg_add_eq K B (A := L)
    simpa only [trdeg_eq_zero, hBtrdeg, add_zero] using h.symm
  have hStrdeg : Algebra.trdeg K S = (a : Cardinal) := by
    have h := trdeg_add_eq K A (A := S)
    simpa only [trdeg_eq_zero, hAtrdeg, add_zero] using h.symm
  obtain ⟨n, hSdim, hntrdeg⟩ := affineDomain_exists_dimension_trdeg L S
  let P' := P.map (algebraMap A S)
  obtain ⟨hP'max, _hP'comap, hP'height⟩ :=
    parameterLocalized_prime_isMaximal_and_height (S := S) P hPzero
  letI : P'.IsMaximal := hP'max
  have hheight : P.height = (n : ℕ∞) := by
    have h := affineDomain_maximal_height_eq_dimension L S P'
    rw [hSdim] at h
    change ((P.map (algebraMap A S)).height : WithBot ℕ∞) = _ at h
    rw [hP'height] at h
    exact_mod_cast h
  refine ⟨n, hheight, ?_⟩
  have h := trdeg_add_eq K L (A := S)
  rw [hLtrdeg, hntrdeg, hStrdeg] at h
  exact_mod_cast h

end
end TranslatedDepthSeven
