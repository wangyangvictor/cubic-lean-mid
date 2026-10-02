import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# A prime becomes maximal after inverting its normalization parameters

Suppose `A/P` is integral over a parameter domain `B` which injects into
`A/P`.  Invert the images in `A` of all nonzero elements of `B`.
The extension of `P` is maximal: any larger prime would give a nonzero
prime in `A/P` contracting to zero in `B`, contrary to integral
incomparability.  The exact localization ideal correspondence also proves
that its height is unchanged.

This argument requires no fraction-field scalar structure on the quotient
and no component-dimension statement.  A finite normalization supplies its
integrality hypothesis directly.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- Integral incomparability in a quotient, with the parameter contraction
displayed literally.  Primality of the larger ideal is not needed. -/
theorem eq_of_le_of_integral_primeQuotient_of_parameterContraction_eq_bot
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (P Q : Ideal A) [P.IsPrime] [Algebra.IsIntegral B (A ⧸ P)]
    (hPQ : P ≤ Q) (hQzero : Q.comap (algebraMap B A) = ⊥) : Q = P := by
  apply le_antisymm _ hPQ
  intro x hxQ
  by_contra hxP
  let Q' := Q.map (Ideal.Quotient.mk P)
  have hxQ' : Ideal.Quotient.mk P x ∈ Q' :=
    Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hxQ
  have hxne : Ideal.Quotient.mk P x ≠ 0 := by
    intro hz
    exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hcontraction : Q'.comap (algebraMap B (A ⧸ P)) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq B A (A ⧸ P), ← Ideal.comap_comap]
    change ((Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P)).comap
      (algebraMap B A) = ⊥
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hPQ, hQzero]
  letI : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.bot_prime
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff
    (I := (⊥ : Ideal (A ⧸ P))) (J := Q') bot_le
    ⟨hxQ', by simpa only [Ideal.mem_bot] using hxne⟩
    (Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk P x))
  rw [hcontraction] at hlt
  exact not_lt_bot hlt

theorem parameterContraction_eq_bot_iff_disjoint_nonzeroImages
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    (Q : Ideal A) :
    Q.comap (algebraMap B A) = ⊥ ↔
      Disjoint (((nonZeroDivisors B).map (algebraMap B A) : Submonoid A) : Set A)
        (Q : Set A) := by
  constructor
  · intro hzero
    apply Set.disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hx
    have hbQ : b ∈ Q.comap (algebraMap B A) := hxQ
    rw [hzero, Ideal.mem_bot] at hbQ
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hbQ
  · intro hdisjoint
    apply le_antisymm _ bot_le
    intro b hb
    by_contra hbne
    have hbnz : b ≠ 0 := by simpa only [Ideal.mem_bot] using hbne
    exact (Set.disjoint_left.mp hdisjoint)
      (Submonoid.mem_map.mpr ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hbnz, rfl⟩) hb

/-- Localizing at all nonzero parameters makes the prime maximal, with
exact contraction and unchanged height.  The localization itself may be
any ring realizing the displayed submonoid localization. -/
theorem parameterLocalized_prime_isMaximal_and_height
    {B A S : Type*} [CommRing B] [IsDomain B] [CommRing A] [CommRing S]
    [Algebra B A] [Algebra A S]
    [IsLocalization ((nonZeroDivisors B).map (algebraMap B A)) S]
    (P : Ideal A) [P.IsPrime] [Algebra.IsIntegral B (A ⧸ P)]
    (hPzero : P.comap (algebraMap B A) = ⊥) :
    (P.map (algebraMap A S)).IsMaximal ∧
      (P.map (algebraMap A S)).comap (algebraMap A S) = P ∧
      (P.map (algebraMap A S)).height = P.height := by
  let T := (nonZeroDivisors B).map (algebraMap B A)
  have hdisjoint := (parameterContraction_eq_bot_iff_disjoint_nonzeroImages P).mp hPzero
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint T S P inferInstance hdisjoint
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint T S P inferInstance hdisjoint
  have hmax : (P.map (algebraMap A S)).IsMaximal := by
    obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal _ hprime.ne_top
    letI : M.IsMaximal := hMmax
    let Q := M.comap (algebraMap A S)
    have hPQ : P ≤ Q := by
      rw [← hcomap]
      exact Ideal.comap_mono hPM
    have hQdisjoint : Disjoint (T : Set A) (Q : Set A) :=
      ((IsLocalization.isPrime_iff_isPrime_disjoint T S M).mp inferInstance).2
    have hQzero := (parameterContraction_eq_bot_iff_disjoint_nonzeroImages Q).mpr hQdisjoint
    have hQP : Q = P :=
      eq_of_le_of_integral_primeQuotient_of_parameterContraction_eq_bot P Q hPQ hQzero
    have hMP : M = P.map (algebraMap A S) := by
      rw [← IsLocalization.map_comap T S M]
      exact congrArg (Ideal.map (algebraMap A S)) hQP
    exact hMP ▸ hMmax
  refine ⟨hmax, hcomap, ?_⟩
  have hheight := IsLocalization.height_comap T (P.map (algebraMap A S))
  rw [hcomap] at hheight
  exact hheight.symm

end
end TranslatedDepthSeven
