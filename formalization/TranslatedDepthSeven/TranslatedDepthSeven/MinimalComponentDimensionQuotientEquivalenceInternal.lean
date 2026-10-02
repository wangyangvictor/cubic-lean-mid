import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic

/-! # Transfer of actual minimal-component dimensions through a quotient isomorphism -/

namespace TranslatedDepthSeven

noncomputable section
set_option maxHeartbeats 1000000

theorem ringKrullDim_minimalComponent_of_quotient_equiv
    {R C : Type*} [CommRing R] [CommRing C]
    (I : Ideal R) (E : (R ⧸ I) ≃+* C) (d : WithBot ℕ∞)
    (hC : ∀ Q ∈ minimalPrimes C, ringKrullDim (C ⧸ Q) = d)
    (P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ringKrullDim (R ⧸ P) = d := by
  let g : R →+* C := E.toRingHom.comp (Ideal.Quotient.mk I)
  have hg : Function.Surjective g := E.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = I := by
    ext x
    change E (Ideal.Quotient.mk I x) = 0 ↔ x ∈ I
    rw [map_eq_zero_iff E E.injective, Ideal.Quotient.eq_zero_iff_mem]
  let Q := P.map g
  have hQ : Q ∈ minimalPrimes C := by
    change Q ∈ (⊥ : Ideal C).minimalPrimes
    rw [← Ideal.map_bot (f := g), Ideal.minimalPrimes_map_of_surjective hg]
    refine ⟨P, ?_, rfl⟩
    simpa only [hker, bot_sup_eq] using hP
  let f : R →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hg
  have hfker : RingHom.ker f = P := by
    change (RingHom.ker (Ideal.Quotient.mk Q)).comap g = P
    rw [Ideal.mk_ker]
    change (P.map g).comap g = P
    rw [Ideal.comap_map_of_surjective g hg, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hP.1.2]
  have hdim := (f.quotientKerEquivOfSurjective hf).ringKrullDim
  rw [hfker] at hdim
  exact hdim.trans (hC Q hQ)

end
end TranslatedDepthSeven
