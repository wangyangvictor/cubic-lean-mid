import TranslatedDepthSeven.FiniteComponentFrontier
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# A surjection between domains cannot preserve dimension with nonzero kernel

A nonzero prime kernel strictly decreases finite Krull dimension. Thus a
surjection is injective when the target dimension is at least the source
dimension. The rings need not be finitely generated: this applies directly
to local rings after their dimension bounds have been proved.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

set_option maxHeartbeats 1000000

/-- A surjection of domains of finite source dimension is injective if
the target dimension is at least the source dimension. -/
theorem injective_of_surjective_of_domain_dimension_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    (f : A →+* B) (hsurj : Function.Surjective f)
    (hfinite : ringKrullDim A < ⊤)
    (hdim : ringKrullDim A ≤ ringKrullDim B) :
    Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  by_contra hker
  letI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
  letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hstrict : (⊥ : Ideal A) < RingHom.ker f := bot_lt_iff_ne_bot.mpr hker
  have hbot : ringKrullDim (A ⧸ (⊥ : Ideal A)) = ringKrullDim A :=
    RingEquiv.ringKrullDim (RingEquiv.quotientBot A)
  have hquot : ringKrullDim (A ⧸ RingHom.ker f) = ringKrullDim B :=
    RingEquiv.ringKrullDim (f.quotientKerEquivOfSurjective hsurj)
  have hdrop := ringKrullDim_quotient_lt_of_prime_lt
    (⊥ : Ideal A) (RingHom.ker f) hstrict (hbot.symm ▸ hfinite)
  rw [hbot, hquot] at hdrop
  exact (not_lt_of_ge hdim) hdrop

/-- The convenient bounded-dimension version: an upper bound for the
source and the matching lower bound for the target give bijectivity. -/
theorem bijective_of_surjective_of_domain_dimension_bounds
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B]
    (f : A →+* B) (hsurj : Function.Surjective f) (n : ℕ)
    (hsource : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (htarget : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    Function.Bijective f := by
  refine ⟨injective_of_surjective_of_domain_dimension_le f hsurj ?_
    (hsource.trans htarget), hsurj⟩
  apply hsource.trans_lt
  exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top n)

end

end TranslatedDepthSeven
