import TranslatedDepthSeven.SurjectivePointLocalizationInternal
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# Coordinate-compatible localization of a quotient

The local ring of a closed subscheme is the quotient of the ambient local
ring by the extended defining ideal.  The construction records its action
on every numerator, so that actual coordinate differences can be carried
between the two presentations used in the Bertini argument.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Quotienting a marked local ring agrees with localizing the quotient.
This formulation allows an explicitly presented surjective coordinate map. -/
theorem bertini_exists_localization_quotient_equiv
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (g : A →ₐ[K] B) (hg : Function.Surjective g)
    (M : Ideal A) (N : Ideal B) [M.IsPrime] [N.IsPrime]
    (hMN : M = N.comap g) (I : Ideal A) (hI : RingHom.ker g = I) :
    ∃ e : (Localization.AtPrime M ⧸
        I.map (algebraMap A (Localization.AtPrime M))) ≃ₐ[K]
        Localization.AtPrime N,
      ∀ a : A, e (Ideal.Quotient.mk _
        (algebraMap A (Localization.AtPrime M) a)) =
          algebraMap B (Localization.AtPrime N) (g a) := by
  obtain ⟨φ, hsurj, hcomp⟩ :=
    exists_surjective_pointLocalizationAlgHom g hg M N hMN
  let f := algebraMap A (Localization.AtPrime M)
  have hφ (a : A) : φ (f a) =
      algebraMap B (Localization.AtPrime N) (g a) :=
    DFunLike.congr_fun hcomp a
  have hker : RingHom.ker φ = I.map f := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl z
      rw [IsLocalization.mk'_mem_iff]
      have ha0 : algebraMap B (Localization.AtPrime N) (g a) = 0 := by
        rw [← hφ, ← IsLocalization.mk'_spec (Localization.AtPrime M) a s, map_mul]
        change φ (IsLocalization.mk' (Localization.AtPrime M) a s) = 0 at hz
        rw [hz, zero_mul]
      obtain ⟨t, ht⟩ :=
        (IsLocalization.map_eq_zero_iff N.primeCompl (Localization.AtPrime N) (g a)).mp ha0
      obtain ⟨u, hu⟩ := hg (t : B)
      have huM : u ∈ M.primeCompl := by
        intro huM
        apply t.property
        have hgu : g u ∈ N := hMN.le huM
        simpa only [hu] using hgu
      apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
        M.primeCompl (Localization.AtPrime M) I a).mpr
      refine ⟨u, huM, ?_⟩
      rw [← hI]
      change g (u * a) = 0
      rw [map_mul, hu]
      exact ht
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change φ (f a) = 0
      rw [hφ]
      have hga : g a = 0 := by
        change a ∈ RingHom.ker g
        rw [hI]
        exact ha
      rw [hga, map_zero]
  let e := (Ideal.quotientEquivAlgOfEq K hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨e, ?_⟩
  intro a
  change (Ideal.quotientKerAlgEquivOfSurjective hsurj)
      (Ideal.quotientEquivAlgOfEq K hker.symm (Ideal.Quotient.mk _ (f a))) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]
  exact hφ a

end
end TranslatedDepthSeven
