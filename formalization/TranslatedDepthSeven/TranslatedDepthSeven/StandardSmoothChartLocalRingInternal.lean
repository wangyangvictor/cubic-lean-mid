import TranslatedDepthSeven.SmoothRationalPointLocalDomainInternal
import TranslatedDepthSeven.SmoothLocalPointDimensionUpperInternal
import TranslatedDepthSeven.PrincipalOpenSmoothFibreTransport
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The actual local ring beneath a standard-smooth chart

This transports the domain property, dimension upper bound and formal
smoothness from the local ring on a displayed localization chart back to
the original algebra.  The equivalence is the canonical equivalence between
two localizations at the same prime.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem localRing_of_standardSmooth_localizationChart
    {K A T : Type*} [Field K] [CommRing A] [CommRing T]
    [Algebra K A] [Algebra A T] [Algebra K T] [IsScalarTower K A T]
    [IsNoetherianRing T]
    (S : Submonoid A) [IsLocalization S T]
    (x : T →ₐ[K] K) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K T]
    (M : Ideal A) [M.IsPrime]
    (hM : M = RingHom.ker
      (x.comp (IsScalarTower.toAlgHom K A T)).toRingHom) :
    IsDomain (Localization.AtPrime M) ∧
      ringKrullDim (Localization.AtPrime M) ≤ (r : WithBot ℕ∞) ∧
      Algebra.FormallySmooth K (Localization.AtPrime M) := by
  let N := RingHom.ker x.toRingHom
  letI : N.IsPrime := RingHom.ker_isPrime x.toRingHom
  let L := Localization.AtPrime N
  letI : IsDomain L := isDomain_pointLocalization_of_standardSmooth x r N rfl
  have hcomap : N.comap (algebraMap A T) = M := hM.symm
  letI : IsLocalization M.primeCompl L := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S L N
    simpa only [hcomap] using h
  let E : L ≃ₐ[K] Localization.AtPrime M :=
    (IsLocalization.algEquiv M.primeCompl L (Localization.AtPrime M)).restrictScalars K
  have hunits : ∀ s : N.primeCompl, IsUnit (x s) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    exact s.property
  let pointL : L →ₐ[K] K := IsLocalization.liftAlgHom hunits
  have hdim : ringKrullDim L ≤ (r : WithBot ℕ∞) :=
    ringKrullDim_localization_le_of_standardSmooth_rationalPoint N.primeCompl pointL r
  letI : Algebra.FormallySmooth K L :=
    rationalPoint_mem_smoothLocus_of_isStandardSmoothOfRelativeDimension r x
  refine ⟨E.symm.injective.isDomain E.symm.toRingHom, ?_, ?_⟩
  · rw [← E.toRingEquiv.ringKrullDim]
    exact hdim
  · exact Algebra.FormallySmooth.of_equiv E

end

end TranslatedDepthSeven
