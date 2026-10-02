import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Surjections on the local rings at corresponding rational points

The map is constructed from the localization universal property.  Its
surjectivity is checked on fractions, so no image-of-multiplicative-sets
identification is hidden in the statement.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000

theorem exists_surjective_pointLocalizationAlgHom
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B]
    (g : A →ₐ[K] B) (hg : Function.Surjective g)
    (M : Ideal A) (N : Ideal B) [M.IsPrime] [N.IsPrime]
    (hMN : M = N.comap g) :
    ∃ φ : Localization.AtPrime M →ₐ[K] Localization.AtPrime N,
      Function.Surjective φ ∧
      φ.comp (IsScalarTower.toAlgHom K A (Localization.AtPrime M)) =
        (IsScalarTower.toAlgHom K B (Localization.AtPrime N)).comp g := by
  let targetMap : A →ₐ[K] Localization.AtPrime N :=
    (IsScalarTower.toAlgHom K B (Localization.AtPrime N)).comp g
  have hunits : ∀ s : M.primeCompl, IsUnit (targetMap s) := by
    intro s
    have hgs : g s ∈ N.primeCompl := by
      intro hgs
      exact s.property (hMN.ge hgs)
    exact IsLocalization.map_units (Localization.AtPrime N) ⟨g s, hgs⟩
  let φ : Localization.AtPrime M →ₐ[K] Localization.AtPrime N :=
    IsLocalization.liftAlgHom hunits
  have hφ (a : A) : φ (algebraMap A (Localization.AtPrime M) a) = targetMap a := by
    change (IsLocalization.liftAlgHom hunits) (algebraMap A (Localization.AtPrime M) a) = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro z
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq N.primeCompl z
    obtain ⟨a, ha⟩ := hg b
    obtain ⟨s, hs⟩ := hg (t : B)
    have hsM : s ∈ M.primeCompl := by
      intro hsM
      apply t.property
      have hgs : g s ∈ N := hMN.le hsM
      simpa only [hs] using hgs
    refine ⟨IsLocalization.mk' (Localization.AtPrime M) a ⟨s, hsM⟩, ?_⟩
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    have hden : algebraMap B (Localization.AtPrime N) (t : B) =
        φ (algebraMap A (Localization.AtPrime M) s) := by
      rw [hφ]
      change algebraMap B (Localization.AtPrime N) (t : B) =
        algebraMap B (Localization.AtPrime N) (g s)
      rw [hs]
    rw [hden, ← map_mul, IsLocalization.mk'_spec, hφ]
    change algebraMap B (Localization.AtPrime N) (g a) = _
    rw [ha]
  · exact AlgHom.ext hφ

end

end TranslatedDepthSeven
