import TranslatedDepthSeven.ProjectiveBertiniIncidenceLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Principal-open base change for the literal incidence quotient

Only localization and quotient universal properties are used.  In particular,
integrality of the incidence is not assumed in these identifications.
-/

namespace TranslatedDepthSeven

noncomputable section

theorem bertini_quotient_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)
    [Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S))]
    (hcomm : ∀ r : R, algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))
      (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (algebraMap R S r)) :
    IsLocalization (M.map (Ideal.Quotient.mk I)) (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  let q := Ideal.Quotient.mk I
  let qS := Ideal.Quotient.mk J
  let f := algebraMap (R ⧸ I) (S ⧸ J)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, r, hr, rfl⟩
    rw [hcomm]
    exact (IsLocalization.map_units S ⟨r, hr⟩).map qS
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj M w
    refine ⟨⟨q r, ⟨q t, Submonoid.mem_map_of_mem q t.property⟩⟩, ?_⟩
    change qS w * f (q t) = f (q r)
    rw [hcomm, hcomm, ← map_mul]
    exact congrArg qS ht
  · intro x y hxy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hcomm, hcomm] at hxy
    have hrs : algebraMap R S (r - s) ∈ J := by
      rw [map_sub]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hxy
    obtain ⟨t, ht, htrs⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I (r - s)).mp hrs
    refine ⟨⟨q t, Submonoid.mem_map_of_mem q ht⟩, ?_⟩
    change q t * q r = q t * q s
    rw [← map_mul, ← map_mul]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    simpa only [mul_sub] using htrs

/-- Localizing the quotient at the image of `s` is the quotient of any
localization away from `s` by the extended ideal, with recorded numerators. -/
theorem bertini_exists_quotient_away_equiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (s : R) [IsLocalization.Away s S] (I : Ideal R) :
    ∃ e : Localization.Away (Ideal.Quotient.mk I s) ≃+*
        (S ⧸ I.map (algebraMap R S)),
      ∀ r : R, e (algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I r)) =
        Ideal.Quotient.mk _ (algebraMap R S r) := by
  letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hcomm (r : R) : algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))
      (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (algebraMap R S r) := rfl
  haveI : IsLocalization.Away (Ideal.Quotient.mk I s)
      (S ⧸ I.map (algebraMap R S)) := by
    simpa only [Submonoid.map_powers] using
      bertini_quotient_isLocalization (Submonoid.powers s) I hcomm
  let e := IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I s))
    (Localization.Away (Ideal.Quotient.mk I s)) (S ⧸ I.map (algebraMap R S))
  exact ⟨e.toRingEquiv, fun r ↦ (e.commutes (Ideal.Quotient.mk I r)).trans (hcomm r)⟩

end
end TranslatedDepthSeven
