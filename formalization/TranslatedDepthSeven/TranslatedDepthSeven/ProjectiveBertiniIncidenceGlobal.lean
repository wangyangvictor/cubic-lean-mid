import TranslatedDepthSeven.ProjectiveBertiniIncidenceBaseChange
import TranslatedDepthSeven.ProjectiveBertiniIncidenceLinearSum
import TranslatedDepthSeven.ProjectiveBertiniPrincipalCover

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000

theorem bertini_exists_linear_sum_away_equiv
    {R σ : Type*} [CommRing R] [Fintype σ] (d : σ → R) (s : R) :
    ∃ e : Localization.Away (Ideal.Quotient.mk
        (Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R))) (C s)) ≃+*
        (MvPolynomial σ (Localization.Away s) ⧸ Ideal.span
          ({bertiniLinear (fun i ↦ algebraMap R (Localization.Away s) (d i))} : Set _)),
      ∀ r : R, e (algebraMap
        (MvPolynomial σ R ⧸ Ideal.span ({bertiniLinear d} : Set _)) _
        (Ideal.Quotient.mk (Ideal.span ({bertiniLinear d} : Set _)) (C r))) =
        Ideal.Quotient.mk _ (C (algebraMap R (Localization.Away s) r)) := by
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := Localization.Away s)
  haveI : IsLocalization.Away (C s : MvPolynomial σ R)
      (MvPolynomial σ (Localization.Away s)) := by
    simpa only [Submonoid.map_powers] using
      (inferInstance : IsLocalization ((Submonoid.powers s).map (C (σ := σ)))
        (MvPolynomial σ (Localization.Away s)))
  let I := Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R))
  have hmap : I.map (algebraMap (MvPolynomial σ R)
      (MvPolynomial σ (Localization.Away s))) =
      Ideal.span ({bertiniLinear (fun i ↦ algebraMap R (Localization.Away s) (d i))} : Set _) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    simp [bertiniLinear, MvPolynomial.algebraMap_def]
  obtain ⟨e, he⟩ := bertini_exists_quotient_away_equiv
    (S := MvPolynomial σ (Localization.Away s)) (C s) I
  refine ⟨e.trans (Ideal.quotEquivOfEq hmap), ?_⟩
  intro r
  rw [RingEquiv.trans_apply, he, Ideal.quotEquivOfEq_mk]
  simp [MvPolynomial.algebraMap_def]

/-- A single regular-pair chart, together with the coordinate-complement
charts, makes the entire literal universal linear incidence integral. -/
theorem bertini_linear_sum_isDomain_of_principal_regular_pair
    {R σ : Type*} [CommRing R] [IsDomain R] [Fintype σ]
    (d : σ → R) (s : R) (hs : s ≠ 0)
    (hcover : Ideal.span (insert s (Set.range d)) = ⊤)
    (i j : σ) (hij : j ≠ i)
    (hi : algebraMap R (Localization.Away s) (d i) ≠ 0)
    (hj : IsRegular (Ideal.Quotient.mk
      (Ideal.span ({algebraMap R (Localization.Away s) (d i)} : Set _))
      (algebraMap R (Localization.Away s) (d j)))) :
    IsDomain (MvPolynomial σ R ⧸ Ideal.span ({bertiniLinear d} : Set _)) := by
  classical
  let I := Ideal.span ({bertiniLinear d} : Set (MvPolynomial σ R))
  let Q := MvPolynomial σ R ⧸ I
  let q : R →+* Q := (Ideal.Quotient.mk I).comp C
  let T : Set Q := q '' (Set.range d \ {0})
  have hcover' : Ideal.span (insert (q s) T) = ⊤ := by
    have hcoverR : Ideal.span (insert s (Set.range d \ {0})) = ⊤ := by
      rw [Ideal.span_insert, Ideal.span_sdiff_singleton_zero,
        ← Ideal.span_insert]
      exact hcover
    have heq := congrArg (Ideal.map q) hcoverR
    simpa only [Ideal.map_span, Set.image_insert_eq, Ideal.map_top] using heq
  have hdist : IsDomain (Localization.Away (q s)) := by
    letI : IsDomain (Localization.Away s) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
    letI := bertini_linear_sum_span_isPrime_of_regular_pair
      (fun k ↦ algebraMap R (Localization.Away s) (d k)) i j hij hi hj
    obtain ⟨e, _⟩ := bertini_exists_linear_sum_away_equiv d s
    exact e.injective.isDomain e.toRingHom
  apply principalCover_isDomain (q s) T hcover' hdist
  rintro b ⟨c, ⟨⟨k, rfl⟩, hc⟩, rfl⟩
  have hc0 : d k ≠ 0 := fun h ↦ hc (Set.mem_singleton_iff.mpr h)
  let S := Localization.Away (d k)
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hc0)
  have hu : IsUnit (algebraMap R S (d k)) := IsLocalization.Away.algebraMap_isUnit (d k)
  letI := bertini_linear_sum_span_isPrime_of_isUnit
    (fun l ↦ algebraMap R S (d l)) k hu
  obtain ⟨e, he⟩ := bertini_exists_linear_sum_away_equiv d (d k)
  refine ⟨e.injective.isDomain e.toRingHom, ?_⟩
  intro hz
  have hz' := congrArg e hz
  have hz'' := (he s).symm.trans (hz'.trans (map_zero e))
  have hsn : algebraMap R S s ≠ 0 := by
    intro h
    apply hs
    exact (IsLocalization.injective S
      (powers_le_nonZeroDivisors_of_noZeroDivisors hc0)) (h.trans (map_zero _).symm)
  exact bertini_linear_sum_quotient_C_ne_zero
    (fun l ↦ algebraMap R S (d l)) (algebraMap R S s) hsn hz''

end
end TranslatedDepthSeven
