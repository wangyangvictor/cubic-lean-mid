import TranslatedDepthSeven.ProjectiveBertiniIncidenceGlobal
import TranslatedDepthSeven.ProjectiveBertiniIncidenceProjectiveSaturation
import TranslatedDepthSeven.ProjectiveBertiniGenericIncidence

/-!
# Elementary coordinate-complement charts after generic localization

An invertible coefficient eliminates its generic variable. Every nonzero
element of the original domain remains nonzero on this chart, by evaluation
at zero in the remaining universal parameters. Its regularity persists
after arbitrary further localization, even when that localization is zero.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000

def bertiniIncidenceCoefficientMap
    {R σ : Type*} [CommRing R] [Fintype σ] (d : σ → R) :
    R →+* BertiniIncidenceRing d :=
  (Ideal.Quotient.mk _).comp C

theorem bertini_incidence_elementaryChart_regular
    {R σ : Type*} [CommRing R] [IsDomain R] [Fintype σ]
    (d : σ → R) (i : σ) (hi : d i ≠ 0) (r : R) (hr : r ≠ 0) :
    IsRegular (algebraMap (BertiniIncidenceRing d)
      (Localization.Away (bertiniIncidenceCoefficientMap d (d i)))
      (bertiniIncidenceCoefficientMap d r)) := by
  let S := Localization.Away (d i)
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hi)
  have hu : IsUnit (algebraMap R S (d i)) := IsLocalization.Away.algebraMap_isUnit (d i)
  letI := bertini_linear_sum_span_isPrime_of_isUnit
    (fun k ↦ algebraMap R S (d k)) i hu
  obtain ⟨e, he⟩ := bertini_exists_linear_sum_away_equiv d (d i)
  letI : IsDomain (Localization.Away (bertiniIncidenceCoefficientMap d (d i))) :=
    e.injective.isDomain e.toRingHom
  apply isRegular_of_ne_zero'
  intro hz
  have hz' := congrArg e hz
  have hz'' := (he r).symm.trans (hz'.trans (map_zero e))
  have hr' : algebraMap R S r ≠ 0 := by
    intro h
    exact hr ((IsLocalization.injective S
      (powers_le_nonZeroDivisors_of_noZeroDivisors hi)) (h.trans (map_zero _).symm))
  exact bertini_linear_sum_quotient_C_ne_zero
    (fun k ↦ algebraMap R S (d k)) (algebraMap R S r) hr' hz''

/-- This includes localization at all nonzero parameter polynomials; no
nonemptiness of each resulting coordinate chart is required. -/
theorem bertini_incidence_elementaryChart_regular_after_localization
    {R σ S : Type*} [CommRing R] [IsDomain R] [Fintype σ]
    (d : σ → R) [CommRing S] [Algebra (BertiniIncidenceRing d) S]
    (M : Submonoid (BertiniIncidenceRing d)) [IsLocalization M S]
    (i : σ) (hi : d i ≠ 0) (r : R) (hr : r ≠ 0) :
    IsRegular (algebraMap S
      (Localization.Away (algebraMap (BertiniIncidenceRing d) S
        (bertiniIncidenceCoefficientMap d (d i))))
      (algebraMap (BertiniIncidenceRing d) S (bertiniIncidenceCoefficientMap d r))) := by
  apply bertini_isRegular_away_after_localization M
  exact bertini_incidence_elementaryChart_regular d i hi r hr

end
end TranslatedDepthSeven
