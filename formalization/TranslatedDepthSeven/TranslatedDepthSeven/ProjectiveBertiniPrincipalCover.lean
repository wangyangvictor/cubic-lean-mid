import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Gluing an integral generic incidence from principal charts

For the hyperplane system through a marked point, the charts are a smooth
neighborhood of that point and the complements of its coordinate equations.
The latter allow a generic coefficient to be eliminated. This file supplies
only the ring-theoretic gluing step; it asserts no Bertini existence result.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A distinguished principal chart detects zero if its defining element
remains nonzero on every other integral chart in a principal cover. -/
theorem principalCover_injective_of_integral_overlaps
    {R : Type*} [CommRing R] (a : R) (s : Set R)
    (hcover : Ideal.span (insert a s) = ⊤)
    (hcharts : ∀ b ∈ s, IsDomain (Localization.Away b) ∧
      algebraMap R (Localization.Away b) a ≠ 0) :
    Function.Injective (algebraMap R (Localization.Away a)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) x).mp hx
  apply Localization.algebraMap_injective_of_span_eq_top (insert a s) hcover
  funext b
  rcases b with ⟨b, hb⟩
  change algebraMap R (Localization.Away b) x =
    algebraMap R (Localization.Away b) 0
  rw [map_zero]
  rcases hb with rfl | hb
  · exact hx
  · have hc := hcharts b hb
    letI : IsDomain (Localization.Away b) := hc.1
    have he := congrArg (algebraMap R (Localization.Away b)) hn
    rw [map_mul, map_pow, map_zero] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero n hc.2)

/-- Domain on one distinguished chart and all its nonempty overlapping
charts implies domain globally. The cover is literal ideal generation. -/
theorem principalCover_isDomain
    {R : Type*} [CommRing R] (a : R) (s : Set R)
    (hcover : Ideal.span (insert a s) = ⊤)
    (ha : IsDomain (Localization.Away a))
    (hcharts : ∀ b ∈ s, IsDomain (Localization.Away b) ∧
      algebraMap R (Localization.Away b) a ≠ 0) : IsDomain R := by
  letI : IsDomain (Localization.Away a) := ha
  exact (principalCover_injective_of_integral_overlaps a s hcover hcharts).isDomain
    (algebraMap R (Localization.Away a))

end

end TranslatedDepthSeven
