import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! A valuation of an ambient field centered at any specified prime of an
embedded domain. This will supply an actual valuative degeneration for orbit
closures; no curve, valuation, or center is assumed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalValuative

/-- Embed the actual coordinate domain in a valuation subring of the chosen
ambient field, with exactly the prescribed center. -/
theorem exists_valuation_center {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f) (m : Ideal R) [m.IsPrime] :
    ∃ V : ValuationSubring K, ∃ g : R →+* V,
      (∀ x, (g x : K) = f x) ∧ (IsLocalRing.maximalIdeal V).comap g = m := by
  have hu (y : m.primeCompl) : IsUnit (f y) := by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hy0 : (y : R) = 0 := hf (by simpa using hy)
    apply y.property
    rw [hy0]
    exact m.zero_mem
  let e : Localization.AtPrime m →+* K := IsLocalization.lift hu
  obtain ⟨V,hV,hlocal⟩ := IsLocalRing.exists_factor_valuationRing e
  let h : Localization.AtPrime m →+* V := e.codRestrict V.toSubring hV
  letI : IsLocalHom h := hlocal
  let g : R →+* V := h.comp (algebraMap R (Localization.AtPrime m))
  refine ⟨V,g,?_,?_⟩
  · intro x
    exact IsLocalization.lift_eq hu x
  · have he : (IsLocalRing.maximalIdeal V).comap h =
        IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
      ext x
      change h x ∈ IsLocalRing.maximalIdeal V ↔
        x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m)
      simp only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
      exact not_congr (isUnit_map_iff h x)
    change (IsLocalRing.maximalIdeal V).comap
      (h.comp (algebraMap R (Localization.AtPrime m))) = m
    rw [← Ideal.comap_comap,he,Localization.AtPrime.comap_maximalIdeal]

end HessianTheorem11.UnconditionalValuative
