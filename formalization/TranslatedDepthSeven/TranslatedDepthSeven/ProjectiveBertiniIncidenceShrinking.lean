import TranslatedDepthSeven.LocalizedIdealEquality
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic

/-!
# Spreading a regular coordinate pair from a marked local ring

Regularity modulo an ideal can be checked by its colon ideal. Noetherian
finite generation clears the local equality of the two ideals on one
principal neighborhood. This supplies a genuine regular pair for the
linear-incidence algebra, without assuming a geometric conclusion.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {R : Type*} [CommRing R]

/-- One explicit colon-clearing multiplier makes the selected element
regular modulo the extended ideal on a principal open. -/
theorem bertini_regular_mod_away_of_colon_clear
    (I : Ideal R) (b s : R)
    (hclear : ∀ x ∈ I.colon (Ideal.span {b}), s * x ∈ I) :
    IsRegular (Ideal.Quotient.mk
      (I.map (algebraMap R (Localization.Away s)))
      (algebraMap R (Localization.Away s) b)) := by
  let S := Localization.Away s
  let f : R →+* S := algebraMap R S
  let J := I.map f
  have hcancel : ∀ y : S, f b * y ∈ J → y ∈ J := by
    intro y hy
    obtain ⟨⟨z, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers s) y
    change y * f (t : R) = f z at ht
    have hbz : f (b * z) ∈ J := by
      have h := J.mul_mem_right (f t) hy
      simpa only [map_mul, mul_assoc, ht] using h
    obtain ⟨m, hm, hmz⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Submonoid.powers s) S I (b * z)).mp hbz
    have hmz' : m * z ∈ I.colon (Ideal.span {b}) := by
      apply Ideal.mem_colon_singleton.mpr
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmz
    have hsz := Ideal.mem_map_of_mem f (hclear (m * z) hmz')
    have hu : IsUnit (f (s * m)) := by
      rw [map_mul]
      exact (IsLocalization.Away.algebraMap_isUnit s).mul
        (IsLocalization.map_units S ⟨m, hm⟩)
    have hz : f z ∈ J := by
      apply (Ideal.unit_mul_mem_iff_mem J hu).mp
      simpa only [map_mul, mul_assoc] using hsz
    apply (Ideal.unit_mul_mem_iff_mem J (IsLocalization.map_units S t)).mp
    rw [mul_comm, ht]
    exact hz
  have hleft : IsLeftRegular (Ideal.Quotient.mk J (f b)) := by
    apply isLeftRegular_of_non_zero_divisor
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hcancel
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hx
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

/-- Regularity at a marked prime spreads to some principal neighborhood
of that prime. This is stated for the literal localized quotient. -/
theorem bertini_exists_away_regular_of_local_regular
    [IsNoetherianRing R] (I P : Ideal R) [P.IsPrime] (b : R)
    (hb : IsRegular (Ideal.Quotient.mk
      (I.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) b))) :
    ∃ s : R, s ∉ P ∧
      IsRegular (Ideal.Quotient.mk
        (I.map (algebraMap R (Localization.Away s)))
        (algebraMap R (Localization.Away s) b)) := by
  let f := algebraMap R (Localization.AtPrime P)
  let J := I.colon (Ideal.span {b})
  have hIJ : I ≤ J := Ideal.le_colon
  have hlocal : I.map f = J.map f := by
    apply le_antisymm (Ideal.map_mono hIJ)
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change f x ∈ I.map f
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hb.left.mul_left_eq_zero_iff.mp
    have hbx : b * x ∈ I := by
      simpa only [mul_comm] using Ideal.mem_colon_singleton.mp hx
    have hm := Ideal.mem_map_of_mem f hbx
    simpa only [map_mul] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨s, hs, hclear, _⟩ :=
    exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq
      I J P hIJ (IsNoetherian.noetherian J) hlocal
  exact ⟨s, hs, bertini_regular_mod_away_of_colon_clear I b s hclear⟩

/-- The regular-pair form used for the selected affine coordinate
differences. The first coefficient stays nonzero on the chosen open. -/
theorem bertini_exists_away_regular_pair_of_local_regular
    [IsDomain R] [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (a b : R) (ha : a ≠ 0)
    (hb : IsRegular (Ideal.Quotient.mk
      ((Ideal.span ({a} : Set R)).map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) b))) :
    ∃ s : R, s ∉ P ∧ algebraMap R (Localization.Away s) a ≠ 0 ∧
      IsRegular (Ideal.Quotient.mk
        (Ideal.span ({algebraMap R (Localization.Away s) a} : Set _))
        (algebraMap R (Localization.Away s) b)) := by
  obtain ⟨s, hs, hreg⟩ :=
    bertini_exists_away_regular_of_local_regular (Ideal.span {a}) P b hb
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ P.zero_mem)
  have hinj := IsLocalization.injective (Localization.Away s)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  refine ⟨s, hs, ?_, ?_⟩
  · exact fun hz ↦ ha (hinj (hz.trans (map_zero _).symm))
  · have hI : (Ideal.span ({a} : Set R)).map (algebraMap R (Localization.Away s)) =
        Ideal.span ({algebraMap R (Localization.Away s) a} : Set _) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hI] at hreg
    exact hreg

end
end TranslatedDepthSeven
