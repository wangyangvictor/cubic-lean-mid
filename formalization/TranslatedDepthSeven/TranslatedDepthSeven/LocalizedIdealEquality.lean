import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Finiteness.Defs

/-!
# A denominator certificate for equality after localization

This file records the elementary algebraic step used when equations are
known to define the chosen component only after one explicit denominator is
inverted.  It deliberately states the certificate as a formula: if `I ⊆ J`
and multiplication by `s` sends every element of `J` into `I`, then `I` and
`J` have the same extension to `R[1/s]`.

The theorem does not assert that such an `s` exists, nor does it bound `s`.
Those are precisely the effective component-identification obligations.
-/

namespace TranslatedDepthSeven

variable {R : Type*} [CommRing R]

/-- A single explicit denominator proves equality of two ideals after
localizing away from that denominator. -/
theorem map_away_eq_of_mul_mem
    (I J : Ideal R) (s : R) (hIJ : I ≤ J)
    (hclear : ∀ x ∈ J, s * x ∈ I) :
    Ideal.map (algebraMap R (Localization.Away s)) I =
      Ideal.map (algebraMap R (Localization.Away s)) J := by
  apply le_antisymm
  · exact Ideal.map_mono hIJ
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [← Ideal.unit_mul_mem_iff_mem
      (Ideal.map (algebraMap R (Localization.Away s)) I)
      (IsLocalization.Away.algebraMap_isUnit s)]
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (hclear x hx)

/-- The same localization criterion with the clearing condition written as
an ideal containment.  This is often the convenient output of an explicit
elimination calculation. -/
theorem map_away_eq_of_span_mul_le
    (I J : Ideal R) (s : R) (hIJ : I ≤ J)
    (hclear : Ideal.span {s} * J ≤ I) :
    Ideal.map (algebraMap R (Localization.Away s)) I =
      Ideal.map (algebraMap R (Localization.Away s)) J := by
  apply map_away_eq_of_mul_mem I J s hIJ
  intro x hx
  apply hclear
  exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩

/-- The denominator-bearing form of principal-open shrinking.  Besides the
equality after localization, the conclusion retains the literal identity
needed for specialization: multiplication by the chosen element sends the
whole larger ideal into the smaller one.  Thus no witness used to identify
the component is lost before denominators are cleared. -/
theorem exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq
    (I J P : Ideal R) [P.IsPrime] (hIJ : I ≤ J) (hJfg : J.FG)
    (hatPrime :
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    ∃ s : R, s ∉ P ∧
      (∀ x ∈ J, s * x ∈ I) ∧
      Ideal.map (algebraMap R (Localization.Away s)) I =
        Ideal.map (algebraMap R (Localization.Away s)) J := by
  classical
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hdenom : ∀ i : Fin n, ∃ m ∈ P.primeCompl, m * f i ∈ I := by
    intro i
    have hfiJ : f i ∈ J := by
      rw [← hf]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hmapJ : algebraMap R (Localization.AtPrime P) (f i) ∈
        Ideal.map (algebraMap R (Localization.AtPrime P)) J :=
      Ideal.mem_map_of_mem _ hfiJ
    have hmapI : algebraMap R (Localization.AtPrime P) (f i) ∈
        Ideal.map (algebraMap R (Localization.AtPrime P)) I := by
      rw [hatPrime]
      exact hmapJ
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff
      P.primeCompl (Localization.AtPrime P) I (f i)).mp hmapI
  choose d hdP hdI using hdenom
  let s : R := ∏ i : Fin n, d i
  have hsP : s ∉ P := by
    intro hs
    have hex : ∃ i ∈ (Finset.univ : Finset (Fin n)), d i ∈ P :=
      (Ideal.IsPrime.prod_mem_iff (p := P)
        (s := Finset.univ) (x := d)).mp hs
    obtain ⟨i, _hi, hdi⟩ := hex
    exact (hdP i) hdi
  have hclear : ∀ x ∈ J, s * x ∈ I := by
    intro x hx
    rw [← hf] at hx
    refine Submodule.span_induction
      (p := fun x (_ : x ∈ Submodule.span R (Set.range f)) ↦ s * x ∈ I)
      ?gen ?zero ?add ?smul hx
    · rintro x ⟨i, rfl⟩
      obtain ⟨c, hc⟩ : d i ∣ s :=
        Finset.dvd_prod_of_mem d (Finset.mem_univ i)
      rw [hc, mul_assoc]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        I.mul_mem_left c (hdI i)
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add] using I.add_mem hx hy
    · intro a x _ hx
      simpa [mul_assoc, mul_left_comm] using I.mul_mem_left a hx
  exact ⟨s, hsP, hclear, map_away_eq_of_mul_mem I J s hIJ hclear⟩

/-- Qualitative principal-open shrinking.  If two nested ideals agree in the
local ring at a prime and the larger ideal is finitely generated, then they
already agree after inverting one element outside that prime.

This theorem is deliberately non-effective: its chosen denominator carries
no degree or height bound.  It isolates exactly what the effective vertical
argument must strengthen. -/
theorem exists_map_away_eq_of_map_atPrime_eq
    (I J P : Ideal R) [P.IsPrime] (hIJ : I ≤ J) (hJfg : J.FG)
    (hatPrime :
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    ∃ s : R, s ∉ P ∧
      Ideal.map (algebraMap R (Localization.Away s)) I =
        Ideal.map (algebraMap R (Localization.Away s)) J := by
  obtain ⟨s, hsP, _hclear, hmap⟩ :=
    exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq
      I J P hIJ hJfg hatPrime
  exact ⟨s, hsP, hmap⟩

end TranslatedDepthSeven
