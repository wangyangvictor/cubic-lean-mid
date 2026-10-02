import TranslatedDepthSeven.ExplicitDenominatorClearing

/-!
# Vertical generic spreading by one base denominator

Let `R → A` be a map of commutative rings and let `M` be a submonoid of
`R`.  Suppose that nested finitely generated ideals of `A` become equal
after inverting the image of `M`.  Membership in an extended ideal then
gives, for each member of a finite generating family, a denominator in
`M`.  Their product is a single element of `M` which clears the whole
larger ideal into the smaller one.  Consequently the two ideals agree on
the corresponding principal open of the base.

The first theorem retains the literal product of supplied generator
denominators.  The second obtains those denominators from equality in an
arbitrary realization of the localization at `M.map (algebraMap R A)`.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Explicit base-denominator certificate.  Generator-wise denominators
from `M` are multiplied in `R`, and their image in `A` clears every element
of `J`.  Thus `I` and `J` have equal extensions after inverting that one
base element. -/
theorem base_prod_denominator_certificate
    (M : Submonoid R) {n : ℕ} (I J : Ideal A)
    (f : Fin n → A) (d : Fin n → R)
    (hIJ : I ≤ J) (hJ : J = Ideal.span (Set.range f))
    (hdM : ∀ i, d i ∈ M)
    (hclear : ∀ i, algebraMap R A (d i) * f i ∈ I) :
    (∏ i, d i) ∈ M ∧
      (∀ x ∈ J, algebraMap R A (∏ i, d i) * x ∈ I) ∧
      Ideal.map
          (algebraMap A
            (Localization.Away (algebraMap R A (∏ i, d i)))) I =
        Ideal.map
          (algebraMap A
            (Localization.Away (algebraMap R A (∏ i, d i)))) J := by
  classical
  have hprodM : (∏ i, d i) ∈ M := by
    exact M.prod_mem fun i _hi ↦ hdM i
  have hprodClear :
      ∀ x ∈ J, algebraMap R A (∏ i, d i) * x ∈ I := by
    intro x hx
    have hxspan : x ∈ Ideal.span (Set.range f) := by
      simpa only [← hJ] using hx
    simpa only [map_prod] using
      (prod_denominators_mul_mem_of_mem_span_range I f
        (fun i ↦ algebraMap R A (d i)) hclear hxspan)
  exact ⟨hprodM, hprodClear,
    map_away_eq_of_mul_mem I J (algebraMap R A (∏ i, d i))
      hIJ hprodClear⟩

/-- Dense-open spreading for finitely generated nested ideals.  If `I` and
`J` become equal after localizing `A` at the image of `M ⊆ R`, one element
`m ∈ M` clears every element of `J` into `I`; hence their extensions to
`A[1 / algebraMap R A m]` are equal.

In the proof, `m` is the literal product of the finitely many denominators
obtained from a finite generating family of `J`. -/
theorem exists_base_denominator_map_away_eq_of_map_localization_eq
    (M : Submonoid R) (I J : Ideal A) (hIJ : I ≤ J) (hJfg : J.FG)
    {S : Type*} [CommRing S] [Algebra A S]
    [IsLocalization (M.map (algebraMap R A)) S]
    (hlocalized :
      Ideal.map (algebraMap A S) I = Ideal.map (algebraMap A S) J) :
    ∃ m : R, m ∈ M ∧
      (∀ x ∈ J, algebraMap R A m * x ∈ I) ∧
      Ideal.map
          (algebraMap A (Localization.Away (algebraMap R A m))) I =
        Ideal.map
          (algebraMap A (Localization.Away (algebraMap R A m))) J := by
  classical
  obtain ⟨n, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJfg
  have hJ : J = Ideal.span (Set.range f) := hf.symm
  have hdenom :
      ∀ i : Fin n, ∃ d : R, d ∈ M ∧
        algebraMap R A d * f i ∈ I := by
    intro i
    have hfiJ : f i ∈ J := by
      rw [hJ]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hmapJ : algebraMap A S (f i) ∈
        Ideal.map (algebraMap A S) J :=
      Ideal.mem_map_of_mem _ hfiJ
    have hmapI : algebraMap A S (f i) ∈
        Ideal.map (algebraMap A S) I := by
      rw [hlocalized]
      exact hmapJ
    obtain ⟨e, heM, heI⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (M.map (algebraMap R A)) S I (f i)).mp hmapI
    obtain ⟨d, hdM, hde⟩ := (Submonoid.mem_map.mp heM)
    refine ⟨d, hdM, ?_⟩
    rw [hde]
    exact heI
  choose d hdM hclear using hdenom
  obtain ⟨hprodM, hprodClear, haway⟩ :=
    base_prod_denominator_certificate M I J f d hIJ hJ hdM hclear
  exact ⟨∏ i, d i, hprodM, hprodClear, haway⟩

end

end TranslatedDepthSeven
