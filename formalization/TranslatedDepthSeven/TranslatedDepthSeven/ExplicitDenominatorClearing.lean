import TranslatedDepthSeven.LocalizedIdealEquality

/-!
# Explicit simultaneous denominator clearing

This file extracts the effective part of the usual localization argument.
Suppose that `f i` generate an ideal and that the literal witnesses

`d i * f i ∈ I`

are known.  Their product is one simultaneous denominator: multiplication
by `∏ i, d i` sends the whole generated ideal into `I`.  No denominator is
chosen in these statements; the output is a formula in the supplied
denominators.  This makes the lemmas suitable for later degree or coefficient
bounds.
-/

namespace TranslatedDepthSeven

variable {R : Type*} [CommRing R]

/-- Literal denominator witnesses for a finite generating family clear every
element of its span after multiplication by their product. -/
theorem prod_denominators_mul_mem_of_mem_span_range
    {n : ℕ} (I : Ideal R) (f d : Fin n → R)
    (hclear : ∀ i, d i * f i ∈ I) {x : R}
    (hx : x ∈ Ideal.span (Set.range f)) :
    (∏ i, d i) * x ∈ I := by
  classical
  refine Submodule.span_induction
    (p := fun x (_ : x ∈ Submodule.span R (Set.range f)) ↦
      (∏ i, d i) * x ∈ I)
    ?gen ?zero ?add ?smul hx
  · rintro x ⟨i, rfl⟩
    obtain ⟨c, hc⟩ : d i ∣ ∏ j, d j :=
      Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    rw [hc, mul_assoc]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      I.mul_mem_left c (hclear i)
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using I.add_mem hx hy
  · intro a x _ hx
    simpa [mul_assoc, mul_left_comm] using I.mul_mem_left a hx

/-- The preceding elementwise certificate, written as an ideal
containment. -/
theorem span_prod_denominators_mul_span_range_le
    {n : ℕ} (I : Ideal R) (f d : Fin n → R)
    (hclear : ∀ i, d i * f i ∈ I) :
    Ideal.span {(∏ i, d i)} * Ideal.span (Set.range f) ≤ I := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro x hx
  exact prod_denominators_mul_mem_of_mem_span_range I f d hclear hx

/-- A named finitely generated ideal version of explicit denominator
clearing. -/
theorem span_prod_denominators_mul_le_of_eq_span_range
    {n : ℕ} (I J : Ideal R) (f d : Fin n → R)
    (hJ : J = Ideal.span (Set.range f))
    (hclear : ∀ i, d i * f i ∈ I) :
    Ideal.span {(∏ i, d i)} * J ≤ I := by
  rw [hJ]
  exact span_prod_denominators_mul_span_range_le I f d hclear

/-- If an explicit clearing denominator becomes a unit in an algebra, then
the two nested ideals have equal extensions to that algebra. -/
theorem map_eq_of_mul_mem_of_isUnit
    {A : Type*} [CommRing A] [Algebra R A]
    (I J : Ideal R) (h : R) (hIJ : I ≤ J)
    (hunit : IsUnit (algebraMap R A h))
    (hclear : ∀ x ∈ J, h * x ∈ I) :
    Ideal.map (algebraMap R A) I = Ideal.map (algebraMap R A) J := by
  apply le_antisymm
  · exact Ideal.map_mono hIJ
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [← Ideal.unit_mul_mem_iff_mem (Ideal.map (algebraMap R A) I) hunit]
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (hclear x hx)

/-- Explicit generator denominators which become units give equality of the
extended ideals.  The simultaneous denominator is exactly `∏ i, d i`. -/
theorem map_eq_of_generator_denominators
    {A : Type*} [CommRing A] [Algebra R A]
    {n : ℕ} (I J : Ideal R) (f d : Fin n → R)
    (hIJ : I ≤ J) (hJ : J = Ideal.span (Set.range f))
    (hclear : ∀ i, d i * f i ∈ I)
    (hunit : ∀ i, IsUnit (algebraMap R A (d i))) :
    Ideal.map (algebraMap R A) I = Ideal.map (algebraMap R A) J := by
  apply map_eq_of_mul_mem_of_isUnit I J (∏ i, d i) hIJ
  · rw [map_prod, IsUnit.prod_univ_iff]
    exact hunit
  · intro x hx
    apply span_prod_denominators_mul_le_of_eq_span_range I J f d hJ hclear
    exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩

/-- A product of explicit denominators outside a prime is again outside that
prime. -/
theorem prod_denominators_not_mem_prime
    {n : ℕ} (P : Ideal R) [P.IsPrime] (d : Fin n → R)
    (hd : ∀ i, d i ∉ P) :
    (∏ i, d i) ∉ P := by
  intro hprod
  obtain ⟨i, _hi, hdi⟩ :=
    (Ideal.IsPrime.prod_mem_iff (p := P)
      (s := Finset.univ) (x := d)).mp hprod
  exact (hd i) hdi

/-- Fully explicit principal-open shrinking from literal local denominator
witnesses.  The element defining the open set is their product. -/
theorem map_away_prod_denominators_eq
    {n : ℕ} (I J : Ideal R) (f d : Fin n → R)
    (hIJ : I ≤ J) (hJ : J = Ideal.span (Set.range f))
    (hclear : ∀ i, d i * f i ∈ I) :
    Ideal.map (algebraMap R (Localization.Away (∏ i, d i))) I =
      Ideal.map (algebraMap R (Localization.Away (∏ i, d i))) J := by
  apply map_away_eq_of_span_mul_le I J (∏ i, d i) hIJ
  exact span_prod_denominators_mul_le_of_eq_span_range I J f d hJ hclear

/-- A single packaged certificate for the situation at a prime.  All three
outputs use the literal product of the supplied denominators: it avoids the
prime, clears the larger ideal into the smaller ideal, and defines a
principal open on which the ideals agree. -/
theorem prod_denominator_certificate_at_prime
    {n : ℕ} (I J P : Ideal R) [P.IsPrime] (f d : Fin n → R)
    (hIJ : I ≤ J) (hJ : J = Ideal.span (Set.range f))
    (hdP : ∀ i, d i ∉ P) (hclear : ∀ i, d i * f i ∈ I) :
    (∏ i, d i) ∉ P ∧
      Ideal.span {(∏ i, d i)} * J ≤ I ∧
      Ideal.map (algebraMap R (Localization.Away (∏ i, d i))) I =
        Ideal.map (algebraMap R (Localization.Away (∏ i, d i))) J := by
  exact ⟨prod_denominators_not_mem_prime P d hdP,
    span_prod_denominators_mul_le_of_eq_span_range I J f d hJ hclear,
    map_away_prod_denominators_eq I J f d hIJ hJ hclear⟩

/-- The exact common power obtained by clearing generator-wise powers of one
element. -/
theorem power_sum_mul_mem_of_mem_span_range
    {n : ℕ} (I : Ideal R) (f : Fin n → R) (a : R) (e : Fin n → ℕ)
    (hclear : ∀ i, a ^ e i * f i ∈ I) {x : R}
    (hx : x ∈ Ideal.span (Set.range f)) :
    a ^ (∑ i, e i) * x ∈ I := by
  rw [← Finset.prod_pow_eq_pow_sum Finset.univ e a]
  exact prod_denominators_mul_mem_of_mem_span_range I f (fun i ↦ a ^ e i)
    hclear hx

/-- Ideal-containment form of simultaneous power denominator clearing. -/
theorem span_power_sum_mul_le_of_eq_span_range
    {n : ℕ} (I J : Ideal R) (f : Fin n → R) (a : R) (e : Fin n → ℕ)
    (hJ : J = Ideal.span (Set.range f))
    (hclear : ∀ i, a ^ e i * f i ∈ I) :
    Ideal.span {a ^ (∑ i, e i)} * J ≤ I := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro x hx
  rw [hJ] at hx
  exact power_sum_mul_mem_of_mem_span_range I f a e hclear hx

/-- Generator-wise power witnesses imply equality after localizing away from
the underlying element.  The proof retains the quantitative common exponent
`∑ i, e i`. -/
theorem map_away_eq_of_generator_power_witnesses
    {n : ℕ} (I J : Ideal R) (f : Fin n → R) (a : R) (e : Fin n → ℕ)
    (hIJ : I ≤ J) (hJ : J = Ideal.span (Set.range f))
    (hclear : ∀ i, a ^ e i * f i ∈ I) :
    Ideal.map (algebraMap R (Localization.Away a)) I =
      Ideal.map (algebraMap R (Localization.Away a)) J := by
  apply map_eq_of_mul_mem_of_isUnit I J (a ^ (∑ i, e i)) hIJ
  · rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit a).pow _
  · intro x hx
    apply span_power_sum_mul_le_of_eq_span_range I J f a e hJ hclear
    exact Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩

end TranslatedDepthSeven
