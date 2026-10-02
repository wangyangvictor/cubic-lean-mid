import Mathlib.RingTheory.Localization.Away.Basic

/-!
# One principal open for finitely many zero relations

Let `M ⊆ R` be a submonoid and let `R → A` be a morphism of
commutative rings.  If finitely many elements of `A` vanish after localizing
at the image of `M`, one element of `M` kills all of them already in `A`.
The product of one denominator for each relation is a simultaneous
denominator, and all the relations therefore hold after localizing at the
single corresponding principal open.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v

/-- The product of finitely many displayed denominators kills every member
of the corresponding finite family. -/
theorem prod_denominators_kills_finite_family
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n : ℕ} (x : Fin n → A) (d : Fin n → R)
    (hclear : ∀ i, algebraMap R A (d i) * x i = 0) :
    ∀ i, algebraMap R A (∏ j, d j) * x i = 0 := by
  classical
  intro i
  obtain ⟨c, hc⟩ : d i ∣ ∏ j, d j :=
    Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, map_mul]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    congrArg (fun z ↦ algebraMap R A c * z) (hclear i)

/-- If finitely many elements vanish in the canonical localization of `A`
at the image of `M`, a single member of `M` kills all of them in `A`.
The same member defines a principal localization in which they all vanish.
-/
theorem exists_submonoid_element_killing_finite_family_of_localization_eq_zero
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) {n : ℕ} (x : Fin n → A)
    (hzero : ∀ i,
      algebraMap A (Localization (M.map (algebraMap R A))) (x i) = 0) :
    ∃ m : M,
      (∀ i, algebraMap R A (m : R) * x i = 0) ∧
      ∀ i,
        algebraMap A (Localization.Away (algebraMap R A (m : R))) (x i) = 0 := by
  classical
  have hdenom :
      ∀ i : Fin n, ∃ d : R, d ∈ M ∧ algebraMap R A d * x i = 0 := by
    intro i
    obtain ⟨e, he⟩ :=
      (IsLocalization.map_eq_zero_iff
        (M.map (algebraMap R A))
        (Localization (M.map (algebraMap R A))) (x i)).mp (hzero i)
    obtain ⟨d, hdM, hde⟩ := Submonoid.mem_map.mp e.property
    refine ⟨d, hdM, ?_⟩
    rw [hde]
    exact he
  choose d hdM hclear using hdenom
  let m : R := ∏ i, d i
  have hmM : m ∈ M := by
    exact M.prod_mem fun i _hi ↦ hdM i
  have hclearAll : ∀ i, algebraMap R A m * x i = 0 := by
    simpa only [m] using prod_denominators_kills_finite_family x d hclear
  refine ⟨⟨m, hmM⟩, hclearAll, ?_⟩
  intro i
  apply (IsUnit.mul_left_eq_zero
    (IsLocalization.Away.algebraMap_isUnit (algebraMap R A m))).mp
  rw [← map_mul]
  have hmul : x i * algebraMap R A m = 0 := by
    simpa [mul_comm] using hclearAll i
  rw [hmul, map_zero]

/-- Equality version: finitely many equalities in the localization at `M`
hold after multiplying in `A` by one common member of `M`, and hence hold on
the corresponding single principal open. -/
theorem exists_submonoid_element_clearing_finite_family_equalities
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (M : Submonoid R) {n : ℕ} (x y : Fin n → A)
    (heq : ∀ i,
      algebraMap A (Localization (M.map (algebraMap R A))) (x i) =
        algebraMap A (Localization (M.map (algebraMap R A))) (y i)) :
    ∃ m : M,
      (∀ i,
        algebraMap R A (m : R) * x i =
          algebraMap R A (m : R) * y i) ∧
      ∀ i,
        algebraMap A (Localization.Away (algebraMap R A (m : R))) (x i) =
          algebraMap A (Localization.Away (algebraMap R A (m : R))) (y i) := by
  have hzero : ∀ i,
      algebraMap A (Localization (M.map (algebraMap R A))) (x i - y i) = 0 := by
    intro i
    rw [map_sub, heq i, sub_self]
  obtain ⟨m, hclear, haway⟩ :=
    exists_submonoid_element_killing_finite_family_of_localization_eq_zero
      M (fun i ↦ x i - y i) hzero
  refine ⟨m, ?_, ?_⟩
  · intro i
    rw [← sub_eq_zero, ← mul_sub]
    exact hclear i
  · intro i
    rw [← sub_eq_zero, ← map_sub]
    exact haway i

end

end TranslatedDepthSeven
