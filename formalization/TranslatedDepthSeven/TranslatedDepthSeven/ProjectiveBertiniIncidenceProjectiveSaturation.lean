import TranslatedDepthSeven.ProjectiveBertiniIncidenceShrinking
import Mathlib.RingTheory.Ideal.Operations

/-!
# From one integral projective chart to coordinate saturation

This is the chart-gluing part of the projective Bertini argument. It
retains the actual ideal, including possible torsion at the cone vertex.
The hypotheses on the other charts are explicit; no Bertini or generic
integrality assertion is hidden here.
-/

namespace TranslatedDepthSeven

noncomputable section

theorem bertini_isRegular_map_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (r : R) (hr : IsRegular r) :
    IsRegular (algebraMap R S r) := by
  have hleft : IsLeftRegular (algebraMap R S r) := by
    apply isLeftRegular_of_non_zero_divisor
    intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
    have hnum : algebraMap R S (r * a) = 0 := by
      have h := congrArg (fun t : S ↦ t * algebraMap R S (s : R)) hz
      simpa only [mul_assoc, IsLocalization.mk'_spec, zero_mul, ← map_mul] using h
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff M S (r * a)).mp hnum
    apply (IsLocalization.mk'_eq_zero_iff a s).mpr
    refine ⟨t, hr.left.mul_left_eq_zero_iff.mp ?_⟩
    simpa only [mul_assoc, mul_left_comm, mul_comm] using ht
  exact ⟨hleft, hleft.right_of_commute (fun _ ↦ Commute.all _ _)⟩

/-- Regularity on a principal chart survives any further localization of
the base ring. In particular, one may invert the generic parameters after
checking the elementary universal incidence charts. -/
theorem bertini_isRegular_away_after_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (a b : R)
    (ha : IsRegular (algebraMap R (Localization.Away b) a)) :
    IsRegular (algebraMap S (Localization.Away (algebraMap R S b))
      (algebraMap R S a)) := by
  let Rb := Localization.Away b
  let T := Localization.Away (algebraMap R S b)
  let f : Rb →+* T := IsLocalization.Away.map Rb T (algebraMap R S) b
  have hf (r : R) : f (algebraMap R Rb r) =
      algebraMap S T (algebraMap R S r) := by
    simp only [f, IsLocalization.Away.map, IsLocalization.map_eq]
  letI : Algebra Rb T := f.toAlgebra
  haveI : IsScalarTower R Rb T := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (hf r).symm)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Rb M) T :=
    IsLocalization.commutes Rb S T (Submonoid.powers b) M
  have h := bertini_isRegular_map_localization (S := T) (Algebra.algebraMapSubmonoid Rb M)
    (algebraMap R Rb a) ha
  change IsRegular (f (algebraMap R Rb a)) at h
  rwa [hf] at h

theorem bertini_exists_coordinate_power_annihilating_of_regular_overlap
    {R : Type*} [CommRing R] (a b x u : R)
    (hspan : x ∈ Ideal.span ({a, b} : Set R))
    (hu : algebraMap R (Localization.Away a) u = 0)
    (hb : b = 0 ∨ IsRegular (algebraMap R (Localization.Away b) a)) :
    ∃ n : ℕ, x ^ n * u = 0 := by
  let A : Ideal R := (⊥ : Ideal R).colon (Ideal.span {u})
  have hmem (r : R) : r ∈ A ↔ r * u = 0 := by
    simp only [A, Ideal.mem_colon_singleton, Ideal.mem_bot, mul_comm]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) u).mp hu
  have haA : a ∈ A.radical := Ideal.mem_radical_iff.mpr ⟨m, (hmem _).mpr hm⟩
  have hbA : b ∈ A.radical := by
    rcases hb with rfl | ha
    · exact A.radical.zero_mem
    · have he := congrArg (algebraMap R (Localization.Away b)) hm
      rw [map_mul, map_pow, map_zero] at he
      have hu' := (ha.pow m).left.mul_left_eq_zero_iff.mp he
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) u).mp hu'
      exact Ideal.mem_radical_iff.mpr ⟨n, (hmem _).mpr hn⟩
  have hxA : x ∈ A.radical := by
    apply (Ideal.span_le.mpr ?_) hspan
    intro r hr
    rcases hr with rfl | hr
    · exact haA
    · simpa only [Set.mem_singleton_iff] using hr ▸ hbA
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxA
  exact ⟨n, (hmem _).mp hn⟩

theorem bertini_exists_coordinate_power_annihilating
    {R : Type*} [CommRing R] (a b x u : R)
    (hspan : x ∈ Ideal.span ({a, b} : Set R))
    (hu : algebraMap R (Localization.Away a) u = 0)
    (hb : b = 0 ∨ (IsDomain (Localization.Away b) ∧
      algebraMap R (Localization.Away b) a ≠ 0)) :
    ∃ n : ℕ, x ^ n * u = 0 := by
  let A : Ideal R := (⊥ : Ideal R).colon (Ideal.span {u})
  have hmem (r : R) : r ∈ A ↔ r * u = 0 := by
    simp only [A, Ideal.mem_colon_singleton, Ideal.mem_bot, mul_comm]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) u).mp hu
  have haA : a ∈ A.radical := Ideal.mem_radical_iff.mpr ⟨m, (hmem _).mpr hm⟩
  have hbA : b ∈ A.radical := by
    rcases hb with rfl | ⟨hdom, ha⟩
    · exact A.radical.zero_mem
    · letI := hdom
      have he := congrArg (algebraMap R (Localization.Away b)) hm
      rw [map_mul, map_pow, map_zero] at he
      have hu' := (mul_eq_zero.mp he).resolve_left (pow_ne_zero m ha)
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) u).mp hu'
      exact Ideal.mem_radical_iff.mpr ⟨n, (hmem _).mpr hn⟩
  have hxA : x ∈ A.radical := by
    apply (Ideal.span_le.mpr ?_) hspan
    intro r hr
    rcases hr with rfl | hr
    · exact haA
    · simpa only [Set.mem_singleton_iff] using hr ▸ hbA
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxA
  exact ⟨n, (hmem _).mp hn⟩

/-- The kernel of restriction to the distinguished chart is a prime ideal
and equals the original ideal on every specified coordinate chart.
The linear relations `hcoords` apply to `X_i = (X_i-z_i X₀)+z_i X₀`. -/
theorem bertini_exists_prime_coordinate_saturation
    {R ι : Type*} [CommRing R] (T : Ideal R) (a : R) (x : ι → R)
    (b : ι → R ⧸ T)
    (hcoords : ∀ i, Ideal.Quotient.mk T (x i) ∈
      Ideal.span ({Ideal.Quotient.mk T a, b i} : Set (R ⧸ T)))
    (ha : IsDomain (Localization.Away (Ideal.Quotient.mk T a)))
    (hb : ∀ i, b i = 0 ∨ (IsDomain (Localization.Away (b i)) ∧
      algebraMap (R ⧸ T) (Localization.Away (b i)) (Ideal.Quotient.mk T a) ≠ 0)) :
    ∃ J : Ideal R, J.IsPrime ∧ T ≤ J ∧ a ∉ J ∧
      ∀ F ∈ J, ∀ i, ∃ k : ℕ, x i ^ k * F ∈ T := by
  letI := ha
  let f : R →+* Localization.Away (Ideal.Quotient.mk T a) :=
    (algebraMap (R ⧸ T) _).comp (Ideal.Quotient.mk T)
  refine ⟨RingHom.ker f, RingHom.ker_isPrime f, ?_, ?_, ?_⟩
  · intro F hF
    change f F = 0
    change algebraMap (R ⧸ T) _ (Ideal.Quotient.mk T F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hF, map_zero]
  · intro h
    exact (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk T a)).ne_zero h
  · intro F hF i
    obtain ⟨k, hk⟩ := bertini_exists_coordinate_power_annihilating
      (Ideal.Quotient.mk T a) (b i) (Ideal.Quotient.mk T (x i))
      (Ideal.Quotient.mk T F) (hcoords i) hF (hb i)
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa only [map_mul, map_pow] using hk

/-- A saturation already constructed on one chart propagates to every
coordinate by the same elementary overlap calculation. -/
theorem bertini_coordinate_saturation_of_one_chart
    {R ι : Type*} [CommRing R] (T J : Ideal R) (a : R) (x : ι → R)
    (b : ι → R ⧸ T)
    (hcoords : ∀ i, Ideal.Quotient.mk T (x i) ∈
      Ideal.span ({Ideal.Quotient.mk T a, b i} : Set (R ⧸ T)))
    (hsat : ∀ F ∈ J, ∃ m : ℕ, a ^ m * F ∈ T)
    (hb : ∀ i, b i = 0 ∨ (IsDomain (Localization.Away (b i)) ∧
      algebraMap (R ⧸ T) (Localization.Away (b i)) (Ideal.Quotient.mk T a) ≠ 0)) :
    ∀ F ∈ J, ∀ i, ∃ k : ℕ, x i ^ k * F ∈ T := by
  intro F hF i
  obtain ⟨m, hm⟩ := hsat F hF
  have hzero : algebraMap (R ⧸ T) (Localization.Away (Ideal.Quotient.mk T a))
      (Ideal.Quotient.mk T F) = 0 := by
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk T a))
      (Localization.Away (Ideal.Quotient.mk T a)) _).mpr
    refine ⟨⟨Ideal.Quotient.mk T a ^ m, ⟨m, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_pow] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨k, hk⟩ := bertini_exists_coordinate_power_annihilating
    (Ideal.Quotient.mk T a) (b i) (Ideal.Quotient.mk T (x i))
    (Ideal.Quotient.mk T F) (hcoords i) hzero (hb i)
  refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul, map_pow] using hk

/-- The overlap condition needs only regularity, which survives subsequent
localization of the parameter ring and also permits an empty chart. -/
theorem bertini_coordinate_saturation_of_regular_overlaps
    {R ι : Type*} [CommRing R] (T J : Ideal R) (a : R) (x : ι → R)
    (b : ι → R ⧸ T)
    (hcoords : ∀ i, Ideal.Quotient.mk T (x i) ∈
      Ideal.span ({Ideal.Quotient.mk T a, b i} : Set (R ⧸ T)))
    (hsat : ∀ F ∈ J, ∃ m : ℕ, a ^ m * F ∈ T)
    (hb : ∀ i, b i = 0 ∨ IsRegular
      (algebraMap (R ⧸ T) (Localization.Away (b i)) (Ideal.Quotient.mk T a))) :
    ∀ F ∈ J, ∀ i, ∃ k : ℕ, x i ^ k * F ∈ T := by
  intro F hF i
  obtain ⟨m, hm⟩ := hsat F hF
  have hzero : algebraMap (R ⧸ T) (Localization.Away (Ideal.Quotient.mk T a))
      (Ideal.Quotient.mk T F) = 0 := by
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk T a))
      (Localization.Away (Ideal.Quotient.mk T a)) _).mpr
    refine ⟨⟨Ideal.Quotient.mk T a ^ m, ⟨m, rfl⟩⟩, ?_⟩
    simpa only [map_mul, map_pow] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  obtain ⟨k, hk⟩ := bertini_exists_coordinate_power_annihilating_of_regular_overlap
    (Ideal.Quotient.mk T a) (b i) (Ideal.Quotient.mk T (x i))
    (Ideal.Quotient.mk T F) (hcoords i) hzero (hb i)
  refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul, map_pow] using hk

end
end TranslatedDepthSeven
