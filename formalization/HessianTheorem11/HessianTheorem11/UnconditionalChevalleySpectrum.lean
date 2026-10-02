import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Jacobson.Ring

/-! Two elementary bridges from the proved scheme-theoretic Chevalley
 theorem to principal opens and closed-point lifting. -/
noncomputable section
namespace HessianTheorem11.UnconditionalChevalleySpectrum
open PrimeSpectrum Topology Ideal

/-- The image of an injective finite-presentation map of domains contains
a nonempty principal open: a constructible cell containing the generic
point has no nonzero closed equations. -/
theorem exists_basicOpen_subset_range {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (f : R →+* S) (hfin : f.FinitePresentation)
    (hinj : Function.Injective f) :
    ∃ a : R, a ≠ 0 ∧ (basicOpen a : Set (PrimeSpectrum R)) ⊆ Set.range f.specComap := by
  classical
  obtain ⟨D, he⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfin)
  have hbot : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) ∈ D.toSet := by
    rw [he]
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot f).mp hinj
  obtain ⟨C, hC, hb⟩ := Set.mem_iUnion₂.mp hbot
  have hg (i : Fin C.n) : C.g i = 0 := hb.1 (Set.mem_range_self i)
  have hf : C.f ≠ 0 := by
    intro h
    apply hb.2
    rintro _ rfl
    exact h
  refine ⟨C.f, hf, ?_⟩
  intro P hP
  change P ∈ Set.range (PrimeSpectrum.comap f)
  rw [← he]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    rw [hg]
    exact P.asIdeal.zero_mem
  · intro hp
    exact hP (hp (Set.mem_singleton C.f))

/-- A maximal ideal in the spectral image lifts to a maximal ideal.
Enlarging a lifted prime cannot enlarge its proper contraction beyond the
specified maximal ideal. -/
theorem exists_maximal_over {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : Ideal R) [m.IsMaximal]
    (h : (⟨m, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range f.specComap) :
    ∃ M : Ideal S, M.IsMaximal ∧ M.comap f = m := by
  obtain ⟨P, hp⟩ := h
  obtain ⟨M, hM, hPM⟩ := P.asIdeal.exists_le_maximal P.isPrime.ne_top
  refine ⟨M, hM, ?_⟩
  have hcomp : P.asIdeal.comap f = m := congrArg PrimeSpectrum.asIdeal hp
  have hle : m ≤ M.comap f := hcomp ▸ Ideal.comap_mono hPM
  exact ((Ideal.IsMaximal.eq_of_le ‹m.IsMaximal›
    (Ideal.comap_ne_top f hM.ne_top) hle)).symm

/-- The same generic-point argument for a nonempty principal open in
 the source. -/
theorem exists_basicOpen_subset_image_basicOpen {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hfin : f.FinitePresentation) (hinj : Function.Injective f)
    (b : S) (hb : b ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ (basicOpen a : Set (PrimeSpectrum R)) ⊆
      f.specComap '' (basicOpen b : Set (PrimeSpectrum S)) := by
  classical
  obtain ⟨D, he⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_comap_image hfin (s := basicOpen b) isConstructible_basicOpen)
  have hbot : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R) ∈ D.toSet := by
    rw [he]
    refine ⟨⟨⊥, Ideal.bot_prime⟩, hb, ?_⟩
    apply PrimeSpectrum.ext
    exact (RingHom.injective_iff_ker_eq_bot f).mp hinj
  obtain ⟨C, hC, hc⟩ := Set.mem_iUnion₂.mp hbot
  have hg (i : Fin C.n) : C.g i = 0 := hc.1 (Set.mem_range_self i)
  have hf : C.f ≠ 0 := by
    intro h
    apply hc.2
    rintro _ rfl
    exact h
  refine ⟨C.f, hf, ?_⟩
  intro P hP
  change P ∈ PrimeSpectrum.comap f '' (basicOpen b : Set (PrimeSpectrum S))
  rw [← he]
  refine Set.mem_iUnion₂.mpr ⟨C, hC, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    rw [hg]
    exact P.asIdeal.zero_mem
  · intro hp
    exact hP (hp (Set.mem_singleton C.f))

/-- Jacobson rings allow a lifted prime to be enlarged to a closed point
while retaining a specified nonvanishing condition. -/
theorem exists_maximal_over_avoiding {R S : Type*} [CommRing R] [CommRing S]
    [IsJacobsonRing S] (f : R →+* S) (m : Ideal R) [m.IsMaximal] (b : S)
    (h : (⟨m, inferInstance⟩ : PrimeSpectrum R) ∈
      f.specComap '' (basicOpen b : Set (PrimeSpectrum S))) :
    ∃ M : Ideal S, M.IsMaximal ∧ M.comap f = m ∧ b ∉ M := by
  obtain ⟨P, hbP, hp⟩ := h
  have hnot : b ∉ P.asIdeal.jacobson := by
    rw [(isJacobsonRing_iff_prime_eq.mp inferInstance) P.asIdeal P.isPrime]
    exact hbP
  rw [Ideal.jacobson, Ideal.mem_sInf] at hnot
  push_neg at hnot
  obtain ⟨M, ⟨hPM, hM⟩, hbM⟩ := hnot
  refine ⟨M, hM, ?_, hbM⟩
  have hcomp : P.asIdeal.comap f = m := congrArg PrimeSpectrum.asIdeal hp
  have hle : m ≤ M.comap f := hcomp ▸ Ideal.comap_mono hPM
  exact ((Ideal.IsMaximal.eq_of_le ‹m.IsMaximal›
    (Ideal.comap_ne_top f hM.ne_top) hle)).symm

end HessianTheorem11.UnconditionalChevalleySpectrum
