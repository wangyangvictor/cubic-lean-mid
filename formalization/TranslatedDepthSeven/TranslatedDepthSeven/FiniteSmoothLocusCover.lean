import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Finite principal-open cover of the smooth locus

For a finitely presented algebra with Noetherian coordinate ring, the smooth
locus is open and the prime spectrum is Noetherian.  Hence finitely many
principal opens cover the smooth locus.  Each corresponding localization is
smooth over the base.

This is the qualitative finite-cover part of the dimension devissage.  It
does not construct standard-smooth presentations or give degree and
coefficient-height bounds for the selected principal-open elements.
-/

namespace TranslatedDepthSeven

noncomputable section

open TopologicalSpace

universe u v

/-- A finitely presented algebra with Noetherian coordinate ring has a finite
principal-open cover of its smooth locus, and every member of the cover gives
a smooth localization. -/
theorem exists_finset_basicOpen_cover_smoothLocus
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing A] :
    ∃ T : Finset A,
      Algebra.smoothLocus R A ⊆
        ⋃ f ∈ T, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ∧
      ∀ f ∈ T,
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ⊆
            Algebra.smoothLocus R A ∧
          Algebra.Smooth R (Localization.Away f) := by
  classical
  let Good : Type v :=
    {f : A // (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ⊆
      Algebra.smoothLocus R A}
  let U : Good → Set (PrimeSpectrum A) := fun f ↦
    PrimeSpectrum.basicOpen f.1
  have hopen : ∀ f, IsOpen (U f) := by
    intro f
    exact PrimeSpectrum.isOpen_basicOpen
  have hcover : Algebra.smoothLocus R A ⊆ ⋃ f : Good, U f := by
    intro p hp
    obtain ⟨V, ⟨f, rfl⟩, hpV, hV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        hp Algebra.isOpen_smoothLocus
    exact Set.mem_iUnion.mpr ⟨⟨f, hV⟩, hpV⟩
  obtain ⟨S, hS⟩ :=
    (NoetherianSpace.isCompact (Algebra.smoothLocus R A)).elim_finite_subcover
      U hopen hcover
  let T : Finset A := S.image Subtype.val
  refine ⟨T, ?_, ?_⟩
  · intro p hp
    have hpS := hS hp
    obtain ⟨f, hpS⟩ := Set.mem_iUnion.mp hpS
    obtain ⟨hfS, hpf⟩ := Set.mem_iUnion.mp hpS
    refine Set.mem_iUnion.mpr ⟨f.1, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hpf⟩
    exact Finset.mem_image.mpr ⟨f, hfS, rfl⟩
  · intro f hfT
    obtain ⟨g, hgS, rfl⟩ := Finset.mem_image.mp hfT
    refine ⟨g.2, ?_⟩
    exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp g.2

end

end TranslatedDepthSeven
