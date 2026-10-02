import CubicTenVariables.ConePrincipalOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! The actual principal open of a prime closed locus is nonempty and
dense in that locus. These elementary spectrum statements require no
homogeneity, geometric integrality, or additional algebraic geometry input.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.PrincipalOpenConeTopology

variable {R : Type*} [CommRing R]

/-- Remove the actual closed residual defined by adjoining one equation. -/
def locus (I : Ideal R) (g : R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (I : Set R) \
    PrimeSpectrum.zeroLocus (ConePrincipalOpen.residualIdeal I g : Set R)

/-- The residual-complement definition is precisely the intersection
with the principal basic open. -/
theorem locus_eq_inter_basicOpen (I : Ideal R) (g : R) :
    locus I g = PrimeSpectrum.zeroLocus (I : Set R) ∩
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  ext x
  change (I ≤ x.asIdeal ∧ ¬ ConePrincipalOpen.residualIdeal I g ≤ x.asIdeal) ↔
    (I ≤ x.asIdeal ∧ g ∉ x.asIdeal)
  constructor
  · rintro ⟨hI,hres⟩
    refine ⟨hI,fun hg => hres ?_⟩
    exact sup_le hI (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg))
  · rintro ⟨hI,hg⟩
    exact ⟨hI,fun hres => hg (hres (ConePrincipalOpen.mem_residualIdeal I g))⟩

/-- The generic point belongs to this open whenever the equation does
not vanish identically on the prime closed locus. -/
theorem genericPoint_mem (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) :
    (⟨I,hI⟩ : PrimeSpectrum R) ∈ locus I g := by
  rw [locus_eq_inter_basicOpen]
  exact ⟨fun _ hx => hx,hg⟩

theorem locus_nonempty (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) : (locus I g).Nonempty :=
  ⟨⟨I,hI⟩,genericPoint_mem I hI g hg⟩

/-- The closure is the whole prime closed locus, not just an unspecified
dense subset of it. -/
theorem closure_locus (I : Ideal R) (hI : I.IsPrime)
    (g : R) (hg : g ∉ I) :
    closure (locus I g) = PrimeSpectrum.zeroLocus (I : Set R) := by
  apply le_antisymm
  · exact closure_minimal (fun _ hx => hx.1) (PrimeSpectrum.isClosed_zeroLocus _)
  · have hsub : ({⟨I,hI⟩} : Set (PrimeSpectrum R)) ⊆ locus I g :=
      Set.singleton_subset_iff.mpr (genericPoint_mem I hI g hg)
    simpa only [PrimeSpectrum.closure_singleton] using closure_mono hsub

/-- Openness is relative to the actual closed subset with its induced
topology. No primality or nonvanishing assumption is needed for openness. -/
theorem isOpen_relative (I : Ideal R) (g : R) :
    IsOpen {x : PrimeSpectrum.zeroLocus (I : Set R) | x.val ∈ locus I g} := by
  have heq : {x : PrimeSpectrum.zeroLocus (I : Set R) | x.val ∈ locus I g} =
      Subtype.val ⁻¹' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
    ext x
    rw [locus_eq_inter_basicOpen]
    exact and_iff_right x.property
  rw [heq]
  exact PrimeSpectrum.isOpen_basicOpen.preimage continuous_subtype_val

end CubicTenVariables.PrincipalOpenConeTopology
