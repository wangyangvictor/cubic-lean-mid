import HessianTheorem11.UnconditionalGenericFieldSmooth
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! A dominant finite-presentation map of characteristic-zero domains is
smooth on a nonempty source principal open. This is used toward orbit-map
openness. No generic smoothness theorem is assumed. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open scoped nonZeroDivisors

variable (B A : Type*) [CommRing B] [IsDomain B] [CharZero B]
    [CommRing A] [IsDomain A] [Algebra B A] [FaithfulSMul B A]

/-- The fraction field of the source is formally smooth over the base. -/
theorem fractionRing_formallySmooth : Algebra.FormallySmooth B (FractionRing A) := by
  letI : Algebra (FractionRing B) (FractionRing A) :=
    FractionRing.liftAlgebra B (FractionRing A)
  letI : IsScalarTower B (FractionRing B) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra B (FractionRing A)
  letI : Algebra.FormallyEtale B (FractionRing B) :=
    Algebra.FormallyEtale.of_isLocalization B⁰
  letI : Algebra.FormallySmooth (FractionRing B) (FractionRing A) :=
    field_formallySmooth (FractionRing B) (FractionRing A)
  exact Algebra.FormallySmooth.comp B (FractionRing B) (FractionRing A)

/-- The generic point lies in the actual smooth locus. -/
theorem genericPoint_mem_smoothLocus [Algebra.FinitePresentation B A] :
    (⟨⊥,Ideal.bot_prime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus B A := by
  letI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
  letI : Algebra.FormallySmooth B (FractionRing A) := fractionRing_formallySmooth B A
  letI : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    have he : (⊥ : Ideal A).primeCompl = A⁰ := by
      ext x
      simp [mem_nonZeroDivisors_iff_ne_zero]
    change IsLocalization A⁰ (Localization.AtPrime (⊥ : Ideal A))
    rw [← he]
    infer_instance
  change Algebra.FormallySmooth B (Localization.AtPrime (⊥ : Ideal A))
  exact (Algebra.FormallySmooth.iff_of_equiv
    ((IsLocalization.algEquiv A⁰ (Localization.AtPrime (⊥ : Ideal A))
      (FractionRing A)).restrictScalars B)).mpr inferInstance

/-- A genuine nonempty source principal open on which the map is smooth. -/
theorem exists_smooth_principal_open [Algebra.FinitePresentation B A] :
    ∃ f : A, f ≠ 0 ∧ Algebra.Smooth B (Localization.Away f) := by
  have hg := genericPoint_mem_smoothLocus B A
  obtain ⟨_,⟨_,⟨f,rfl⟩,rfl⟩,hf,hsub⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hg
      (Algebra.isOpen_smoothLocus (R := B) (A := A))
  refine ⟨f,?_,Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp hsub⟩
  simpa using hf

/-- The resulting localized spectral map is open, by smoothness, flatness,
going down and the proved Chevalley theorem. -/
theorem exists_open_principal_spectrum_map [Algebra.FinitePresentation B A] :
    ∃ f : A, f ≠ 0 ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
  obtain ⟨f,hf,hs⟩ := exists_smooth_principal_open B A
  letI := hs
  exact ⟨f,hf,PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation⟩

end HessianTheorem11.UnconditionalGeneric
