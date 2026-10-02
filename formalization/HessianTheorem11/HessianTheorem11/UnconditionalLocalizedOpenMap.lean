import HessianTheorem11.UnconditionalGenericSmoothLocus

/-! Transport openness on a source principal localization to the image of
any smaller principal open in the original affine spectrum. -/
noncomputable section
namespace HessianTheorem11.UnconditionalGeneric
open PrimeSpectrum

/-- The exact basic-open image under a principal localization. -/
theorem localization_basicOpen_image {A : Type*} [CommRing A] (f b : A) :
    comap (algebraMap A (Localization.Away f)) ''
      (basicOpen (algebraMap A (Localization.Away f) b) : Set _) =
      (basicOpen (f * b) : Set (PrimeSpectrum A)) := by
  have he : (basicOpen (algebraMap A (Localization.Away f) b) : Set _) =
      comap (algebraMap A (Localization.Away f)) ⁻¹' (basicOpen b : Set _) := rfl
  rw [he,Set.image_preimage_eq_inter_range,localization_away_comap_range (Localization.Away f) f]
  simp [basicOpen_mul,Set.inter_comm]

/-- Openness of the localized map implies openness of the image of D(fb). -/
theorem isOpen_image_basicOpen_mul {B A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] (f b : A)
    (hopen : IsOpenMap (comap (algebraMap B (Localization.Away f)))) :
    IsOpen (comap (algebraMap B A) '' (basicOpen (f * b) : Set _)) := by
  have he : (comap (algebraMap B (Localization.Away f)) : PrimeSpectrum (Localization.Away f) → _) =
      comap (algebraMap B A) ∘ comap (algebraMap A (Localization.Away f)) := by
    rw [IsScalarTower.algebraMap_eq B A (Localization.Away f),comap_comp]
    rfl
  have h := hopen (basicOpen (algebraMap A (Localization.Away f) b))
    (basicOpen _).isOpen
  rw [he,Set.image_comp,localization_basicOpen_image] at h
  exact h

end HessianTheorem11.UnconditionalGeneric
