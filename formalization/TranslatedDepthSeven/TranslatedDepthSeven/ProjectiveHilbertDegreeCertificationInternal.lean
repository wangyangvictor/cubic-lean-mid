import TranslatedDepthSeven.ProjectiveHilbertCertificateFromNormalizationInternal
import TranslatedDepthSeven.HomogeneousNormalizationParameterPositiveInternal

/-!
# Internal projective Hilbert--Serre certification

This discharges the exact projective Hilbert-polynomial input used in the
root theorem, over every characteristic-zero field. Polynomial existence,
degree, positive integral multiplicity, and Krull dimension have all been
proved internally. The irrelevant-ideal condition is used only to exclude
zero normalization dimension. There are no additional geometric inputs.
-/

namespace TranslatedDepthSeven

noncomputable section

theorem projectiveHilbertDegreeCertification_internal
    (K : Type*) [Field K] [CharZero K] :
    StandardAG.ProjectiveHilbertDegreeCertification K := by
  intro N I hprime hhom hirr
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData (N + 1) I hprime hhom
  have hD := D.parameterCount_pos_of_irrelevant_not_le I hprime hhom hirr
  obtain ⟨d, P, hP⟩ := exists_projectiveHilbertCertificate_of_normalization
    I hprime hhom D hD
  exact ⟨D.parameterCount - 1, d, P, hP⟩

end
end TranslatedDepthSeven
