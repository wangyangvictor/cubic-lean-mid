import CubicTenVariables.ProperHomogeneousNormalization
import CubicTenVariables.HomogeneousPowerCertificates
import CubicTenVariables.HomogeneousSpanCertificates
import CubicTenVariables.HomogeneousPerturbationCertificate

/-!
# Existence of fixed homogeneous perturbation certificates

For a proper homogeneous equation ideal over an infinite field, linear
normalization followed by its zero fibre provides positive coordinate-power
identities. Homogeneous coefficient extraction turns these into the literal
fixed certificates used for all lower-degree perturbations. The number of
linear forms is bounded by the dimension of the original quotient.
-/

noncomputable section
namespace CubicTenVariables.HomogeneousPerturbationExistence
open MvPolynomial TranslatedDepthSeven
open HomogeneousPerturbationCertificate HomogeneousPowerCertificates
open HomogeneousSpanCertificates

universe u v
variable {K : Type u} [Field K] [Infinite K]
variable {n : ℕ} {ι : Type v} [Fintype ι]

local instance : GradedAlgebra (homogeneousSubmodule (Fin n) K) :=
  MvPolynomial.gradedAlgebra

/-- One fixed system of linear forms and coordinate-power identities for a
proper homogeneous equation ideal, with no primeness or positive-degree
assumptions. The certificate is chosen before any perturbation. -/
theorem exists_certificate (f : ι → MvPolynomial (Fin n) K) (e : ι → ℕ)
    (hhom : ∀ j, (f j).IsHomogeneous (e j))
    (hproper : Ideal.span (Set.range f) ≠ ⊤) (r : ℕ)
    (hdim : ringKrullDim
      (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) ≤ (r : WithBot ℕ∞)) :
    ∃ s : ℕ, s ≤ r ∧ ∃ d : Fin n → ℕ, Nonempty (Certificate f e d s) := by
  classical
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span (Set.range f)
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    exact ⟨e j, hhom j⟩
  obtain ⟨D, hD⟩ :=
    ProperHomogeneousNormalization.exists_homogeneousLinearNormalizationData_parameterCount_le
      n I hproper hIhom r hdim
  obtain ⟨d, hd, hmem⟩ := exists_cut_coordinate_powers I D hIhom
  have hcut : Ideal.span (Set.range (Sum.elim f D.forms)) = cutIdeal I D := by
    rw [Set.Sum.elim_range, Ideal.span_union]
    rfl
  have hcombined : ∀ j, (Sum.elim f D.forms j).IsHomogeneous
      (Sum.elim e (fun _ : Fin D.parameterCount => 1) j) := by
    intro j
    cases j with
    | inl j => exact hhom j
    | inr j => exact D.forms_isHomogeneous j
  obtain ⟨c, hc, hchom, hczero⟩ := exists_coordinate_power_coefficients
    (Sum.elim f D.forms) (Sum.elim e (fun _ : Fin D.parameterCount => 1))
    hcombined d (fun i => hcut.symm ▸ hmem i)
  exact ⟨D.parameterCount, hD, d, ⟨{
    forms := D.forms
    forms_homogeneous := D.forms_isHomogeneous
    powers_pos := hd
    coefficients := c
    coefficients_homogeneous := hchom
    coefficients_zero := hczero
    identity := hc }⟩⟩

end CubicTenVariables.HomogeneousPerturbationExistence
