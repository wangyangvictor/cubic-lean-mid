import TranslatedDepthSeven.HomogeneousConeStandardChart
import TranslatedDepthSeven.ProjectiveConeSectionInternal
import TranslatedDepthSeven.RationalSmoothPointGeometricIntegrality

/-! # The first affine chart of a projective cone is its original affine cone

Adjoining an unused first coordinate and then setting it to one recovers
the original ideal exactly. This permits the projective smooth-rational-point
criterion to be used on the entire affine cone without choosing a nonzero
coordinate of each point.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000

theorem projectiveConeFinIdeal_eq_map_rename_succ
    {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    projectiveConeFinIdeal K N I = I.map (rename Fin.succ) := by
  unfold projectiveConeFinIdeal projectiveConeIdealExtension
  change (I.map (rename some).toRingHom).map
    (renameEquiv K (_root_.finSuccEquiv (N + 1)).symm).toRingHom = _
  rw [Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp

theorem map_projectiveConeFinIdeal_standardDehomogenization
    {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) :
    (projectiveConeFinIdeal K N I).map
      (standardDehomogenizationHom K (N + 1)) = I := by
  rw [projectiveConeFinIdeal_eq_map_rename_succ]
  change (I.map (rename Fin.succ).toRingHom).map
    (standardDehomogenizationHom K (N + 1)) = I
  rw [Ideal.map_map]
  have hcomp : (standardDehomogenizationHom K (N + 1)).comp
      (rename Fin.succ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [standardDehomogenizationHom]
    · intro i
      simp [standardDehomogenizationHom]
  rw [hcomp, Ideal.map_id]

theorem firstCoordinate_not_mem_projectiveConeFinIdeal
    {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hne : I ≠ ⊤) :
    X (0 : Fin ((N + 1) + 1)) ∉ projectiveConeFinIdeal K N I := by
  intro hX
  have hmem := Ideal.mem_map_of_mem
    (standardDehomogenizationHom K (N + 1)) hX
  rw [map_projectiveConeFinIdeal_standardDehomogenization] at hmem
  have hone : (1 : MvPolynomial (Fin (N + 1)) K) ∈ I := by
    simpa [standardDehomogenizationHom] using hmem
  exact hne ((Ideal.eq_top_iff_one I).mpr hone)

theorem projectiveConeFinIdeal_isHomogeneous
    {K : Type*} [Field K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K)) :
    (projectiveConeFinIdeal K N I).IsHomogeneous
      (homogeneousSubmodule (Fin ((N + 1) + 1)) K) := by
  exact map_renameEquiv_isHomogeneous (_root_.finSuccEquiv (N + 1)).symm
    (projectiveConeIdealExtension I) (projectiveConeIdealExtension_isHomogeneous I hhom)

/-- The existing projective textbook input applies to a smooth rational
point anywhere on the original affine cone, by adjoining one coordinate. -/
theorem geometricallyPrime_of_smoothRationalPoint_on_homogeneous_affineCone
    (hSmooth : StandardAG.RationalProjectiveSmoothPointGeometricIntegrality)
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (z : Fin (N + 1) → ℚ) (hz : IsSmoothAffineIdealRationalPoint I z) :
    GeometricallyPrimeMvPolynomialIdeal I := by
  apply (geometricallyPrime_projectiveConeFinIdeal_iff N I).mp
  apply hSmooth (N + 1) (projectiveConeFinIdeal ℚ N I)
    (projectiveConeFinIdeal_isPrime ℚ N I hprime)
    (projectiveConeFinIdeal_isHomogeneous N I hhom)
    (firstCoordinate_not_mem_projectiveConeFinIdeal N I hprime.ne_top) z
  have hchart : rationalProjectiveAffineChartIdeal (projectiveConeFinIdeal ℚ N I) = I :=
    map_projectiveConeFinIdeal_standardDehomogenization N I
  rwa [hchart]

end
end TranslatedDepthSeven
