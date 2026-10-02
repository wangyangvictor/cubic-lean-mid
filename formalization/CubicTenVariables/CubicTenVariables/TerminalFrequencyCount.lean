import CubicTenVariables.OffTerminalFrequencyCertificate
import CubicTenVariables.RationalConeIntegralModel
import CubicTenVariables.HomogeneousProgressionBoxCount
import CubicTenVariables.ConeComponentProgressionCount

/-! The actual B4 exceptional frequencies have a linear progression count.
The rational closure and its dimension are proved geometry; no counting
hypothesis or literature result is supplied. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.TerminalFrequencyCount
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open RationalConeClosure RationalClosureIdempotent ConeComponentProgressionCount
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Counting on a rational cone closure controls every subset of the
original rational cone, without asserting that the original cone is closed. -/
theorem cone_bound {n : ℕ} (Z : Set (GeometricPoint n)) (hcone : IsAffineCone Z)
    (d : ℕ) (hd : affineDimension (rationalConeClosure Z) ≤ (d : Dimension)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ P : Set (Fin n → ℚ), P ⊆ rationalPoints Z →
      ∀ (u : Fin n → ℝ) (L : ℝ), 0 ≤ L → ∀ m : ℕ, 0 < m →
      ∀ b : Fin n → ℤ, ((points P u L m b).card : ℝ) ≤
        K*(1+L/(m : ℝ))^d := by
  obtain ⟨s,G,e,_he,hQ,hG,_hzero⟩ := RationalConeIntegralModel.exists_homogeneous_model Z hcone
  have hne : (rationalConeClosure Z).Nonempty := by
    refine ⟨0,?_⟩
    exact Or.inr rfl
  have hproper := IntegralModelDimension.rationalIdeal_ne_top G _ hne hG
  have hhom : (IntegralModelDimension.rationalIdeal G).IsHomogeneous
      (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hQ]
    exact RationalConeIntegralModel.rationalIdeal_isHomogeneous Z hcone
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸
      IntegralModelDimension.rationalIdeal G) ≤ (d : Dimension) := by
    rw [IntegralModelDimension.rational_quotient_dimension_eq G _ hne hG]
    exact hd
  obtain ⟨K,hK,hcount⟩ := HomogeneousProgressionBoxCount.exists_bound
    _ hproper hhom d hdim
  refine ⟨K,hK,?_⟩
  intro P hP u L hL m hm b
  apply hcount (points P u L m b) u L hL m hm b
  · intro x hx
    exact ((mem_points P u L m b x).mp hx).1
  · intro x hx
    exact ((mem_points P u L m b x).mp hx).2.1
  · intro x hx
    have hPx := hP ((mem_points P u L m b x).mp hx).2.2
    rw [hQ]
    intro g hg
    exact hg _ (rational_generators_subset Z ⟨_,Or.inl hPx,rfl⟩)

/-- The literal B4 bad-section locus has O(1+L/m) integral points in every
translated progression box. The constant precedes all box and residue data. -/
theorem exists_bound (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ m : ℕ, 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (OffTerminalFrequencyCertificate.exceptionalSet F) u L m b).card : ℝ) ≤
          K*(1+L/(m : ℝ)) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hF.map _,hAn⟩
  obtain ⟨K,hK,hcount⟩ := cone_bound
    (TerminalBadNormals.badNormals (geometricPolynomial A.polynomial) 4)
    (TerminalBadNormals.badNormals_isAffineCone _ _) 1
    (TerminalTenBound.rational_fourth_stratum_dimension_le_one A)
  refine ⟨K,hK,?_⟩
  have hsub : OffTerminalFrequencyCertificate.exceptionalSet F ⊆
      rationalPoints (TerminalBadNormals.badNormals (geometricPolynomial A.polynomial) 4) := by
    intro v hv
    exact ((OffTerminalFrequencyCertificate.mem_exceptional_iff F hF v).mp hv).2
  intro u L hL m hm b
  simpa only [pow_one] using hcount _ hsub u L hL m hm b

end CubicTenVariables.TerminalFrequencyCount
