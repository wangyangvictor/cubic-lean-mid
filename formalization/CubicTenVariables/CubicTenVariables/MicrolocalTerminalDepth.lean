import CubicTenVariables.ProjectiveMicrolocalModels
import CubicTenVariables.TerminalTenBound

/-! Terminal improvement for the actual microlocal depth-five rational
locus. The incidence equations imply containment in the raw fourth
section-singularity locus before any rational closure is taken. The
existing ten-variable terminal theorem then gives dimension at most one.
No singular-support existence or additional literature input is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalTerminalDepth
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData ProjectiveMicrolocalDepth ProjectiveMicrolocalModels
open BihomogeneousIncidenceFamily RationalConeClosure

variable {n t : ℕ} {F : MvPolynomial (Fin n) ℤ}
  {f : Fin t → BihomogeneousIncidenceFamily.Polynomial n n}

/-- The stronger raw inclusion avoids adding new rational points by first
closing the geometric section-singularity locus. -/
theorem depth_succ_subset_badNormals (h : Geometry F f) (r : ℕ) :
    depth f (r+1) ⊆ TerminalBadNormals.badNormals
      (geometricPolynomial (map (Int.castRingHom ℚ) F)) r :=
  ConormalTerminalComparison.depth_subset_section_badNormals _ _
    (incidence_subset_section h) r

theorem depth_succ_subset_sectionClosure (h : Geometry F f) (r : ℕ) :
    depth f (r+1) ⊆
      TerminalIntegralClosureModels.sectionClosure (map (Int.castRingHom ℚ) F) r :=
  (depth_succ_subset_badNormals h r).trans
    (TerminalIntegralClosureModels.subset_nonzeroClosure _)

/-- Every higher actual depth locus lies in the same terminal closure. -/
theorem depth_ge_subset_sectionClosure (h : Geometry F f) {j r : ℕ}
    (hj : r+1 ≤ j) :
    depth f j ⊆
      TerminalIntegralClosureModels.sectionClosure (map (Int.castRingHom ℚ) F) r :=
  (depth_antitone hj).trans (depth_succ_subset_sectionClosure h r)

/-- This uses the empty-preserving closure of the actual rational points
on the left. The origin adjoined on the right causes no added premise. -/
theorem rationalDepth_succ_subset_rational_terminal (h : Geometry F f) (r : ℕ) :
    rationalDepth f (r+1) ⊆ rationalConeClosure
      (TerminalBadNormals.badNormals (geometricPolynomial (map (Int.castRingHom ℚ) F)) r) := by
  intro v hv
  apply Or.inl
  apply geometricClosure_mono ?_ hv
  rintro _ ⟨q,hq,rfl⟩
  exact ⟨q,depth_succ_subset_badNormals h r hq,rfl⟩

/-- The actual rational depth-five locus in ten variables has affine
dimension at most one. This is stronger than the general conormal bound. -/
theorem rationalDepth_five_dimension_le_one {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    affineDimension (rationalDepth f 5) ≤ (1 : Dimension) := by
  let A : AnisotropicCubic 10 := ⟨map (Int.castRingHom ℚ) F,hhom.map _,hF⟩
  exact (affineDimension_mono (rationalDepth_succ_subset_rational_terminal h 4)).trans
    (TerminalTenBound.rational_fourth_stratum_dimension_le_one A)

/-- One fixed integral homogeneous equation list models the actual R5,
with its exact rational points and dimension at most one in every good
characteristic, including an empty R5. -/
theorem exists_rationalDepth_five_model {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (h : Geometry F f) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (m : ℕ) (G : Fin m → MvPolynomial (Fin 10) ℤ) (d : Fin m → ℕ),
      (∀ i, (G i).IsHomogeneous (d i)) ∧
      IntegralModelDimension.rationalIdeal G = vanishingIdeal ℚ (rationalPoints (depth f 5)) ∧
      IntegralModelDimension.geometricIdeal G = vanishingIdeal GeometricField (rationalDepth f 5) ∧
      (∀ x : GeometricPoint 10, x ∈ rationalDepth f 5 ↔
        ∀ i, eval₂ (Int.castRingHom GeometricField) x (G i) = 0) ∧
      (∀ q : Fin 10 → ℚ, (∀ i, eval₂ (Int.castRingHom ℚ) q (G i) = 0) ↔
        rationalEmbedding q ∈ depth f 5) ∧
      ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ D →
        ∀ (K : Type) [Field K] [CharP K p],
          ringKrullDim (MvPolynomial (Fin 10) K ⧸
            FixedEquationNormalization.equationIdeal G K) ≤ (1 : Dimension) ∧
          ringKrullDim (MvPolynomial (Fin 10) K ⧸ vanishingIdeal K
            (FixedEquationDimensionReduction.zeroSet G K)) ≤ (1 : Dimension) :=
  ExactRationalConeModel.exists_model_good_characteristic_dimension_bound
    (depth f 5) (depth_cone h 5) (depth_closed h (by decide))
      (rationalDepth_five_dimension_le_one h hhom hF)

end CubicTenVariables.MicrolocalTerminalDepth
