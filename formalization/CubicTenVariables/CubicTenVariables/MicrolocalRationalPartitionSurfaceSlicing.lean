import CubicTenVariables.MicrolocalPartitionCountsSurfaceSlicing
import CubicTenVariables.MicrolocalRationalPartition

/-!
# The actual microlocal partition from componentwise surface slicing

This file replaces the general Salberger counting premise only along the
two high rows of the actual n=10 promotion table.  It leaves the needed
geometric content explicit as surface-slicing data on those components.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace CubicTenVariables.MicrolocalRationalPartition

open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels MicrolocalPartitionCounts
open MicrolocalPromotedPartition ConeComponentProgressionCount
open ConeComponentSurfaceSlicingEndpoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The application-specific geometric premise needed in place of the
general Salberger theorem: for a relevant anisotropic cubic microlocal
geometry and actual depth model at level three or four, there exists a
promotion table whose original components have the surface-slicing data
used by the high-row count. -/
def HighTableSurfaceSlicing : Prop :=
  ∀ {t N : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10},
    Geometry F f → F.IsHomogeneous 3 →
    Anisotropic (map (Int.castRingHom ℚ) F) →
    ∀ (j : Fin 6), (j.val = 3 ∨ j.val = 4) →
    ZDepthModel f (j.val + 1) N →
    ∃ T : MicrolocalPromotionTable.Table F f j.val,
      ∀ i, HighComponentSurfaceSlicingData (8 - j.val)
        (PolynomialExponentialFamily.baseIdeal (T.G i))

/-- Construct the same rational microlocal partition as the established
route, using `table_part_bound_of_surfaceSlicing` only for rows three and
four. -/
theorem exists_partition_of_surfaceSlicing
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (surfaceSlicing : HighTableSurfaceSlicing)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ)
      (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
      (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val + 1)),
      Conclusion F f N B T := by
  classical
  obtain ⟨t, f, N, B, hN, hB, hgeo, hdata⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hF hAn
  have htable : ∀ i : Fin 4,
      ∃ T : MicrolocalPromotionTable.Table F f (i.val + 1),
        (i.val + 1 = 3 ∨ i.val + 1 = 4) →
          ∀ k, HighComponentSurfaceSlicingData (8 - (i.val + 1))
            (PolynomialExponentialFamily.baseIdeal (T.G k)) := by
    intro i
    by_cases hi : i.val + 1 = 3 ∨ i.val + 1 = 4
    · let j : Fin 6 := ⟨i.val + 1, by omega⟩
      obtain ⟨Ti, hTi⟩ := surfaceSlicing hgeo hF hAn j
        (by simpa only [j] using hi)
        (by simpa only [j] using
          hdata.depth_models ⟨i.val + 1, by omega⟩)
      refine ⟨Ti, fun _ => ?_⟩
      simpa only [j] using hTi
    · let Ti : MicrolocalPromotionTable.Table F f (i.val + 1) :=
        Classical.choice
          (MicrolocalPromotionTable.exists_table degreeSpan smooth spread weil
            dichotomy hgeo hF hAn
              (by omega : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ 4)
              (hdata.depth_models ⟨i.val + 1, by omega⟩))
      exact ⟨Ti, fun h => (hi h).elim⟩
  choose T hTslicing using htable
  let O : Fin 4 → Set (Fin 10 → ℚ) := fun i => (T i).open
  let U := promotionFamily O
  have hU : Compatible f U := promotionFamily_compatible O
    (fun i => (T i).open_subset_layer (by omega))
  have hcount : Counts f U := by
    constructor
    · obtain ⟨C, hC, hbound⟩ := AmbientProgressionCount.exists_ten_bound
      exact ⟨C, hC, hbound (part f U ⟨0, by decide⟩)⟩
    · intro j hj
      obtain ⟨C, hC, hbound⟩ := exists_low_level_bound hgeo hAn j hj
      exact ⟨C, hC, hbound U hU⟩
    · intro j hj ε hε
      rcases hj with hj | hj
      · have he : j = (⟨3, by decide⟩ : Fin 6) := Fin.ext hj
        subst j
        exact table_part_bound_of_surfaceSlicing hgeo hAn
          ⟨3, by decide⟩ (Or.inl rfl) (T 2)
          (hTslicing 2 (Or.inl rfl))
          U hU (promotionFamily_level O 2) ε hε
      · have he : j = (⟨4, by decide⟩ : Fin 6) := Fin.ext hj
        subst j
        exact table_part_bound_of_surfaceSlicing hgeo hAn
          ⟨4, by decide⟩ (Or.inr rfl) (T 3)
          (hTslicing 3 (Or.inr rfl))
          U hU (promotionFamily_level O 3) ε hε
    · obtain ⟨C, hC, hbound⟩ := exists_terminal_bound hgeo hF hAn
      exact ⟨C, hC, hbound U hU⟩
  have hunique : ∀ x : Fin 10 → ℚ, x ≠ 0 →
      ∃! j : Fin 6, x ∈ part f U j :=
    fun x hx => existsUnique_level U hU x hx
  have hcert := MicrolocalPartitionCertificates.exists_certificates
    F hF hAn f N B hN hgeo hdata T
  exact ⟨t, f, N, B, T,
    ⟨hN, hB, hgeo, hdata, hU, hcount,
      fun ε hε => MicrolocalUniformPartitionCount.exists_uniform_bound
        hcount ε hε,
      hcert, hunique, union_parts _ hU, union_with_origin _ hU,
      fun j a ha x =>
        MicrolocalPartitionCounts.part_smul_mem_iff hgeo T j a ha x⟩⟩

end CubicTenVariables.MicrolocalRationalPartition
