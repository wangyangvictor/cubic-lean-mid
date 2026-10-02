import CubicTenVariables.ConeComponentFixedLeadingCount
import CubicTenVariables.MicrolocalRationalPartition

/-!
# The original numerical microlocal partition from fixed-leading counts

Only the high-row component-count call is replaced. The actual promotion
tables, rational partition, prime certificates, homogeneity and uniform
progression counts are the existing ones. No surface-family slicing or
additional geometry certificate is a hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace CubicTenVariables.MicrolocalFixedLeadingPartition
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open MicrolocalPromotedPartition ConeComponentProgressionCount MicrolocalPartitionCounts
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Apply fixed-leading cone counts to the actual high-row finite cover. -/
theorem table_part_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (highCounts : ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts) (hgeo : Geometry F f)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val=3 ∨ j.val=4)
    (T : MicrolocalPromotionTable.Table F f j.val)
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U) (hopen : U j.val = T.open)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(8-j.val) := by
  obtain ⟨k, J, hJ, hcover⟩ := MicrolocalPromotionCover.exists_part_cover hgeo hAn j hj
    (fun i => PolynomialExponentialFamily.baseIdeal (T.G i)) T.prime T.homogeneous
    T.cover_point (fun i => map (Int.castRingHom ℚ) (T.h i))
    (T.cases_for_high_levels hj) U hU hopen
  obtain ⟨C, hC, hcount⟩ :=
    ConeComponentFixedLeadingCount.exists_high_level_bound highCounts j.val hj J hJ ε hε
  exact ⟨C, hC, hcount _ hcover⟩

/-- Construct all four tables from the actual exceptional loci, and prove
all selected progression counts on their single partition. -/
theorem exists_partition_counts {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10} {N : ℕ}
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (highCounts : ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts)
    (hgeo : Geometry F f) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (hmodels : ∀ i : Fin 9, ZDepthModel f (i.val+1) N) :
    ∃ T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1),
      Compatible f (promotionFamily (fun i => (T i).open)) ∧
      Counts f (promotionFamily (fun i => (T i).open)) ∧
      ∀ x : Fin 10 → ℚ, x ≠ 0 →
        ∃! j : Fin 6, x ∈ part f (promotionFamily (fun i => (T i).open)) j := by
  classical
  let T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1) := fun i =>
    Classical.choice (MicrolocalPromotionTable.exists_table degreeSpan smooth spread weil dichotomy
      hgeo hF hAn (by omega : 1 ≤ i.val+1 ∧ i.val+1 ≤ 4)
      (hmodels ⟨i.val+1,by omega⟩))
  let O : Fin 4 → Set (Fin 10 → ℚ) := fun i => (T i).open
  let U := promotionFamily O
  have hU : Compatible f U := promotionFamily_compatible O
    (fun i => (T i).open_subset_layer (by omega))
  refine ⟨T,hU,?_,fun x hx => existsUnique_level U hU x hx⟩
  constructor
  · obtain ⟨C,hC,hbound⟩ := AmbientProgressionCount.exists_ten_bound
    exact ⟨C,hC,hbound (part f U ⟨0,by decide⟩)⟩
  · intro j hj
    obtain ⟨C,hC,hbound⟩ := exists_low_level_bound hgeo hAn j hj
    exact ⟨C,hC,hbound U hU⟩
  · intro j hj ε hε
    rcases hj with hj | hj
    · have he : j = (⟨3,by decide⟩ : Fin 6) := Fin.ext hj
      subst j
      exact table_part_bound highCounts hgeo hAn ⟨3,by decide⟩ (Or.inl rfl) (T 2) U hU
        (promotionFamily_level O 2) ε hε
    · have he : j = (⟨4,by decide⟩ : Fin 6) := Fin.ext hj
      subst j
      exact table_part_bound highCounts hgeo hAn ⟨4,by decide⟩ (Or.inr rfl) (T 3) U hU
        (promotionFamily_level O 3) ε hε
  · obtain ⟨C,hC,hbound⟩ := exists_terminal_bound hgeo hF hAn
    exact ⟨C,hC,hbound U hU⟩

/-- The actual partition and its counts, with no incidence, models,
components, opens or component classification left as supplied data.
The listed literature hypotheses remain explicit; the integrality inputs have internal proofs. -/
theorem exists_from_literature
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (highCounts : ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      1 ≤ N ∧ 1 ≤ B ∧ Geometry F f ∧ TenMicrolocalIncidence.Conclusion F f N B ∧
      Compatible f (promotionFamily (fun i => (T i).open)) ∧
      Counts f (promotionFamily (fun i => (T i).open)) ∧
      ∀ x : Fin 10 → ℚ, x ≠ 0 →
        ∃! j : Fin 6, x ∈ part f (promotionFamily (fun i => (T i).open)) j := by
  obtain ⟨t,f,N,B,hN,hB,hgeo,hdata⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hF hAn
  obtain ⟨T,hU,hcount,hunique⟩ := exists_partition_counts degreeSpan smooth spread weil dichotomy
    highCounts hgeo hF hAn hdata.depth_models
  exact ⟨t,f,N,B,T,hN,hB,hgeo,hdata,hU,hcount,hunique⟩

/-- Construct the numerical partition and all required selected counting
and prime-certificate interfaces without supplied application data. -/
theorem exists_partition
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (highCounts : ConeComponentFixedLeadingCount.HighDegreeFixedLeadingCounts)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      MicrolocalRationalPartition.Conclusion F f N B T := by
  obtain ⟨t,f,N,B,T,hN,hB,hgeo,hdata,hU,hcount,hunique⟩ :=
    exists_from_literature microlocal degreeSpan smooth spread weil
      dichotomy highCounts F hF hAn
  have hcert := MicrolocalPartitionCertificates.exists_certificates F hF hAn f N B hN hgeo hdata T
  exact ⟨t,f,N,B,T,⟨hN,hB,hgeo,hdata,hU,hcount,
    fun ε hε => MicrolocalUniformPartitionCount.exists_uniform_bound hcount ε hε,hcert,hunique,
    union_parts _ hU,union_with_origin _ hU,
    fun j a ha x => MicrolocalPartitionCounts.part_smul_mem_iff hgeo T j a ha x⟩⟩


end CubicTenVariables.MicrolocalFixedLeadingPartition
