import CubicTenVariables.MicrolocalPartitionCounts
import CubicTenVariables.MicrolocalPartitionCertificates
import CubicTenVariables.MicrolocalUniformPartitionCount

/-! The selected numerical rational-frequency partition for ten variables.
One shared incidence and four constructed component tables provide the
partition, homogeneity, all selected progression counts, and polynomial-height
prime certificates on all six nonzero levels. The origin is separate.
The listed literature hypotheses and proved integrality inputs remain explicit. No adapted smooth
stratification or lisse-sheaf structure is asserted by this replacement. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalRationalPartition
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData MicrolocalPartitionCounts MicrolocalPromotedPartition

/-- Every field refers to the very same incidence, tables and partition. -/
structure Conclusion {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)) : Prop where
  modulus_pos : 1 ≤ N
  betti_pos : 1 ≤ B
  geometry : Geometry F f
  incidence : TenMicrolocalIncidence.Conclusion F f N B
  compatible : Compatible f (promotionFamily (fun i => (T i).open))
  counts : Counts f (promotionFamily (fun i => (T i).open))
  uniform_counts : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (j : Fin 6) (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((ConeComponentProgressionCount.points
          (part f (promotionFamily (fun i => (T i).open)) j) u L m b).card : ℝ) ≤
            C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(MicrolocalUniformPartitionCount.profile j)
  certificates : MicrolocalPartitionCertificates.Certificates F f
    (promotionFamily (fun i => (T i).open))
  unique_level : ∀ x : Fin 10 → ℚ, x ≠ 0 →
    ∃! j : Fin 6, x ∈ part f (promotionFamily (fun i => (T i).open)) j
  punctured_cover : (⋃ j : Fin 6, part f (promotionFamily (fun i => (T i).open)) j) =
    {x | x ≠ 0}
  cover_with_origin : (⋃ j : Fin 6, part f (promotionFamily (fun i => (T i).open)) j) ∪ {0} =
    Set.univ
  homogeneous : ∀ (j : Fin 6) (a : ℚ), a ≠ 0 → ∀ x : Fin 10 → ℚ,
    a • x ∈ part f (promotionFamily (fun i => (T i).open)) j ↔
      x ∈ part f (promotionFamily (fun i => (T i).open)) j

/-- Construct the numerical partition and all required selected counting
and prime-certificate interfaces without supplied application data. -/
theorem exists_partition
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (lit : Published.Salberger2023Theorem04)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ)
      (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1)),
      Conclusion F f N B T := by
  obtain ⟨t,f,N,B,T,hN,hB,hgeo,hdata,hU,hcount,hunique⟩ :=
    MicrolocalPartitionCounts.exists_from_literature microlocal degreeSpan smooth spread weil
      dichotomy lit F hF hAn
  have hcert := MicrolocalPartitionCertificates.exists_certificates F hF hAn f N B hN hgeo hdata T
  exact ⟨t,f,N,B,T,⟨hN,hB,hgeo,hdata,hU,hcount,
    fun ε hε => MicrolocalUniformPartitionCount.exists_uniform_bound hcount ε hε,hcert,hunique,
    union_parts _ hU,union_with_origin _ hU,
    fun j a ha x => MicrolocalPartitionCounts.part_smul_mem_iff hgeo T j a ha x⟩⟩

end CubicTenVariables.MicrolocalRationalPartition
