import CubicTenVariables.PrimeSquarePartitionCertificates
import CubicTenVariables.TenMicrolocalIncidenceData

/-! The selected seven-part Q partition, constructed from one actual
incidence family. The prime-square estimates, positive polynomial-height
certificates, rational progression counts and good-prime depth models
refer to that same family. The existential construction retains the
microlocal/model hypotheses and the proved prime-field count interface. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.MicrolocalSquareRationalPartition
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData MicrolocalSquarePartition

structure Conclusion {t : ℕ} (F : MvPolynomial (Fin 10) ℤ)
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ) : Prop where
  modulus_pos : 1 ≤ N
  betti_pos : 1 ≤ B
  geometry : Geometry F f
  incidence : TenMicrolocalIncidence.Conclusion F f N B
  unique_level : ∀ x : Fin 10 → ℚ, ∃! j : Fin 7, x ∈ part f j
  cover : (⋃ j : Fin 7, part f j) = Set.univ
  homogeneous : ∀ (j : Fin 7) (a : ℚ), a ≠ 0 → ∀ x : Fin 10 → ℚ,
    a • x ∈ part f j ↔ x ∈ part f j
  layers : ∀ j : Fin 7, j.val < 6 →
    part f j = (MicrolocalPromotedPartition.filtration f j.val \
      MicrolocalPromotedPartition.filtration f (j.val+1)) \ {0}
  origin : part f ⟨6,by decide⟩ = {0}
  uniform_counts : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (j : Fin 7) (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((ConeComponentProgressionCount.points (part f j) u L m b).card : ℝ) ≤
          C*(1+L/(m : ℝ))^(![10,8,7,6,5,1,0] j)
  certificates : PrimeSquarePartitionCertificates.Certificates F f
  local_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
    ∀ v : Fin 10 → ℤ, (fun i => (v i : ZMod p)) ≠ 0 → ∀ j : ℕ,
      ¬ ((j+1 : ℕ) : Dimension) ≤
        IntegralGeometricFiberDepth.geometricFiberDimension f (ZMod p)
          (fun i => (v i : ZMod p)) →
      ‖completeCubicSum F (p^2) v‖ ≤ C*(p : ℝ)^(11+j)

/-- This construction accepts any already selected shared incidence, so
it can be used with the P partition without choosing incompatible data. -/
theorem of_data (lit : FixedFamilyPrimeFieldPointCount.Uniform)
    {t : ℕ} (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (N B : ℕ) (hN : 1 ≤ N) (hB : 1 ≤ B) (hgeo : Geometry F f)
    (h : TenMicrolocalIncidence.Conclusion F f N B) : Conclusion F f N B := by
  refine ⟨hN,hB,hgeo,h,existsUnique_level,union_parts,
    part_smul_mem_iff hgeo,?_,part_six,?_,
    PrimeSquarePartitionCertificates.exists_certificates lit F hF hAn f N B hN hgeo h,
    PrimeSquareMicrolocalBound.exists_off_depth_bound lit hF h⟩
  · intro j hj
    by_cases hj5 : j.val < 5
    · exact part_eq_layer j hj5
    · have he : j=⟨5,by decide⟩ := by
        apply Fin.ext
        change j.val=5
        omega
      subst j
      exact part_five_eq_layer hgeo hF hAn
  · simpa only [exponent_eq_table] using exists_uniform_bound hgeo hF hAn

/-- H14.2's selected numerical endpoint: all seven certificates and
counts are built from the microlocal/model hypotheses and the proved
prime-field count interface. -/
theorem exists_partition
    (microlocal : Literature.ProjectiveMicrolocalCertificate)
    (points : FixedFamilyPrimeFieldPointCount.Uniform)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10) (N B : ℕ),
      Conclusion F f N B := by
  obtain ⟨t,f,N,B,hN,hB,hgeo,h⟩ :=
    TenMicrolocalIncidenceData.exists_data microlocal F hF hAn
  exact ⟨t,f,N,B,of_data points F hF hAn f N B hN hB hgeo h⟩

end CubicTenVariables.MicrolocalSquareRationalPartition
