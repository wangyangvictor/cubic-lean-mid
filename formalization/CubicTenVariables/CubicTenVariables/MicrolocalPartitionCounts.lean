import CubicTenVariables.MicrolocalPromotionCover
import CubicTenVariables.MicrolocalPromotionTable
import CubicTenVariables.TenMicrolocalIncidenceData
import CubicTenVariables.AmbientProgressionCount
import CubicTenVariables.HomogeneousPromotionScaling

/-! Assembly of the four componentwise promotion sets into one rational
frequency partition. These are the opens needed for the numerical route;
no global smoothness or lisse-sheaf structure is asserted. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalPartitionCounts
open MvPolynomial HessianTheorem11 TranslatedDepthSeven
open ProjectiveMicrolocalData ProjectiveMicrolocalModels RationalConeClosure
open MicrolocalPromotedPartition ConeComponentProgressionCount
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Four positive-level promotion sets, with the required empty boundaries. -/
def promotionFamily (O : Fin 4 → Set (Fin 10 → ℚ)) (j : ℕ) : Set (Fin 10 → ℚ) :=
  if hj : 1 ≤ j ∧ j ≤ 4 then O ⟨j-1,by omega⟩ else ∅

@[simp] theorem promotionFamily_zero (O : Fin 4 → Set (Fin 10 → ℚ)) :
    promotionFamily O 0 = ∅ := by simp [promotionFamily]

@[simp] theorem promotionFamily_five (O : Fin 4 → Set (Fin 10 → ℚ)) :
    promotionFamily O 5 = ∅ := by simp [promotionFamily]

theorem promotionFamily_level (O : Fin 4 → Set (Fin 10 → ℚ)) (i : Fin 4) :
    promotionFamily O (i.val+1) = O i := by
  rw [promotionFamily,dif_pos (by omega : 1 ≤ i.val+1 ∧ i.val+1 ≤ 4)]
  congr 1

theorem promotionFamily_compatible {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (O : Fin 4 → Set (Fin 10 → ℚ))
    (hO : ∀ i, O i ⊆ PromotedFrequencyPartition.layer (filtration f) (i.val+1)) :
    Compatible f (promotionFamily O) := by
  refine ⟨promotionFamily_zero O,promotionFamily_five O,?_⟩
  intro j hj
  by_cases hpos : 1 ≤ j ∧ j ≤ 4
  · let i : Fin 4 := ⟨j-1,by omega⟩
    have hi : i.val+1 = j := by dsimp [i]; omega
    rw [← hi,promotionFamily_level]
    exact hO i
  · rw [promotionFamily,dif_neg hpos]
    exact Set.empty_subset _

/-- The selected progression estimates on all six levels of the same partition.
The fractional refinements at levels one and two are not asserted. -/
structure Counts {t : ℕ} (f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10)
    (U : ℕ → Set (Fin 10 → ℚ)) : Prop where
  ambient : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f U ⟨0,by decide⟩) u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^10
  low : ∀ j : Fin 6, (j.val = 1 ∨ j.val = 2) →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^(9-j.val)
  high : ∀ j : Fin 6, (j.val = 3 ∨ j.val = 4) → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(8-j.val)
  terminal : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
    ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((points (part f U ⟨5,by decide⟩) u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))

/-- Feed the actual component table to the finite-cover counting theorem. -/
theorem table_part_bound {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (lit : Published.Salberger2023Theorem04) (hgeo : Geometry F f)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (j : Fin 6) (hj : j.val=3 ∨ j.val=4)
    (T : MicrolocalPromotionTable.Table F f j.val)
    (U : ℕ → Set (Fin 10 → ℚ)) (hU : Compatible f U) (hopen : U j.val = T.open)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(8-j.val) :=
  MicrolocalPromotionCover.exists_part_bound lit hgeo hAn j hj
    (fun i => PolynomialExponentialFamily.baseIdeal (T.G i)) T.prime T.homogeneous
    T.cover_point (fun i => map (Int.castRingHom ℚ) (T.h i))
    (T.cases_for_high_levels hj) U hU hopen ε hε

/-- The constructed numerical partition retains the homogeneity needed
when a conductor argument divides a frequency by an integer. -/
theorem part_smul_mem_iff {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    (hgeo : Geometry F f)
    (T : ∀ i : Fin 4, MicrolocalPromotionTable.Table F f (i.val+1))
    (j : Fin 6) (a : ℚ) (ha : a ≠ 0) (x : Fin 10 → ℚ) :
    a • x ∈ part f (promotionFamily (fun i => (T i).open)) j ↔
      x ∈ part f (promotionFamily (fun i => (T i).open)) j := by
  apply HomogeneousPromotionScaling.part_smul_mem_iff hgeo _ ?_ j a ha x
  intro k b hb y hy
  unfold promotionFamily at hy ⊢
  split_ifs with hk
  · rw [dif_pos hk] at hy
    let i : Fin 4 := ⟨k-1,by omega⟩
    change y ∈ (T i).open at hy
    change b • y ∈ (T i).open
    exact (HomogeneousPromotionScaling.promotionOpen_smul_mem_iff
      (fun a => PolynomialExponentialFamily.baseIdeal ((T i).G a))
      (T i).homogeneous (fun a => map (Int.castRingHom ℚ) ((T i).h a)) (T i).e
      (fun a => ((T i).choice a).homogeneous.map _) b hb y).mpr hy
  · rw [dif_neg hk] at hy
    exact False.elim hy

/-- Construct all four tables from the actual exceptional loci, and prove
all selected progression counts on their single partition. -/
theorem exists_partition_counts {t : ℕ} {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10} {N : ℕ}
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (lit : Published.Salberger2023Theorem04)
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
      exact table_part_bound lit hgeo hAn ⟨3,by decide⟩ (Or.inl rfl) (T 2) U hU
        (promotionFamily_level O 2) ε hε
    · have he : j = (⟨4,by decide⟩ : Fin 6) := Fin.ext hj
      subst j
      exact table_part_bound lit hgeo hAn ⟨4,by decide⟩ (Or.inr rfl) (T 3) U hU
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
    (lit : Published.Salberger2023Theorem04)
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
    lit hgeo hF hAn hdata.depth_models
  exact ⟨t,f,N,B,T,hN,hB,hgeo,hdata,hU,hcount,hunique⟩

end CubicTenVariables.MicrolocalPartitionCounts
