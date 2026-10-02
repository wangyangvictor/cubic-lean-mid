import HessianTheorem11.SmoothRadialDefect
import HessianTheorem11.RadialLimitKernel

/-! The radial zero-weight limit with a transverse kernel block. Its
transverse columns vanish directly by weight, and invertible transport then
preserves the full actual Hessian kernel. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module NonzeroLimitTransport

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}

theorem SmoothRadialSupportData.minimum_weight
    (E : SmoothRadialSupportData F x T) (j : Fin n)
    (hj : j ∈ E.adapted.tangentIndices ∩ E.adapted.kernelIndices ∨ j = E.adapted.radial)
    (i : Fin n) :
    smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices j ≤
      smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i := by
  rw [E.weight_values j, E.weight_values i]
  simp only [hj, if_true]
  split_ifs <;> norm_num

theorem SmoothRadialSupportData.transverse_limit_column_zero
    (E : SmoothRadialSupportData F x T) (G : MvPolynomial (Fin n) K)
    (hG : G.IsHomogeneous 3)
    (hW : ∀ d ∈ G.support, monomialWeight
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) d = 0)
    (j : Fin n) (hjL : j ∈ E.adapted.kernelIndices) (hjT : j ∉ E.adapted.tangentIndices) :
    (hessian G (Pi.single E.adapted.radial 1)).mulVec (Pi.single j 1) = 0 := by
  classical
  ext i
  rw [Matrix.mulVec_single_one]
  by_contra hne
  have hw := hessian_coordinate_weight G hG _ hW E.adapted.radial i j hne
  have hjr : j ≠ E.adapted.radial := by rintro rfl; exact hjT E.adapted.radial_mem_tangent
  rw [E.weight_values i, E.weight_values j,
    smoothRadialWeight_radial E.adapted.radial_mem_tangent E.adapted.radial_notMem_kernel] at hw
  simp only [Finset.mem_inter, hjT, false_and, hjr, false_or, if_false, hjL, if_true] at hw
  split_ifs at hw <;> omega

/-- The transported limit has exactly the old coordinate kernel, including
the transverse kernel directions that need not be fixed by the unipotent. -/
theorem SmoothRadialSupportData.limit_kernel_iff
    (E : SmoothRadialSupportData F x T) (hF : F.IsHomogeneous 3)
    (U : Matrix (Fin n) (Fin n) K) (hU : Function.Injective U.mulVec)
    (hupper : WeightUpperUnipotent
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) U)
    (htransport : zeroWeightPart (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) =
      PolynomialRestriction.restrict U
        (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)) :
    ∀ v, (hessian (zeroWeightPart (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices))
      (Pi.single E.adapted.radial 1)).mulVec v = 0 ↔
      ∀ i, i ∉ E.adapted.kernelIndices → v i = 0 := by
  classical
  let G := PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F
  let w := smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices
  let H := hessian G (Pi.single E.adapted.radial 1)
  let H0 := hessian (zeroWeightPart G w) (Pi.single E.adapted.radial 1)
  have hrad : U.mulVec (Pi.single E.adapted.radial 1) = Pi.single E.adapted.radial 1 :=
    hupper.fixes_minimum_column _ (E.minimum_weight _ (Or.inr rfl))
  have hcong : H0 = U.transpose * H * U := by
    unfold H0
    rw [show zeroWeightPart G w = PolynomialRestriction.restrict U G from htransport,
      PolynomialRestriction.hessian_restrict, hrad]
  have hcol : ∀ j ∈ E.adapted.kernelIndices, H0.mulVec (Pi.single j 1) = 0 := by
    intro j hj
    by_cases hjT : j ∈ E.adapted.tangentIndices
    · have hfix := hupper.fixes_minimum_column j (E.minimum_weight j
        (Or.inl (Finset.mem_inter.mpr ⟨hjT, hj⟩)))
      rw [hcong, matrix_congruence_kernel_iff U H hU, hfix]
      apply (E.adapted.coordinate_kernel_iff _).mpr
      intro i hi
      have hij : i ≠ j := by rintro rfl; exact hi hj
      simp [hij]
    · exact E.transverse_limit_column_zero (zeroWeightPart G w)
        (zeroWeightPart_homogeneous (PolynomialRestriction.homogeneous_restrict _ F hF) w)
        (zeroWeightPart_weights G w) j hj hjT
  have hle : LinearMap.ker H.mulVecLin ≤ LinearMap.ker H0.mulVecLin := by
    intro v hv
    have hc := (E.adapted.coordinate_kernel_iff v).mp hv
    have he : v = ∑ j, v j • (Pi.single j (1 : K) : Fin n → K) := by
      ext i
      simp [Pi.single_apply]
    change H0.mulVec v = 0
    rw [he, Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.mulVec_smul]
    by_cases hj : j ∈ E.adapted.kernelIndices
    · rw [hcol j hj, smul_zero]
    · rw [hc j hj, zero_smul]
  have hu : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hU)
  have hr : H0.rank = H.rank := by
    rw [hcong, Matrix.rank_mul_eq_left_of_isUnit_det U _ hu]
    exact Matrix.rank_mul_eq_right_of_isUnit_det U.transpose H (by rwa [Matrix.det_transpose])
  have hd : finrank K (LinearMap.ker H.mulVecLin) = finrank K (LinearMap.ker H0.mulVecLin) := by
    have h1 := H.mulVecLin.finrank_range_add_finrank_ker
    have h2 := H0.mulVecLin.finrank_range_add_finrank_ker
    change H.rank + _ = _ at h1
    change H0.rank + _ = _ at h2
    rw [hr] at h2
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle hd
  intro v
  change v ∈ LinearMap.ker H0.mulVecLin ↔ _
  rw [← heq]
  exact E.adapted.coordinate_kernel_iff v

/-- A radial limit with the preserved kernel has exactly one normal
coordinate outside the union of tangent and kernel indices. -/
theorem SmoothRadialSupportData.normal_card_eq_one_of_limit_kernel
    (E : SmoothRadialSupportData F x T) (G : MvPolynomial (Fin n) K)
    (hG : G.IsHomogeneous 3)
    (hW : ∀ d ∈ G.support, monomialWeight
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) d = 0)
    (hker : ∀ v, (hessian G (Pi.single E.adapted.radial 1)).mulVec v = 0 ↔
      ∀ i, i ∉ E.adapted.kernelIndices → v i = 0) :
    (Finset.univ \ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices)).card = 1 := by
  classical
  have hle : (Finset.univ \ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices)).card ≤ 1 := by
    apply normal_columns_card_le_one (hessian G (Pi.single E.adapted.radial 1))
      (E.adapted.tangentIndices ∪ E.adapted.kernelIndices) E.adapted.kernelIndices
      E.adapted.radial Finset.subset_union_right (fun v => (hker v).mp)
    intro i j hj hir
    have hjT : j ∉ E.adapted.tangentIndices := fun h => hj (Finset.mem_union_left _ h)
    have hjL : j ∉ E.adapted.kernelIndices := fun h => hj (Finset.mem_union_right _ h)
    by_cases hiL : i ∈ E.adapted.kernelIndices
    · have hcol : (hessian G (Pi.single E.adapted.radial 1)).mulVec (Pi.single i 1) = 0 := by
        apply (hker _).mpr
        intro l hl
        have hli : l ≠ i := by rintro rfl; exact hl hiL
        simp [hli]
      have hh := congrFun hcol j
      rw [Matrix.mulVec_single_one] at hh
      have hs := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j)
        (hessian_symmetric G (Pi.single E.adapted.radial 1))
      exact hs.symm.trans hh
    · by_contra hne
      have hw := hessian_coordinate_weight G hG _ hW E.adapted.radial i j hne
      have hjr : j ≠ E.adapted.radial := by rintro rfl; exact hjT E.adapted.radial_mem_tangent
      rw [E.weight_values i, E.weight_values j,
        smoothRadialWeight_radial E.adapted.radial_mem_tangent E.adapted.radial_notMem_kernel] at hw
      by_cases hiT : i ∈ E.adapted.tangentIndices <;>
        simp [hiL, hiT, hjL, hjT, hir, hjr] at hw
  have hpositive : 0 < (Finset.univ \
      (E.adapted.tangentIndices ∪ E.adapted.kernelIndices)).card := by
    by_contra hn
    have hempty : Finset.univ \ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    have hall : ∀ i : Fin n, i ∈ E.adapted.tangentIndices ∪ E.adapted.kernelIndices :=
      fun i => Finset.sdiff_eq_empty_iff_subset.mp hempty (Finset.mem_univ i)
    have hz : (hessian G (Pi.single E.adapted.radial 1)).mulVec
        (Pi.single E.adapted.radial 1) = 0 := by
      ext i
      rw [Matrix.mulVec_single_one]
      by_contra hne
      have hw := hessian_coordinate_weight G hG _ hW E.adapted.radial i E.adapted.radial hne
      rw [E.weight_values i,
        smoothRadialWeight_radial E.adapted.radial_mem_tangent E.adapted.radial_notMem_kernel] at hw
      rcases Finset.mem_union.mp (hall i) with hiT | hiL
      · by_cases hiL : i ∈ E.adapted.kernelIndices <;>
          by_cases hir : i = E.adapted.radial <;> simp_all
      · by_cases hiT : i ∈ E.adapted.tangentIndices <;>
          by_cases hir : i = E.adapted.radial <;> simp_all
    have hbad := (hker _).mp hz E.adapted.radial E.adapted.radial_notMem_kernel
    simpa using hbad
  omega

theorem SmoothRadialSupportData.normal_card_eq_one_of_unipotent_transport
    (E : SmoothRadialSupportData F x T) (hF : F.IsHomogeneous 3)
    (U : Matrix (Fin n) (Fin n) K) (hU : Function.Injective U.mulVec)
    (hupper : WeightUpperUnipotent
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) U)
    (htransport : zeroWeightPart (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices) =
      PolynomialRestriction.restrict U
        (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)) :
    (Finset.univ \ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices)).card = 1 := by
  apply E.normal_card_eq_one_of_limit_kernel
    (zeroWeightPart (PolynomialRestriction.restrict (basisMatrix E.adapted.basis) F)
      (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices))
    (zeroWeightPart_homogeneous (PolynomialRestriction.homogeneous_restrict _ F hF) _)
    (zeroWeightPart_weights _ _)
  exact E.limit_kernel_iff hF U hU hupper htransport

/-- The geometric transport theorem applies whenever the retained radial
weight has sum zero. -/
theorem SmoothRadialSupportData.normal_card_eq_one
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    {n : ℕ} (F : AnisotropicCubic n) (hn : 0 < n)
    {x : GeometricPoint n} {T : Submodule GeometricField (GeometricPoint n)}
    (E : SmoothRadialSupportData (geometricPolynomial F.polynomial) x T)
    (hsum : ∑ i, smoothRadialWeight E.adapted.radial
      E.adapted.tangentIndices E.adapted.kernelIndices i = 0) :
    (Finset.univ \ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices)).card = 1 := by
  obtain ⟨U, hdet, hupper, htransport⟩ := anisotropic_zeroWeightPart_transport
    boundary bigCell F hn (basisMatrix E.adapted.basis) (basisMatrix_injective E.adapted.basis)
    (smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices)
    hsum E.support_nonnegative
  exact E.normal_card_eq_one_of_unipotent_transport (geometric_homogeneous F.homogeneous)
    U (injective_of_det_one U hdet) hupper htransport

/-- The exceptional thirteen-variable radial limit has the exact block
sizes used in the twelve-variable reduction. -/
theorem SmoothRadialSupportData.thirteen_defect_one_dimensions
    (boundary : NonzeroLimitTransport.RationalRelativeBoundaryInput)
    (bigCell : NonzeroLimitTransport.TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13)
    {x : GeometricPoint 13} {T : Submodule GeometricField (GeometricPoint 13)}
    (E : SmoothRadialSupportData (geometricPolynomial F.polynomial) x T)
    (he : (finrank GeometricField T : ℤ) -
      ((hessian (geometricPolynomial F.polynomial) x).rank : ℤ) = 3)
    (hc : E.defect = 1) :
    finrank GeometricField T = 11 ∧
      (hessian (geometricPolynomial F.polynomial) x).rank = 8 ∧
      finrank GeometricField (LinearMap.ker
        (hessian (geometricPolynomial F.polynomial) x).mulVecLin) = 5 := by
  classical
  have hsum := (E.defect_le_one_of_thirteen he).2
  rw [hc] at hsum
  norm_num at hsum
  have hnormal := E.normal_card_eq_one boundary bigCell F (by decide) hsum
  have hu := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (E.adapted.tangentIndices ∪ E.adapted.kernelIndices))
  rw [Finset.card_univ, Fintype.card_fin, hnormal] at hu
  have hunion : (E.adapted.tangentIndices ∪ E.adapted.kernelIndices).card =
      E.adapted.tangentIndices.card + E.defect := by
    have h := Finset.card_sdiff_add_card E.adapted.kernelIndices E.adapted.tangentIndices
    rw [Finset.union_comm] at h
    unfold defect
    omega
  rw [hunion, E.adapted.tangent_card, hc] at hu
  have hr := (hessian (geometricPolynomial F.polynomial) x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian (geometricPolynomial F.polynomial) x).rank + _ = _ at hr
  rw [show finrank GeometricField (GeometricPoint 13) = 13 by simp] at hr
  have ht : finrank GeometricField T = 11 :=
    Nat.add_right_cancel (show finrank GeometricField T + 1 = 11 + 1 from
      Nat.add_left_cancel hu)
  rw [ht] at he
  norm_num at he
  have hrank : (hessian (geometricPolynomial F.polynomial) x).rank = 8 := by omega
  exact ⟨ht, hrank, by omega⟩

end HessianTheorem11
