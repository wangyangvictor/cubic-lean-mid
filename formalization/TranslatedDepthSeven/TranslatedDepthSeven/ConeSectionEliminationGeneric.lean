import TranslatedDepthSeven.RankSevenNonvertexProjectionInternal

/-!
# Four-row elimination for a translated cone over an arbitrary field

The earlier rank-seven implementation of this calculation used thirteen
spatial variables over `ℚ`.  The quotient construction uses twelve spatial
variables over `Qbar`.  This file records the underlying calculation once,
with the field and the number of spatial variables arbitrary.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 400000

universe u

variable {K : Type u} [Field K]

/-- Spatial coefficients of a four-row homogeneous section. -/
def coneSectionSpatialMatrix {N : ℕ}
    (A : Matrix (Fin 4) (Option (Fin N)) K) :
    Matrix (Fin 4) (Fin N) K :=
  fun i j ↦ A i (some j)

/-- Evaluation of the four rows at the translated vertex `(m,-b)`. -/
def coneSectionVertexEvaluation {N : ℕ}
    (A : Matrix (Fin 4) (Option (Fin N)) K)
    (b : Fin N → K) (m : K) : Fin 4 → K :=
  fun i ↦ m * A i none - ∑ j, A i (some j) * b j

theorem coneSectionVertexEvaluation_eq_mulVec {N : ℕ}
    (A : Matrix (Fin 4) (Option (Fin N)) K)
    (b : Fin N → K) (m : K) :
    coneSectionVertexEvaluation A b m =
      Matrix.mulVec A (fun j ↦ j.elim m (fun i ↦ -b i)) := by
  funext i
  simp [coneSectionVertexEvaluation, Matrix.mulVec, dotProduct]
  ring

/-- Scaling every spatial row by the same nonzero scalar does not change
the generated row ideal. -/
theorem indexedRowIdeal_vertexContainedBase_eq_spatial {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) :
    indexedMatrixRowLinearIdeal (vertexContainedBaseMatrix b m A) =
      indexedMatrixRowLinearIdeal (coneSectionSpatialMatrix A) := by
  have hrow : ∀ i : Fin 4,
      indexedMatrixRowLinearPolynomial (vertexContainedBaseMatrix b m A) i =
        MvPolynomial.C m⁻¹ *
          indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i := by
    intro i
    unfold indexedMatrixRowLinearPolynomial vertexContainedBaseMatrix
      coneSectionSpatialMatrix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    ring
  apply le_antisymm
  · rw [indexedMatrixRowLinearIdeal]
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    rw [hrow]
    exact (indexedMatrixRowLinearIdeal
      (coneSectionSpatialMatrix A)).mul_mem_left _
      (Ideal.subset_span (Set.mem_range_self i))
  · rw [indexedMatrixRowLinearIdeal]
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    have hscaled := (indexedMatrixRowLinearIdeal
      (vertexContainedBaseMatrix b m A)).mul_mem_left
        (MvPolynomial.C m)
        (Ideal.subset_span (Set.mem_range_self i))
    rw [hrow, ← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hm,
      map_one, one_mul] at hscaled
    exact hscaled

/-- The three alternating spatial rows obtained from a nonzero pivot. -/
def coneSectionThreeEquationMatrix {N : ℕ}
    (A : Matrix (Fin 4) (Option (Fin N)) K)
    (b : Fin N → K) (m : K) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin N) K :=
  fun k j ↦
    coneSectionVertexEvaluation A b m i₀ *
        coneSectionSpatialMatrix A (finThreeEquivNonpivotRow i₀ k) j -
      coneSectionVertexEvaluation A b m (finThreeEquivNonpivotRow i₀ k) *
        coneSectionSpatialMatrix A i₀ j

/-- The linear form substituted for the distinguished cone coordinate. -/
def genericConePivotEliminationForm {N : ℕ}
    (b : Fin N → K) (m : K)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4) :
    MvPolynomial (Fin N) K :=
  -MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹ *
    indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀

theorem genericConePivotEliminationForm_isHomogeneous {N : ℕ}
    (b : Fin N → K) (m : K)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4) :
    (genericConePivotEliminationForm b m A i₀).IsHomogeneous 1 := by
  unfold genericConePivotEliminationForm
  rw [← map_neg]
  exact (indexedMatrixRowLinearPolynomial_isHomogeneous
    (coneSectionSpatialMatrix A) i₀).C_mul _

/-- Formula for a transformed row after eliminating the cone coordinate. -/
theorem generic_optionLinearElimination_transformedRow_apply {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ i : Fin 4) :
    optionLinearEliminationAlgHom
        (genericConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A) i) =
      MvPolynomial.C (m⁻¹ * coneSectionVertexEvaluation A b m i) *
          genericConePivotEliminationForm b m A i₀ +
        MvPolynomial.C m⁻¹ *
          indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i := by
  classical
  unfold indexedMatrixRowLinearPolynomial
    translatedConeCoordinateSectionMatrix coneSectionVertexEvaluation
    coneSectionSpatialMatrix
  rw [Fintype.sum_option]
  simp only [optionLinearEliminationAlgHom_X_none,
    optionLinearEliminationAlgHom_X_some, map_add, map_mul, map_sum,
    optionLinearEliminationAlgHom_C]
  simp only [← MvPolynomial.C_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_mul]
  ring

/-- The displayed alternating row is the corresponding polynomial
alternating combination. -/
theorem generic_indexedRowPolynomial_threeEquation {N : ℕ}
    (b : Fin N → K) (m : K)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (k : Fin 3) :
    indexedMatrixRowLinearPolynomial
        (coneSectionThreeEquationMatrix A b m i₀) k =
      MvPolynomial.C (coneSectionVertexEvaluation A b m i₀) *
          indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A)
            (finThreeEquivNonpivotRow i₀ k) -
        MvPolynomial.C (coneSectionVertexEvaluation A b m
            (finThreeEquivNonpivotRow i₀ k)) *
          indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀ := by
  classical
  unfold indexedMatrixRowLinearPolynomial coneSectionThreeEquationMatrix
    coneSectionSpatialMatrix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_sub, map_mul, map_mul]
  ring

theorem generic_optionLinearElimination_pivotRow {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0) :
    optionLinearEliminationAlgHom
        (genericConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A) i₀) = 0 := by
  rw [generic_optionLinearElimination_transformedRow_apply b m hm A i₀ i₀]
  unfold genericConePivotEliminationForm
  rw [map_mul]
  have hcancel :
      MvPolynomial.C (coneSectionVertexEvaluation A b m i₀) *
          MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹ =
        (1 : MvPolynomial (Fin N) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpivot, map_one]
  calc
    MvPolynomial.C m⁻¹ *
          MvPolynomial.C (coneSectionVertexEvaluation A b m i₀) *
          (-MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹ *
            indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀) +
        MvPolynomial.C m⁻¹ *
          indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀ =
        MvPolynomial.C m⁻¹ *
          (-(MvPolynomial.C (coneSectionVertexEvaluation A b m i₀) *
              MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹) *
            indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀ +
            indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀) := by ring
    _ = 0 := by rw [hcancel]; ring

theorem generic_optionLinearElimination_nonpivotRow {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0)
    (k : Fin 3) :
    optionLinearEliminationAlgHom
        (genericConePivotEliminationForm b m A i₀)
        (indexedMatrixRowLinearPolynomial
          (translatedConeCoordinateSectionMatrix b m A)
          (finThreeEquivNonpivotRow i₀ k)) =
      MvPolynomial.C
          (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
        indexedMatrixRowLinearPolynomial
          (coneSectionThreeEquationMatrix A b m i₀) k := by
  rw [generic_optionLinearElimination_transformedRow_apply b m hm A i₀
    (finThreeEquivNonpivotRow i₀ k)]
  rw [generic_indexedRowPolynomial_threeEquation]
  unfold genericConePivotEliminationForm
  rw [map_mul, map_mul]
  have hcancel :
      MvPolynomial.C (coneSectionVertexEvaluation A b m i₀) *
          MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹ =
        (1 : MvPolynomial (Fin N) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpivot, map_one]
  let R₀ := indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀
  let i := (finThreeEquivNonpivotRow i₀ k : Fin 4)
  let R := indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i
  let a : MvPolynomial (Fin N) K := MvPolynomial.C m⁻¹
  let c : MvPolynomial (Fin N) K :=
    MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)⁻¹
  let f : MvPolynomial (Fin N) K :=
    MvPolynomial.C (coneSectionVertexEvaluation A b m i₀)
  let d : MvPolynomial (Fin N) K :=
    MvPolynomial.C (coneSectionVertexEvaluation A b m i)
  have hcf : c * f = 1 := by
    simpa only [c, f, mul_comm] using hcancel
  change a * d * (-c * R₀) + a * R = a * c * (f * R - d * R₀)
  calc
    a * d * (-c * R₀) + a * R =
        a * c * (f * R - d * R₀) + a * (1 - c * f) * R := by ring
    _ = a * c * (f * R - d * R₀) := by rw [hcf]; ring

/-- Exact image of the transformed four-row ideal under elimination. -/
theorem generic_map_transformedRowIdeal_elimination {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0) :
    (indexedMatrixRowLinearIdeal
        (translatedConeCoordinateSectionMatrix b m A)).map
        (optionLinearEliminationAlgHom
          (genericConePivotEliminationForm b m A i₀)) =
      indexedMatrixRowLinearIdeal
        (coneSectionThreeEquationMatrix A b m i₀) := by
  let l := genericConePivotEliminationForm b m A i₀
  let e := optionLinearEliminationAlgHom l
  let B := translatedConeCoordinateSectionMatrix b m A
  let D := coneSectionThreeEquationMatrix A b m i₀
  apply le_antisymm
  · rw [indexedMatrixRowLinearIdeal, Ideal.map_span]
    apply Ideal.span_le.2
    rintro f ⟨g, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i = i₀
    · subst i
      rw [show e (indexedMatrixRowLinearPolynomial B i₀) = 0 by
        exact generic_optionLinearElimination_pivotRow b m hm A i₀ hpivot]
      exact Ideal.zero_mem _
    · let k : Fin 3 := (finThreeEquivNonpivotRow i₀).symm ⟨i, hi⟩
      have hki : (finThreeEquivNonpivotRow i₀ k : Fin 4) = i := by
        exact congrArg Subtype.val
          ((finThreeEquivNonpivotRow i₀).apply_symm_apply ⟨i, hi⟩)
      have hrow : e (indexedMatrixRowLinearPolynomial B i) =
          MvPolynomial.C
              (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
            indexedMatrixRowLinearPolynomial D k := by
        simpa only [e, l, B, D, hki] using
          generic_optionLinearElimination_nonpivotRow b m hm A i₀ hpivot k
      rw [hrow]
      exact (indexedMatrixRowLinearIdeal D).mul_mem_left _
        (Ideal.subset_span ⟨k, rfl⟩)
  · rw [indexedMatrixRowLinearIdeal]
    apply Ideal.span_le.2
    rintro f ⟨k, rfl⟩
    let i : Fin 4 := finThreeEquivNonpivotRow i₀ k
    have hrow : e (indexedMatrixRowLinearPolynomial B i) =
        MvPolynomial.C
            (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
          indexedMatrixRowLinearPolynomial D k := by
      exact generic_optionLinearElimination_nonpivotRow b m hm A i₀ hpivot k
    have hsource : indexedMatrixRowLinearPolynomial B i ∈
        indexedMatrixRowLinearIdeal B := Ideal.subset_span ⟨i, rfl⟩
    have hscaled :
        MvPolynomial.C
            (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
          indexedMatrixRowLinearPolynomial D k ∈
        (indexedMatrixRowLinearIdeal B).map e := by
      rw [← hrow]
      exact Ideal.mem_map_of_mem e hsource
    have hscalar :
        (m * coneSectionVertexEvaluation A b m i₀) *
            (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) = 1 := by
      field_simp [hm, hpivot]
    have heq :
        MvPolynomial.C (m * coneSectionVertexEvaluation A b m i₀) *
            (MvPolynomial.C
                (m⁻¹ * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
              indexedMatrixRowLinearPolynomial D k) =
          indexedMatrixRowLinearPolynomial D k := by
      rw [← mul_assoc, ← map_mul, hscalar, map_one, one_mul]
    rw [← heq]
    exact ((indexedMatrixRowLinearIdeal B).map e).mul_mem_left _ hscaled

/-- The pivot row is a unit multiple of the kernel generator. -/
theorem generic_transformedPivotRow_eq_kernelGenerator {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0) :
    indexedMatrixRowLinearPolynomial
        (translatedConeCoordinateSectionMatrix b m A) i₀ =
      MvPolynomial.C (m⁻¹ * coneSectionVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some
          (genericConePivotEliminationForm b m A i₀)) := by
  classical
  let β := coneSectionVertexEvaluation A b m i₀
  let R := indexedMatrixRowLinearPolynomial (coneSectionSpatialMatrix A) i₀
  have hβ : β ≠ 0 := hpivot
  have hnone : translatedConeCoordinateSectionMatrix b m A i₀ none =
      m⁻¹ * β := by rfl
  have hsome (j : Fin N) :
      translatedConeCoordinateSectionMatrix b m A i₀ (some j) =
        m⁻¹ * coneSectionSpatialMatrix A i₀ j := by rfl
  have hrename : MvPolynomial.rename some R =
      ∑ j, MvPolynomial.C (coneSectionSpatialMatrix A i₀ j) *
        MvPolynomial.X (some j) := by
    unfold R indexedMatrixRowLinearPolynomial
    simp only [map_sum, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
  have hsum :
      (∑ j, MvPolynomial.C (m⁻¹ * coneSectionSpatialMatrix A i₀ j) *
          MvPolynomial.X (some j)) =
        MvPolynomial.C m⁻¹ * MvPolynomial.rename some R := by
    rw [hrename, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    ring
  have hcancel :
      MvPolynomial.C (m⁻¹ * β) * MvPolynomial.C β⁻¹ =
        (MvPolynomial.C m⁻¹ : MvPolynomial (Option (Fin N)) K) := by
    rw [← map_mul]
    congr 1
    field_simp [hm, hβ]
  unfold indexedMatrixRowLinearPolynomial
  rw [Fintype.sum_option, hnone]
  simp_rw [hsome]
  rw [hsum]
  unfold genericConePivotEliminationForm
  change MvPolynomial.C (m⁻¹ * β) * MvPolynomial.X none +
      MvPolynomial.C m⁻¹ * MvPolynomial.rename some R =
    MvPolynomial.C (m⁻¹ * β) *
      (MvPolynomial.X none - MvPolynomial.rename some
        (-MvPolynomial.C β⁻¹ * R))
  simp only [map_neg, map_mul, MvPolynomial.rename_C]
  have hcancel' :
      MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.C β⁻¹ =
        (MvPolynomial.C m⁻¹ : MvPolynomial (Option (Fin N)) K) := by
    rw [← map_mul]
    exact hcancel
  calc
    MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.X none +
        MvPolynomial.C m⁻¹ * MvPolynomial.rename some R =
      MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.X none +
        (MvPolynomial.C m⁻¹ * MvPolynomial.C β * MvPolynomial.C β⁻¹) *
          MvPolynomial.rename some R := by rw [hcancel']
    _ = MvPolynomial.C m⁻¹ * MvPolynomial.C β *
        (MvPolynomial.X none -
          (-MvPolynomial.C β⁻¹ * MvPolynomial.rename some R)) := by ring

theorem generic_ker_elimination_le_transformedRowIdeal {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0) :
    RingHom.ker (optionLinearEliminationAlgHom
        (genericConePivotEliminationForm b m A i₀)) ≤
      indexedMatrixRowLinearIdeal
        (translatedConeCoordinateSectionMatrix b m A) := by
  rw [ker_optionLinearEliminationAlgHom]
  apply Ideal.span_le.2
  rintro f rfl
  let B := translatedConeCoordinateSectionMatrix b m A
  let l := genericConePivotEliminationForm b m A i₀
  have hrow : indexedMatrixRowLinearPolynomial B i₀ =
      MvPolynomial.C (m⁻¹ * coneSectionVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some l) :=
    generic_transformedPivotRow_eq_kernelGenerator b m hm A i₀ hpivot
  have hscaled :
      MvPolynomial.C (m⁻¹ * coneSectionVertexEvaluation A b m i₀) *
        (MvPolynomial.X none - MvPolynomial.rename some l) ∈
      indexedMatrixRowLinearIdeal B := by
    rw [← hrow]
    exact Ideal.subset_span ⟨i₀, rfl⟩
  have hscalar :
      (m * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
          (m⁻¹ * coneSectionVertexEvaluation A b m i₀) = 1 := by
    field_simp [hm, hpivot]
  have heq :
      MvPolynomial.C (m * (coneSectionVertexEvaluation A b m i₀)⁻¹) *
          (MvPolynomial.C
              (m⁻¹ * coneSectionVertexEvaluation A b m i₀) *
            (MvPolynomial.X none - MvPolynomial.rename some l)) =
        MvPolynomial.X none - MvPolynomial.rename some l := by
    rw [← mul_assoc, ← map_mul, hscalar, map_one, one_mul]
  rw [← heq]
  exact (indexedMatrixRowLinearIdeal B).mul_mem_left _ hscaled

theorem generic_map_projectiveCone_elimination {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (l : MvPolynomial (Fin N) K) :
    (projectiveConeIdealExtension J).map
        (optionLinearEliminationAlgHom l) = J := by
  unfold projectiveConeIdealExtension
  have hcomp :
      (optionLinearEliminationAlgHom l).toRingHom.comp
          (MvPolynomial.rename some).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  calc
    (J.map (MvPolynomial.rename some)).map
        (optionLinearEliminationAlgHom l) =
      J.map ((optionLinearEliminationAlgHom l).toRingHom.comp
        (MvPolynomial.rename some).toRingHom) :=
      J.map_map (MvPolynomial.rename some).toRingHom
        (optionLinearEliminationAlgHom l).toRingHom
    _ = J.map (RingHom.id _) := by rw [hcomp]
    _ = J := Ideal.map_id J

/-- The coordinate-cone section is exactly the inverse image of the
three-row base section under a split homogeneous quotient map. -/
theorem generic_coordinateConeSupRows_eq_comap_elimination {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation A b m i₀ ≠ 0) :
    projectiveConeIdealExtension J ⊔
        indexedMatrixRowLinearIdeal
          (translatedConeCoordinateSectionMatrix b m A) =
      (J ⊔ indexedMatrixRowLinearIdeal
          (coneSectionThreeEquationMatrix A b m i₀)).comap
        (optionLinearEliminationAlgHom
          (genericConePivotEliminationForm b m A i₀)) := by
  let l := genericConePivotEliminationForm b m A i₀
  let e := optionLinearEliminationAlgHom l
  let H := projectiveConeIdealExtension J ⊔
    indexedMatrixRowLinearIdeal
      (translatedConeCoordinateSectionMatrix b m A)
  let Q := J ⊔ indexedMatrixRowLinearIdeal
    (coneSectionThreeEquationMatrix A b m i₀)
  have hmap : H.map e = Q := by
    rw [Ideal.map_sup, generic_map_projectiveCone_elimination,
      generic_map_transformedRowIdeal_elimination b m hm A i₀ hpivot]
  change H = Q.comap e
  rw [← hmap, Ideal.comap_map_of_surjective e
    (optionLinearEliminationAlgHom_surjective l)]
  rw [← RingHom.ker_eq_comap_bot]
  symm
  apply sup_eq_left.mpr
  exact (generic_ker_elimination_le_transformedRowIdeal
    b m hm A i₀ hpivot).trans le_sup_right

/-- The split quotient map in the original consecutive coordinates. -/
def genericNonvertexProjectionQuotientAlgHom {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4) :
    MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin N) K :=
  (optionLinearEliminationAlgHom
    (genericConePivotEliminationForm b m A i₀)).comp
      ((MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)).trans
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm).toAlgHom

/-- A homogeneous right inverse to the quotient map. -/
def genericNonvertexProjectionQuotientSection {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin (N + 1)) K :=
  (((MvPolynomial.renameEquiv K (_root_.finSuccEquiv N)).trans
      (homogeneousAffinePolynomialChangeAlgEquiv b m hm).symm).symm).toAlgHom.comp
    (MvPolynomial.rename some)

theorem genericNonvertexProjectionQuotient_rightInverse {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4) :
    (genericNonvertexProjectionQuotientAlgHom b m hm A i₀).comp
        (genericNonvertexProjectionQuotientSection b m hm) =
      AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [genericNonvertexProjectionQuotientAlgHom,
    genericNonvertexProjectionQuotientSection]
  have hcancel : (MvPolynomial.C m : MvPolynomial (Fin N) K) *
      MvPolynomial.C m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hm, map_one]
  rw [← mul_assoc, hcancel, one_mul]
  ring

theorem genericNonvertexProjectionQuotient_surjective {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4) :
    Function.Surjective
      (genericNonvertexProjectionQuotientAlgHom b m hm A i₀) := by
  intro f
  refine ⟨genericNonvertexProjectionQuotientSection b m hm f, ?_⟩
  exact DFunLike.congr_fun
    (genericNonvertexProjectionQuotient_rightInverse b m hm A i₀) f

theorem genericNonvertexProjectionQuotient_isHomogeneous {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Option (Fin N)) K) (i₀ : Fin 4)
    (d : ℕ) (f : MvPolynomial (Fin (N + 1)) K)
    (hf : f.IsHomogeneous d) :
    (genericNonvertexProjectionQuotientAlgHom b m hm A i₀ f).IsHomogeneous d := by
  apply optionLinearEliminationAlgHom_isHomogeneous
    (genericConePivotEliminationForm b m A i₀)
    (genericConePivotEliminationForm_isHomogeneous b m A i₀)
  apply isHomogeneous_homogeneousAffinePolynomialChange_symm b m hm
  exact hf.rename_isHomogeneous

theorem genericNonvertexProjectionQuotientSection_isHomogeneous {N : ℕ}
    (b : Fin N → K) (m : K) (hm : m ≠ 0)
    (d : ℕ) (f : MvPolynomial (Fin N) K)
    (hf : f.IsHomogeneous d) :
    (genericNonvertexProjectionQuotientSection b m hm f).IsHomogeneous d := by
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  apply isHomogeneous_homogeneousAffinePolynomialChange b m hm
  exact hf.rename_isHomogeneous

/-- On the standard affine chart, the homogeneous section of the quotient
map evaluates at the translated spatial point `b+m*w`. -/
theorem eval_genericNonvertexProjectionQuotientSection_affine {N : ℕ}
    (b w : Fin N → K) (m : K) (hm : m ≠ 0)
    (q : MvPolynomial (Fin N) K) :
    MvPolynomial.eval (Fin.cons 1 w)
        (genericNonvertexProjectionQuotientSection b m hm q) =
      MvPolynomial.eval (fun j ↦ b j + m * w j) q := by
  unfold genericNonvertexProjectionQuotientSection
  change MvPolynomial.eval (Fin.cons 1 w)
      (MvPolynomial.rename (_root_.finSuccEquiv N).symm
        (homogeneousAffinePolynomialChangeAlgEquiv b m hm
          (MvPolynomial.rename some q))) = _
  rw [MvPolynomial.eval_rename]
  change MvPolynomial.aeval (Fin.cons 1 w ∘ (_root_.finSuccEquiv N).symm)
      (homogeneousAffinePolynomialChangeAlgEquiv b m hm
        (MvPolynomial.rename some q)) =
      MvPolynomial.aeval (fun j ↦ b j + m * w j) q
  rw [aeval_homogeneousAffinePolynomialChange]
  rw [aeval_rename]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  simp [homogeneousAffineLinearEquiv]

/-- Literal node-section ideal as the inverse image of the eliminated base
section. -/
theorem quotientNodeIdeal_eq_comap_nonvertexProjection
    (J : Ideal (MvPolynomial (Fin 12) K))
    (b : Fin 12 → K) (m : K) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) K) (i₀ : Fin 4)
    (hpivot : coneSectionVertexEvaluation
      (finSuccReindexedMatrix A) b m i₀ ≠ 0) :
    isolatedVertexTranslatedConeFinIdeal b m hm J ⊔ matrixRowLinearIdeal A =
      (J ⊔ indexedMatrixRowLinearIdeal
          (coneSectionThreeEquationMatrix
            (finSuccReindexedMatrix A) b m i₀)).comap
        (genericNonvertexProjectionQuotientAlgHom
          b m hm (finSuccReindexedMatrix A) i₀) := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv 12)
  let T := homogeneousAffinePolynomialChangeAlgEquiv b m hm
  let U := E.trans T.symm
  let A' := finSuccReindexedMatrix A
  let D := coneSectionThreeEquationMatrix A' b m i₀
  let H := projectiveConeIdealExtension J ⊔
    indexedMatrixRowLinearIdeal (translatedConeCoordinateSectionMatrix b m A')
  have hsourceMap :
      (isolatedVertexTranslatedConeFinIdeal b m hm J ⊔
        matrixRowLinearIdeal A).map U = H := by
    calc
      (isolatedVertexTranslatedConeFinIdeal b m hm J ⊔
          matrixRowLinearIdeal A).map U =
        ((isolatedVertexTranslatedConeFinIdeal b m hm J ⊔
          matrixRowLinearIdeal A).map E).map T.symm := by
            exact ((isolatedVertexTranslatedConeFinIdeal b m hm J ⊔
              matrixRowLinearIdeal A).map_mapₐ E.toAlgHom T.symm.toAlgHom).symm
      _ = (translatedProjectiveConeIdeal b m hm J ⊔
          indexedMatrixRowLinearIdeal A').map T.symm := by
        rw [Ideal.map_sup, map_isolatedVertexTranslatedConeFinIdeal_renameEquiv_finSucc,
          map_matrixRowLinearIdeal_renameEquiv_finSucc]
      _ = H := map_translatedCone_sup_rows_homogeneousAffine_symm
        J b m hm A'
  have hcoord : H =
      (J ⊔ indexedMatrixRowLinearIdeal D).comap
        (optionLinearEliminationAlgHom
          (genericConePivotEliminationForm b m A' i₀)) := by
    exact generic_coordinateConeSupRows_eq_comap_elimination
      J b m hm A' i₀ hpivot
  calc
    isolatedVertexTranslatedConeFinIdeal b m hm J ⊔ matrixRowLinearIdeal A =
        ((isolatedVertexTranslatedConeFinIdeal b m hm J ⊔
          matrixRowLinearIdeal A).map U).comap U :=
      (Ideal.comap_map_of_bijective U U.bijective).symm
    _ = ((J ⊔ indexedMatrixRowLinearIdeal D).comap
        (optionLinearEliminationAlgHom
          (genericConePivotEliminationForm b m A' i₀))).comap U := by
      rw [hsourceMap, hcoord]
    _ = _ := by rfl

end

end TranslatedDepthSeven
