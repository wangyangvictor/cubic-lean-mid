import TranslatedDepthSeven.TranslatedProjectiveConeJoin
import TranslatedDepthSeven.RationalProjectiveLinearSpace
import TranslatedDepthSeven.ProjectiveLinearHeightBound
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight
import TranslatedDepthSeven.AffinePacketProjectiveSection

/-!
# Images of packet sections under the translated-cone projection

Let `A` be four independent homogeneous equations in the coordinates
`(s,y) ∈ ℚ × ℚ¹³`, and put

`L(s,y) = s x₀ + m y`,  `ω = (m,-x₀)`.

The kernel of `L` is the line spanned by `ω`.  This file writes down
equations for the image of `ker A` under `L`.  If `Aω=0`, the four spatial
parts of the rows of `A` remain independent and cut out the image.  If
`Aω≠0`, choose a row `i₀` for which `(Aω) i₀≠0` and eliminate the
homogenizing variable; the three resulting equations cut out the image.

Everything is stated for literal matrices and vectors.  The final part
records integral coefficient and Plücker-height bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization
open Matrix

set_option maxHeartbeats 1200000

/-- The linear projection `(s,y) ↦ s x₀ + m y`. -/
def translatedJoinProjection
    (x₀ : Fin 13 → ℚ) (m : ℚ)
    (v : Option (Fin 13) → ℚ) : Fin 13 → ℚ :=
  fun j ↦ v none * x₀ j + m * v (some j)

/-- The preceding formula as a rational linear map. -/
def translatedJoinProjectionLinearMap
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    (Option (Fin 13) → ℚ) →ₗ[ℚ] (Fin 13 → ℚ) where
  toFun := translatedJoinProjection x₀ m
  map_add' := by
    intro u v
    funext j
    simp [translatedJoinProjection]
    ring
  map_smul' := by
    intro c v
    funext j
    simp [translatedJoinProjection]
    ring

@[simp]
theorem translatedJoinProjectionLinearMap_apply
    (x₀ : Fin 13 → ℚ) (m : ℚ)
    (v : Option (Fin 13) → ℚ) :
    translatedJoinProjectionLinearMap x₀ m v =
      translatedJoinProjection x₀ m v :=
  rfl

/-- The spatial part of four homogeneous equations. -/
def projectiveSectionSpatialMatrix
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ) :
    Matrix (Fin 4) (Fin 13) ℚ :=
  fun i j ↦ A i (some j)

/-- Evaluation of the equations at the kernel vector `ω=(m,-x₀)`. -/
def translatedJoinVertexEvaluation
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) : Fin 4 → ℚ :=
  A *ᵥ translatedProjectiveConeVertexVector x₀ m

theorem translatedJoinVertexEvaluation_apply
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (i : Fin 4) :
    translatedJoinVertexEvaluation A x₀ m i =
      m * A i none -
        ∑ j, projectiveSectionSpatialMatrix A i j * x₀ j := by
  simp [translatedJoinVertexEvaluation,
    translatedProjectiveConeVertexVector, Matrix.mulVec, dotProduct,
    projectiveSectionSpatialMatrix]
  ring

/-- The kernel vector is killed by the translated-cone projection. -/
@[simp]
theorem translatedJoinProjection_vertex
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    translatedJoinProjection x₀ m
        (translatedProjectiveConeVertexVector x₀ m) = 0 := by
  funext j
  simp [translatedJoinProjection,
    translatedProjectiveConeVertexVector]

/-- The basic elimination identity
`m A(s,y) = D L(s,y) + (Aω)s`. -/
theorem projectiveSection_elimination_identity
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ)
    (v : Option (Fin 13) → ℚ) (i : Fin 4) :
    m * (A *ᵥ v) i =
      (projectiveSectionSpatialMatrix A *ᵥ
        translatedJoinProjection x₀ m v) i +
      translatedJoinVertexEvaluation A x₀ m i * v none := by
  classical
  rw [translatedJoinVertexEvaluation_apply]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option,
    projectiveSectionSpatialMatrix, translatedJoinProjection]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have h₁ : (∑ j, A i (some j) * (v none * x₀ j)) =
      v none * ∑ j, A i (some j) * x₀ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have h₂ : (∑ j, A i (some j) * (m * v (some j))) =
      m * ∑ j, A i (some j) * v (some j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [h₁, h₂]
  ring

/-- A convenient explicit preimage of `x` with prescribed homogenizing
coordinate `s`. -/
def translatedJoinProjectionPreimage
    (x₀ : Fin 13 → ℚ) (m s : ℚ) (x : Fin 13 → ℚ) :
    Option (Fin 13) → ℚ
  | none => s
  | some j => (x j - s * x₀ j) / m

theorem translatedJoinProjection_preimage
    (x₀ : Fin 13 → ℚ) (m s : ℚ) (hm : m ≠ 0)
    (x : Fin 13 → ℚ) :
    translatedJoinProjection x₀ m
        (translatedJoinProjectionPreimage x₀ m s x) = x := by
  funext j
  simp [translatedJoinProjection, translatedJoinProjectionPreimage]
  field_simp
  ring

/-- Reindex the three rows different from a chosen pivot row. -/
def finThreeEquivNonpivotRow (i₀ : Fin 4) :
    Fin 3 ≃ {i : Fin 4 // i ≠ i₀} :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin]
    rw [Fintype.card_subtype_compl]
    simp)

/-- If `β=Aω` and `β i₀≠0`, eliminate the homogenizing variable
between row `i₀` and each of the other three rows. -/
def translatedJoinImageThreeEquationMatrix
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin 13) ℚ :=
  fun k j ↦
    translatedJoinVertexEvaluation A x₀ m i₀ *
        projectiveSectionSpatialMatrix A (finThreeEquivNonpivotRow i₀ k) j -
      translatedJoinVertexEvaluation A x₀ m
          (finThreeEquivNonpivotRow i₀ k) *
        projectiveSectionSpatialMatrix A i₀ j

/-- In the vertex-contained case, the spatial parts of the four equations
cut out exactly the vector-space image of `ker A`. -/
theorem exists_kernel_preimage_iff_spatial_mulVec_eq_zero
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : translatedJoinVertexEvaluation A x₀ m = 0)
    (x : Fin 13 → ℚ) :
    (∃ v : Option (Fin 13) → ℚ,
        A *ᵥ v = 0 ∧ translatedJoinProjection x₀ m v = x) ↔
      projectiveSectionSpatialMatrix A *ᵥ x = 0 := by
  constructor
  · rintro ⟨v, hAv, rfl⟩
    funext i
    have hi := projectiveSection_elimination_identity A x₀ m v i
    have hAi := congrFun hAv i
    have hβi := congrFun hvertex i
    simpa [hAi, hβi] using hi.symm
  · intro hx
    let v := translatedJoinProjectionPreimage x₀ m 0 x
    refine ⟨v, ?_, translatedJoinProjection_preimage x₀ m 0 hm x⟩
    funext i
    have hi := projectiveSection_elimination_identity A x₀ m v i
    have hDi := congrFun hx i
    have hβi := congrFun hvertex i
    have hLv := translatedJoinProjection_preimage x₀ m 0 hm x
    rw [show translatedJoinProjection x₀ m v = x by exact hLv] at hi
    have hzero : m * (A *ᵥ v) i = 0 := by
      simpa [hDi, hβi] using hi
    exact (mul_eq_zero.mp hzero).resolve_left hm

/-- Evaluation of an eliminated equation is the corresponding alternating
combination of the two spatial equations. -/
theorem translatedJoinImageThreeEquationMatrix_mulVec
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (i₀ : Fin 4)
    (x : Fin 13 → ℚ) (k : Fin 3) :
    (translatedJoinImageThreeEquationMatrix A x₀ m i₀ *ᵥ x) k =
      translatedJoinVertexEvaluation A x₀ m i₀ *
          (projectiveSectionSpatialMatrix A *ᵥ x)
            (finThreeEquivNonpivotRow i₀ k) -
        translatedJoinVertexEvaluation A x₀ m
            (finThreeEquivNonpivotRow i₀ k) *
          (projectiveSectionSpatialMatrix A *ᵥ x) i₀ := by
  classical
  simp only [Matrix.mulVec, dotProduct,
    translatedJoinImageThreeEquationMatrix,
    projectiveSectionSpatialMatrix]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun a b : ℚ ↦ a - b)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- If the vertex is not in the section, the three literal eliminated
equations cut out exactly the vector-space image of `ker A`. -/
theorem exists_kernel_preimage_iff_threeEquation_mulVec_eq_zero
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0)
    (x : Fin 13 → ℚ) :
    (∃ v : Option (Fin 13) → ℚ,
        A *ᵥ v = 0 ∧ translatedJoinProjection x₀ m v = x) ↔
      translatedJoinImageThreeEquationMatrix A x₀ m i₀ *ᵥ x = 0 := by
  constructor
  · rintro ⟨v, hAv, rfl⟩
    funext k
    rw [translatedJoinImageThreeEquationMatrix_mulVec]
    let i := (finThreeEquivNonpivotRow i₀ k).1
    have hi := projectiveSection_elimination_identity A x₀ m v i
    have hi₀ := projectiveSection_elimination_identity A x₀ m v i₀
    have hAi := congrFun hAv i
    have hAi₀ := congrFun hAv i₀
    change _ * (projectiveSectionSpatialMatrix A *ᵥ
        translatedJoinProjection x₀ m v) i -
      translatedJoinVertexEvaluation A x₀ m i *
        (projectiveSectionSpatialMatrix A *ᵥ
          translatedJoinProjection x₀ m v) i₀ = 0
    rw [hAi] at hi
    rw [hAi₀] at hi₀
    have hDi :
        (projectiveSectionSpatialMatrix A *ᵥ
          translatedJoinProjection x₀ m v) i =
        -translatedJoinVertexEvaluation A x₀ m i * v none := by
      simp only [Pi.zero_apply, mul_zero] at hi
      linarith
    have hDi₀ :
        (projectiveSectionSpatialMatrix A *ᵥ
          translatedJoinProjection x₀ m v) i₀ =
        -translatedJoinVertexEvaluation A x₀ m i₀ * v none := by
      simp only [Pi.zero_apply, mul_zero] at hi₀
      linarith
    rw [hDi, hDi₀]
    ring
  · intro hx
    let D := projectiveSectionSpatialMatrix A
    let β := translatedJoinVertexEvaluation A x₀ m
    let s : ℚ := -(D *ᵥ x) i₀ / β i₀
    let v := translatedJoinProjectionPreimage x₀ m s x
    have hLv : translatedJoinProjection x₀ m v = x :=
      translatedJoinProjection_preimage x₀ m s hm x
    refine ⟨v, ?_, hLv⟩
    funext i
    have hsum : (D *ᵥ x) i + β i * s = 0 := by
      by_cases hii₀ : i = i₀
      · subst i
        dsimp [s]
        have hβ : β i₀ ≠ 0 := hpivot
        (field_simp [hβ]; ring)
      · let k : Fin 3 :=
          (finThreeEquivNonpivotRow i₀).symm ⟨i, hii₀⟩
        have hk := congrFun hx k
        simp only [Pi.zero_apply] at hk
        rw [translatedJoinImageThreeEquationMatrix_mulVec] at hk
        have heq : (finThreeEquivNonpivotRow i₀ k).1 = i := by
          simp [k]
        rw [heq] at hk
        change β i₀ * (D *ᵥ x) i - β i * (D *ᵥ x) i₀ = 0 at hk
        dsimp [s]
        have hβ : β i₀ ≠ 0 := hpivot
        calc
          (D *ᵥ x) i + β i * (-((D *ᵥ x) i₀) / β i₀) =
              (β i₀ * (D *ᵥ x) i - β i * (D *ᵥ x) i₀) /
                β i₀ := by
            field_simp [hβ]
            ring
          _ = 0 := by rw [hk]; simp
    have hi := projectiveSection_elimination_identity A x₀ m v i
    rw [hLv] at hi
    change m * (A *ᵥ v) i = (D *ᵥ x) i + β i * s at hi
    rw [hsum] at hi
    exact (mul_eq_zero.mp hi).resolve_left hm

/-- Four independent equations in fourteen coordinates have a
ten-dimensional kernel. -/
theorem finrank_kernel_four_by_fourteen
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (hA : A.rank = 4) :
    Module.finrank ℚ (LinearMap.ker A.mulVecLin) = 10 := by
  have hrange :
      Module.finrank ℚ (LinearMap.range A.mulVecLin) = 4 := by
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols, hA]
  have hnullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hrange] at hnullity
  have hdomain : Module.finrank ℚ (Option (Fin 13) → ℚ) = 14 := by
    simp
  rw [hdomain] at hnullity
  omega

/-- If one vertex evaluation is nonzero, the join projection is injective
on the kernel of the four equations. -/
theorem translatedJoinProjection_domRestrict_injective_of_pivot
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0) :
    Function.Injective
      ((translatedJoinProjectionLinearMap x₀ m).domRestrict
        (LinearMap.ker A.mulVecLin)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hAv : A *ᵥ (v : Option (Fin 13) → ℚ) = 0 := v.property
  have hLv :
      translatedJoinProjection x₀ m (v : Option (Fin 13) → ℚ) = 0 := hv
  have hi := projectiveSection_elimination_identity A x₀ m
    (v : Option (Fin 13) → ℚ) i₀
  rw [hLv] at hi
  have hAi := congrFun hAv i₀
  have hvnone : (v : Option (Fin 13) → ℚ) none = 0 := by
    have hproduct : translatedJoinVertexEvaluation A x₀ m i₀ *
        (v : Option (Fin 13) → ℚ) none = 0 := by
      simpa [hAi] using hi.symm
    exact (mul_eq_zero.mp hproduct).resolve_left hpivot
  apply Subtype.ext
  funext q
  cases q with
  | none => simpa using hvnone
  | some j =>
      have hj := congrFun hLv j
      have hproduct : m * (v : Option (Fin 13) → ℚ) (some j) = 0 := by
        simpa [translatedJoinProjection, hvnone] using hj
      have hvj := (mul_eq_zero.mp hproduct).resolve_left hm
      simpa using hvj

/-- The range of the restricted join projection is literally the kernel of
the three eliminated equations. -/
theorem range_domRestrict_eq_kernel_threeEquation
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0) :
    LinearMap.range
        ((translatedJoinProjectionLinearMap x₀ m).domRestrict
          (LinearMap.ker A.mulVecLin)) =
      LinearMap.ker
        (translatedJoinImageThreeEquationMatrix A x₀ m i₀).mulVecLin := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    have himage :=
      (exists_kernel_preimage_iff_threeEquation_mulVec_eq_zero
        A x₀ m hm i₀ hpivot x).mp
        ⟨(v : Option (Fin 13) → ℚ), v.property, by simpa using hv⟩
    exact himage
  · intro hx
    obtain ⟨v, hAv, hLv⟩ :=
      (exists_kernel_preimage_iff_threeEquation_mulVec_eq_zero
        A x₀ m hm i₀ hpivot x).mpr hx
    exact ⟨⟨v, hAv⟩, hLv⟩

/-- If the vertex is not in the section, its image in `ℙ¹²` has
codimension three. -/
theorem translatedJoinImageThreeEquationMatrix_rank
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0) :
    (translatedJoinImageThreeEquationMatrix A x₀ m i₀).rank = 3 := by
  let W := LinearMap.ker A.mulVecLin
  let L := (translatedJoinProjectionLinearMap x₀ m).domRestrict W
  let E := translatedJoinImageThreeEquationMatrix A x₀ m i₀
  have hW : Module.finrank ℚ W = 10 :=
    finrank_kernel_four_by_fourteen A hA
  have hLinj : Function.Injective L :=
    translatedJoinProjection_domRestrict_injective_of_pivot
      A x₀ m hm i₀ hpivot
  have hrangeL : Module.finrank ℚ (LinearMap.range L) = 10 := by
    rw [LinearMap.finrank_range_of_inj hLinj, hW]
  have hrangeEq : LinearMap.range L = LinearMap.ker E.mulVecLin :=
    range_domRestrict_eq_kernel_threeEquation A x₀ m hm i₀ hpivot
  have hkerE : Module.finrank ℚ (LinearMap.ker E.mulVecLin) = 10 := by
    rw [← hrangeEq]
    exact hrangeL
  have hrangeE : Module.finrank ℚ (LinearMap.range E.mulVecLin) = E.rank := by
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
  have hnullity := LinearMap.finrank_range_add_finrank_ker E.mulVecLin
  rw [hrangeE, hkerE] at hnullity
  have hdomain : Module.finrank ℚ (Fin 13 → ℚ) = 13 := by simp
  rw [hdomain] at hnullity
  change E.rank = 3
  omega

/-- For `m≠0`, the join projection is onto. -/
theorem translatedJoinProjectionLinearMap_surjective
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    Function.Surjective (translatedJoinProjectionLinearMap x₀ m) := by
  intro x
  refine ⟨translatedJoinProjectionPreimage x₀ m 0 x, ?_⟩
  exact translatedJoinProjection_preimage x₀ m 0 hm x

/-- Its kernel is the one-dimensional vertex line. -/
theorem finrank_kernel_translatedJoinProjectionLinearMap
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    Module.finrank ℚ (LinearMap.ker
      (translatedJoinProjectionLinearMap x₀ m)) = 1 := by
  let L := translatedJoinProjectionLinearMap x₀ m
  have hsurj : Function.Surjective L :=
    translatedJoinProjectionLinearMap_surjective x₀ m hm
  have hrangeTop : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrange : Module.finrank ℚ (LinearMap.range L) = 13 := by
    rw [hrangeTop]
    simp
  have hnullity := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange] at hnullity
  have hdomain : Module.finrank ℚ (Option (Fin 13) → ℚ) = 14 := by
    simp
  rw [hdomain] at hnullity
  change Module.finrank ℚ (LinearMap.ker L) = 1
  omega

/-- When `Aω=0`, restriction to `ker A` retains precisely the vertex line
as its kernel. -/
theorem finrank_kernel_translatedJoinProjection_domRestrict_of_vertex
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : translatedJoinVertexEvaluation A x₀ m = 0) :
    Module.finrank ℚ
        (LinearMap.ker
          ((translatedJoinProjectionLinearMap x₀ m).domRestrict
            (LinearMap.ker A.mulVecLin))) = 1 := by
  let W := LinearMap.ker A.mulVecLin
  let L := translatedJoinProjectionLinearMap x₀ m
  let Lw := L.domRestrict W
  let K := LinearMap.ker Lw
  let KL := LinearMap.ker L
  let inclusion : K →ₗ[ℚ] KL :=
    { toFun := fun z ↦ ⟨(z.1 : Option (Fin 13) → ℚ), z.property⟩
      map_add' := by intro u v; rfl
      map_smul' := by intro c v; rfl }
  have hinclusion : Function.Injective inclusion := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : KL ↦ (z : Option (Fin 13) → ℚ)) huv
  have hupper : Module.finrank ℚ K ≤ 1 := by
    calc
      Module.finrank ℚ K ≤ Module.finrank ℚ KL :=
        inclusion.finrank_le_finrank_of_injective hinclusion
      _ = 1 := finrank_kernel_translatedJoinProjectionLinearMap x₀ m hm
  let ω : Option (Fin 13) → ℚ :=
    translatedProjectiveConeVertexVector x₀ m
  have hωA : A *ᵥ ω = 0 := hvertex
  let ωW : W := ⟨ω, hωA⟩
  have hωL : Lw ωW = 0 := by
    exact translatedJoinProjection_vertex x₀ m
  let ωK : K := ⟨ωW, hωL⟩
  have hωne : ωK ≠ 0 := by
    intro hzero
    have hval : ω = 0 := by
      exact congrArg (fun z : K ↦ (z.1 : Option (Fin 13) → ℚ)) hzero
    exact (translatedProjectiveConeVertexVector_ne_zero x₀ m hm) hval
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hωWzero : ωK.1 = 0 :=
      (Submodule.eq_bot_iff K).mp hbot ωK.1 ωK.property
    apply hωne
    apply Subtype.ext
    exact hωWzero
  have hlower : 1 ≤ Module.finrank ℚ K :=
    Submodule.one_le_finrank_iff.mpr hKne
  exact Nat.le_antisymm hupper hlower

/-- In the vertex-contained case, the range of the restricted projection is
the kernel of the four spatial equations. -/
theorem range_domRestrict_eq_kernel_spatial
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : translatedJoinVertexEvaluation A x₀ m = 0) :
    LinearMap.range
        ((translatedJoinProjectionLinearMap x₀ m).domRestrict
          (LinearMap.ker A.mulVecLin)) =
      LinearMap.ker (projectiveSectionSpatialMatrix A).mulVecLin := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    exact (exists_kernel_preimage_iff_spatial_mulVec_eq_zero
      A x₀ m hm hvertex x).mp
      ⟨(v : Option (Fin 13) → ℚ), v.property, by simpa using hv⟩
  · intro hx
    obtain ⟨v, hAv, hLv⟩ :=
      (exists_kernel_preimage_iff_spatial_mulVec_eq_zero
        A x₀ m hm hvertex x).mpr hx
    exact ⟨⟨v, hAv⟩, hLv⟩

/-- If the vertex belongs to the original codimension-four section, the
image in `ℙ¹²` still has codimension four. -/
theorem projectiveSectionSpatialMatrix_rank_of_vertex
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : translatedJoinVertexEvaluation A x₀ m = 0) :
    (projectiveSectionSpatialMatrix A).rank = 4 := by
  let W := LinearMap.ker A.mulVecLin
  let L := (translatedJoinProjectionLinearMap x₀ m).domRestrict W
  let D := projectiveSectionSpatialMatrix A
  have hW : Module.finrank ℚ W = 10 :=
    finrank_kernel_four_by_fourteen A hA
  have hkerL : Module.finrank ℚ (LinearMap.ker L) = 1 :=
    finrank_kernel_translatedJoinProjection_domRestrict_of_vertex
      A x₀ m hm hvertex
  have hnullityL := LinearMap.finrank_range_add_finrank_ker L
  rw [hkerL, hW] at hnullityL
  have hrangeL : Module.finrank ℚ (LinearMap.range L) = 9 := by omega
  have hrangeEq : LinearMap.range L = LinearMap.ker D.mulVecLin :=
    range_domRestrict_eq_kernel_spatial A x₀ m hm hvertex
  have hkerD : Module.finrank ℚ (LinearMap.ker D.mulVecLin) = 9 := by
    rw [← hrangeEq]
    exact hrangeL
  have hrangeD : Module.finrank ℚ (LinearMap.range D.mulVecLin) = D.rank := by
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
  have hnullityD := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  rw [hrangeD, hkerD] at hnullityD
  have hdomain : Module.finrank ℚ (Fin 13 → ℚ) = 13 := by simp
  rw [hdomain] at hnullityD
  change D.rank = 4
  omega

/-- Every nonzero projected vector from `ker A` gives a point of the
codimension-four image space in the vertex-contained case. -/
theorem projectedPoint_mem_spatialProjectiveLinearSpace
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : translatedJoinVertexEvaluation A x₀ m = 0)
    (v : Option (Fin 13) → ℚ) (hAv : A *ᵥ v = 0)
    (hprojected : translatedJoinProjection x₀ m v ≠ 0) :
    Projectivization.mk ℚ (translatedJoinProjection x₀ m v) hprojected ∈
      rationalProjectiveLinearSpace (projectiveSectionSpatialMatrix A) := by
  apply (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
    _ _ hprojected).2
  exact (exists_kernel_preimage_iff_spatial_mulVec_eq_zero
    A x₀ m hm hvertex _).mp ⟨v, hAv, rfl⟩

/-- Every nonzero projected vector from `ker A` gives a point of the
codimension-three eliminated image space in the complementary case. -/
theorem projectedPoint_mem_threeEquationProjectiveLinearSpace
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0)
    (v : Option (Fin 13) → ℚ) (hAv : A *ᵥ v = 0)
    (hprojected : translatedJoinProjection x₀ m v ≠ 0) :
    Projectivization.mk ℚ (translatedJoinProjection x₀ m v) hprojected ∈
      rationalProjectiveLinearSpace
        (translatedJoinImageThreeEquationMatrix A x₀ m i₀) := by
  apply (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
    _ _ hprojected).2
  exact (exists_kernel_preimage_iff_threeEquation_mulVec_eq_zero
    A x₀ m hm i₀ hpivot _).mp ⟨v, hAv, rfl⟩

/-- If the vertex is not in `ker A`, some one of the four displayed
vertex evaluations can be used as the elimination pivot. -/
theorem exists_translatedJoinVertexEvaluation_ne_zero
    (A : Matrix (Fin 4) (Option (Fin 13)) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ)
    (hvertex : translatedProjectiveConeVertexVector x₀ m ∉
      LinearMap.ker A.mulVecLin) :
    ∃ i₀ : Fin 4, translatedJoinVertexEvaluation A x₀ m i₀ ≠ 0 := by
  by_contra h
  push_neg at h
  apply hvertex
  exact funext h

/-! ## Standard `Fin 14` homogeneous coordinates -/

/-- Reindex the fourteen standard homogeneous coordinates as
`Option (Fin 13)`, with coordinate zero corresponding to `none`. -/
def reindexedHomogeneousEquationMatrix
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    Matrix (Fin 4) (Option (Fin 13)) ℚ :=
  A.submatrix (Equiv.refl (Fin 4)) (finSuccEquiv 13).symm

theorem reindexedHomogeneousEquationMatrix_rank
    (A : Matrix (Fin 4) (Fin 14) ℚ) :
    (reindexedHomogeneousEquationMatrix A).rank = A.rank := by
  exact Matrix.rank_submatrix A (Equiv.refl (Fin 4)) (finSuccEquiv 13).symm

/-- The vector `(m,-x₀)` in standard `Fin 14` coordinates. -/
def translatedJoinVertexFinVector
    (x₀ : Fin 13 → ℚ) (m : ℚ) : Fin 14 → ℚ :=
  fun q ↦ translatedProjectiveConeVertexVector x₀ m (finSuccEquiv 13 q)

/-- The projection in standard `Fin 14` coordinates. -/
def translatedJoinProjectionFin
    (x₀ : Fin 13 → ℚ) (m : ℚ)
    (v : Fin 14 → ℚ) : Fin 13 → ℚ :=
  translatedJoinProjection x₀ m (v ∘ (finSuccEquiv 13).symm)

theorem reindexedHomogeneousEquationMatrix_mulVec
    (A : Matrix (Fin 4) (Fin 14) ℚ) (v : Fin 14 → ℚ) :
    reindexedHomogeneousEquationMatrix A *ᵥ
        (v ∘ (finSuccEquiv 13).symm) = A *ᵥ v := by
  change (A.submatrix (Equiv.refl (Fin 4)) (finSuccEquiv 13).symm) *ᵥ
      (v ∘ (finSuccEquiv 13).symm) = A *ᵥ v
  rw [Matrix.submatrix_mulVec_equiv]
  rfl

theorem translatedJoinVertexEvaluation_reindexed
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    translatedJoinVertexEvaluation
        (reindexedHomogeneousEquationMatrix A) x₀ m =
      A *ᵥ translatedJoinVertexFinVector x₀ m := by
  rw [translatedJoinVertexEvaluation]
  have hvector : translatedJoinVertexFinVector x₀ m ∘
      (finSuccEquiv 13).symm =
        translatedProjectiveConeVertexVector x₀ m := by
    funext q
    simp [translatedJoinVertexFinVector]
  rw [← hvector, reindexedHomogeneousEquationMatrix_mulVec]

/-- The four-equation image matrix in standard coordinates. -/
def translatedJoinImageFourEquationMatrixFin
    (A : Matrix (Fin 4) (Fin 14) ℚ) : Matrix (Fin 4) (Fin 13) ℚ :=
  projectiveSectionSpatialMatrix (reindexedHomogeneousEquationMatrix A)

/-- The three-equation image matrix in standard coordinates after choosing
a nonzero vertex-evaluation row. -/
def translatedJoinImageThreeEquationMatrixFin
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin 13) ℚ :=
  translatedJoinImageThreeEquationMatrix
    (reindexedHomogeneousEquationMatrix A) x₀ m i₀

/-- Standard-coordinate codimension-four branch. -/
theorem translatedJoinImageFourEquationMatrixFin_rank
    (A : Matrix (Fin 4) (Fin 14) ℚ) (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : A *ᵥ translatedJoinVertexFinVector x₀ m = 0) :
    (translatedJoinImageFourEquationMatrixFin A).rank = 4 := by
  apply projectiveSectionSpatialMatrix_rank_of_vertex
  · rw [reindexedHomogeneousEquationMatrix_rank, hA]
  · exact hm
  · rw [translatedJoinVertexEvaluation_reindexed]
    exact hvertex

/-- Standard-coordinate codimension-three branch for a displayed pivot. -/
theorem translatedJoinImageThreeEquationMatrixFin_rank
    (A : Matrix (Fin 4) (Fin 14) ℚ) (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : (A *ᵥ translatedJoinVertexFinVector x₀ m) i₀ ≠ 0) :
    (translatedJoinImageThreeEquationMatrixFin A x₀ m i₀).rank = 3 := by
  apply translatedJoinImageThreeEquationMatrix_rank
  · rw [reindexedHomogeneousEquationMatrix_rank, hA]
  · exact hm
  · rw [translatedJoinVertexEvaluation_reindexed]
    exact hpivot

/-- If the vertex is not in the original kernel, a pivot and a literal
rank-three image equation matrix exist. -/
theorem exists_translatedJoinImageThreeEquationMatrixFin_rank
    (A : Matrix (Fin 4) (Fin 14) ℚ) (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : A *ᵥ translatedJoinVertexFinVector x₀ m ≠ 0) :
    ∃ i₀ : Fin 4,
      (A *ᵥ translatedJoinVertexFinVector x₀ m) i₀ ≠ 0 ∧
      (translatedJoinImageThreeEquationMatrixFin A x₀ m i₀).rank = 3 := by
  have hexists : ∃ i₀ : Fin 4,
      (A *ᵥ translatedJoinVertexFinVector x₀ m) i₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hvertex (funext h)
  obtain ⟨i₀, hi₀⟩ := hexists
  exact ⟨i₀, hi₀,
    translatedJoinImageThreeEquationMatrixFin_rank
      A hA x₀ m hm i₀ hi₀⟩

/-- Static rank dichotomy for a codimension-four section under the join
projection. -/
theorem translatedJoinImage_rank_dichotomyFin
    (A : Matrix (Fin 4) (Fin 14) ℚ) (hA : A.rank = 4)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0) :
    (A *ᵥ translatedJoinVertexFinVector x₀ m = 0 ∧
        (translatedJoinImageFourEquationMatrixFin A).rank = 4) ∨
      ∃ i₀ : Fin 4,
        (A *ᵥ translatedJoinVertexFinVector x₀ m) i₀ ≠ 0 ∧
        (translatedJoinImageThreeEquationMatrixFin A x₀ m i₀).rank = 3 := by
  by_cases hvertex : A *ᵥ translatedJoinVertexFinVector x₀ m = 0
  · exact Or.inl ⟨hvertex,
      translatedJoinImageFourEquationMatrixFin_rank
        A hA x₀ m hm hvertex⟩
  · exact Or.inr
      (exists_translatedJoinImageThreeEquationMatrixFin_rank
        A hA x₀ m hm hvertex)

/-- A standard-coordinate source point in `ker A` projects into the
four-equation image kernel. -/
theorem translatedJoinImageFourEquationMatrixFin_mulVec_projection_eq_zero
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (hvertex : A *ᵥ translatedJoinVertexFinVector x₀ m = 0)
    (v : Fin 14 → ℚ) (hAv : A *ᵥ v = 0) :
    translatedJoinImageFourEquationMatrixFin A *ᵥ
      translatedJoinProjectionFin x₀ m v = 0 := by
  apply (exists_kernel_preimage_iff_spatial_mulVec_eq_zero
    (reindexedHomogeneousEquationMatrix A) x₀ m hm
    (by simpa [translatedJoinVertexEvaluation_reindexed] using hvertex) _).mp
  refine ⟨v ∘ (finSuccEquiv 13).symm, ?_, rfl⟩
  simpa [reindexedHomogeneousEquationMatrix_mulVec] using hAv

/-- A standard-coordinate source point in `ker A` projects into the
three-equation image kernel. -/
theorem translatedJoinImageThreeEquationMatrixFin_mulVec_projection_eq_zero
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (x₀ : Fin 13 → ℚ) (m : ℚ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : (A *ᵥ translatedJoinVertexFinVector x₀ m) i₀ ≠ 0)
    (v : Fin 14 → ℚ) (hAv : A *ᵥ v = 0) :
    translatedJoinImageThreeEquationMatrixFin A x₀ m i₀ *ᵥ
      translatedJoinProjectionFin x₀ m v = 0 := by
  apply (exists_kernel_preimage_iff_threeEquation_mulVec_eq_zero
    (reindexedHomogeneousEquationMatrix A) x₀ m hm i₀
    (by simpa [translatedJoinVertexEvaluation_reindexed] using hpivot) _).mp
  refine ⟨v ∘ (finSuccEquiv 13).symm, ?_, rfl⟩
  simpa [reindexedHomogeneousEquationMatrix_mulVec] using hAv

/-! ## Integral equations and explicit heights -/

/-- Integral spatial parts of four homogeneous equations. -/
def integralTranslatedJoinImageFourEquationMatrix
    (A : Matrix (Fin 4) (Fin 14) ℤ) : Matrix (Fin 4) (Fin 13) ℤ :=
  fun i j ↦ A i ((finSuccEquiv 13).symm (some j))

/-- Integral evaluation of a row of `A` at `(m,-x₀)`. -/
def integralTranslatedJoinVertexEvaluation
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) : Fin 4 → ℤ :=
  fun i ↦
    m * A i ((finSuccEquiv 13).symm none) -
      ∑ j, integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j

/-- Integral eliminated equations in the branch where the displayed pivot
evaluation is nonzero. -/
def integralTranslatedJoinImageThreeEquationMatrix
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin 13) ℤ :=
  fun k j ↦
    integralTranslatedJoinVertexEvaluation A x₀ m i₀ *
        integralTranslatedJoinImageFourEquationMatrix A
          (finThreeEquivNonpivotRow i₀ k) j -
      integralTranslatedJoinVertexEvaluation A x₀ m
          (finThreeEquivNonpivotRow i₀ k) *
        integralTranslatedJoinImageFourEquationMatrix A i₀ j

theorem integralTranslatedJoinImageFourEquationMatrix_map_intCast
    (A : Matrix (Fin 4) (Fin 14) ℤ) :
    (integralTranslatedJoinImageFourEquationMatrix A).map
        ((↑) : ℤ → ℚ) =
      translatedJoinImageFourEquationMatrixFin
        (A.map ((↑) : ℤ → ℚ)) := by
  rfl

theorem integralTranslatedJoinVertexEvaluation_intCast
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (i : Fin 4) :
    (integralTranslatedJoinVertexEvaluation A x₀ m i : ℚ) =
      translatedJoinVertexEvaluation
        (reindexedHomogeneousEquationMatrix
          (A.map ((↑) : ℤ → ℚ)))
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i := by
  rw [translatedJoinVertexEvaluation_apply]
  simp only [integralTranslatedJoinVertexEvaluation,
    integralTranslatedJoinImageFourEquationMatrix,
    reindexedHomogeneousEquationMatrix,
    projectiveSectionSpatialMatrix, Matrix.submatrix_apply,
    Matrix.map_apply, Int.cast_sub, Int.cast_mul, Int.cast_sum]
  simp

theorem integralTranslatedJoinImageThreeEquationMatrix_map_intCast
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (i₀ : Fin 4) :
    (integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
        ((↑) : ℤ → ℚ) =
      translatedJoinImageThreeEquationMatrixFin
        (A.map ((↑) : ℤ → ℚ))
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i₀ := by
  ext k j
  simp only [Matrix.map_apply,
    integralTranslatedJoinImageThreeEquationMatrix,
    translatedJoinImageThreeEquationMatrixFin,
    translatedJoinImageThreeEquationMatrix, Int.cast_sub, Int.cast_mul]
  rw [integralTranslatedJoinVertexEvaluation_intCast,
    integralTranslatedJoinVertexEvaluation_intCast]
  rfl

/-- The four image equations inherit the entry bound of `A`. -/
theorem integralTranslatedJoinImageFourEquationMatrix_entry_natAbs_le
    {H : ℕ} (A : Matrix (Fin 4) (Fin 14) ℤ)
    (hA : ∀ i q, (A i q).natAbs ≤ H) (i : Fin 4) (j : Fin 13) :
    (integralTranslatedJoinImageFourEquationMatrix A i j).natAbs ≤ H :=
  hA i ((finSuccEquiv 13).symm (some j))

/-- Polynomial bound for every integral vertex evaluation. -/
theorem integralTranslatedJoinVertexEvaluation_natAbs_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ)
    (hA : ∀ i q, (A i q).natAbs ≤ H)
    (hx₀ : ∀ j, (x₀ j).natAbs ≤ X)
    (hm : m.natAbs ≤ M) (i : Fin 4) :
    (integralTranslatedJoinVertexEvaluation A x₀ m i).natAbs ≤
      (M + 13 * X) * H := by
  classical
  let q₀ := (finSuccEquiv 13).symm none
  have hfirst : (m * A i q₀).natAbs ≤ M * H := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hm (hA i q₀)
  have hsum :
      (∑ j, integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j).natAbs ≤
        13 * (H * X) := by
    calc
      (∑ j, integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j).natAbs ≤
          ∑ j, (integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j).natAbs :=
        int_natAbs_sum_le_sum_natAbs Finset.univ _
      _ ≤ ∑ _j : Fin 13, H * X := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul
          (integralTranslatedJoinImageFourEquationMatrix_entry_natAbs_le A hA i j)
          (hx₀ j)
      _ = 13 * (H * X) := by simp
  rw [integralTranslatedJoinVertexEvaluation]
  calc
    (m * A i q₀ -
        ∑ j, integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j).natAbs ≤
        (m * A i q₀).natAbs +
          (∑ j, integralTranslatedJoinImageFourEquationMatrix A i j * x₀ j).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ M * H + 13 * (H * X) := Nat.add_le_add hfirst hsum
    _ = (M + 13 * X) * H := by ring

/-- Polynomial entry bound for the three eliminated image equations. -/
theorem integralTranslatedJoinImageThreeEquationMatrix_entry_natAbs_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (i₀ : Fin 4)
    (hA : ∀ i q, (A i q).natAbs ≤ H)
    (hx₀ : ∀ j, (x₀ j).natAbs ≤ X)
    (hm : m.natAbs ≤ M) (k : Fin 3) (j : Fin 13) :
    (integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀ k j).natAbs ≤
      2 * ((M + 13 * X) * H) * H := by
  rw [integralTranslatedJoinImageThreeEquationMatrix]
  calc
    (integralTranslatedJoinVertexEvaluation A x₀ m i₀ *
          integralTranslatedJoinImageFourEquationMatrix A
            (finThreeEquivNonpivotRow i₀ k) j -
        integralTranslatedJoinVertexEvaluation A x₀ m
            (finThreeEquivNonpivotRow i₀ k) *
          integralTranslatedJoinImageFourEquationMatrix A i₀ j).natAbs ≤
        (integralTranslatedJoinVertexEvaluation A x₀ m i₀ *
          integralTranslatedJoinImageFourEquationMatrix A
            (finThreeEquivNonpivotRow i₀ k) j).natAbs +
        (integralTranslatedJoinVertexEvaluation A x₀ m
            (finThreeEquivNonpivotRow i₀ k) *
          integralTranslatedJoinImageFourEquationMatrix A i₀ j).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ ((M + 13 * X) * H) * H + ((M + 13 * X) * H) * H := by
      simp only [Int.natAbs_mul]
      exact Nat.add_le_add
        (Nat.mul_le_mul
          (integralTranslatedJoinVertexEvaluation_natAbs_le
            A x₀ m hA hx₀ hm i₀)
          (integralTranslatedJoinImageFourEquationMatrix_entry_natAbs_le
            A hA (finThreeEquivNonpivotRow i₀ k) j))
        (Nat.mul_le_mul
          (integralTranslatedJoinVertexEvaluation_natAbs_le
            A x₀ m hA hx₀ hm (finThreeEquivNonpivotRow i₀ k))
          (integralTranslatedJoinImageFourEquationMatrix_entry_natAbs_le
            A hA i₀ j))
    _ = 2 * ((M + 13 * X) * H) * H := by ring

/-- Plücker-height bound for the codimension-four image. -/
theorem integralTranslatedJoinImageFourEquationMatrix_height_le
    {H : ℕ} (A : Matrix (Fin 4) (Fin 14) ℤ)
    (hA : ∀ i q, (A i q).natAbs ≤ H) :
    rationalProjectiveLinearHeight
        ((integralTranslatedJoinImageFourEquationMatrix A).map
          ((↑) : ℤ → ℚ)) ≤
      Nat.factorial 4 * H ^ 4 := by
  exact rationalProjectiveLinearHeight_map_intCast_le
    (integralTranslatedJoinImageFourEquationMatrix A)
    (integralTranslatedJoinImageFourEquationMatrix_entry_natAbs_le A hA)

/-- Plücker-height bound for the codimension-three image. -/
theorem integralTranslatedJoinImageThreeEquationMatrix_height_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (i₀ : Fin 4)
    (hA : ∀ i q, (A i q).natAbs ≤ H)
    (hx₀ : ∀ j, (x₀ j).natAbs ≤ X)
    (hm : m.natAbs ≤ M) :
    rationalProjectiveLinearHeight
        ((integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
          ((↑) : ℤ → ℚ)) ≤
      Nat.factorial 3 * (2 * ((M + 13 * X) * H) * H) ^ 3 := by
  exact rationalProjectiveLinearHeight_map_intCast_le
    (integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀)
    (integralTranslatedJoinImageThreeEquationMatrix_entry_natAbs_le
      A x₀ m i₀ hA hx₀ hm)

/-- The projection of the standard affine point `[1:y]` is the displayed
integral affine combination `x₀+m y`. -/
theorem translatedJoinProjectionFin_rationalHomogeneousAffinePoint
    (x₀ y : Fin 13 → ℤ) (m : ℤ) :
    translatedJoinProjectionFin (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
        (rationalHomogeneousAffinePoint y) =
      fun j ↦ ((x₀ j + m * y j : ℤ) : ℚ) := by
  funext j
  simp [translatedJoinProjectionFin, translatedJoinProjection,
    rationalHomogeneousAffinePoint]

/-- The integral four-equation matrix has rank four in the
vertex-contained branch. -/
theorem integralTranslatedJoinImageFourEquationMatrix_rank
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (hA : (A.map ((↑) : ℤ → ℚ)).rank = 4)
    (hvertex : integralTranslatedJoinVertexEvaluation A x₀ m = 0) :
    ((integralTranslatedJoinImageFourEquationMatrix A).map
      ((↑) : ℤ → ℚ)).rank = 4 := by
  rw [integralTranslatedJoinImageFourEquationMatrix_map_intCast]
  apply translatedJoinImageFourEquationMatrixFin_rank
    (A.map ((↑) : ℤ → ℚ)) hA
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed]
    funext i
    rw [← integralTranslatedJoinVertexEvaluation_intCast]
    simp [hvertex]

/-- The integral three-equation matrix has rank three when its chosen
vertex evaluation is nonzero. -/
theorem integralTranslatedJoinImageThreeEquationMatrix_rank
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (hA : (A.map ((↑) : ℤ → ℚ)).rank = 4)
    (i₀ : Fin 4)
    (hpivot : integralTranslatedJoinVertexEvaluation A x₀ m i₀ ≠ 0) :
    ((integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
      ((↑) : ℤ → ℚ)).rank = 3 := by
  rw [integralTranslatedJoinImageThreeEquationMatrix_map_intCast]
  apply translatedJoinImageThreeEquationMatrixFin_rank
    (A.map ((↑) : ℤ → ℚ)) hA
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed,
      ← integralTranslatedJoinVertexEvaluation_intCast]
    exact_mod_cast hpivot

/-- Integral form of the same static rank dichotomy. -/
theorem integralTranslatedJoinImage_rank_dichotomy
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (hA : (A.map ((↑) : ℤ → ℚ)).rank = 4) :
    (integralTranslatedJoinVertexEvaluation A x₀ m = 0 ∧
        ((integralTranslatedJoinImageFourEquationMatrix A).map
          ((↑) : ℤ → ℚ)).rank = 4) ∨
      ∃ i₀ : Fin 4,
        integralTranslatedJoinVertexEvaluation A x₀ m i₀ ≠ 0 ∧
        ((integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
          ((↑) : ℤ → ℚ)).rank = 3 := by
  by_cases hvertex : integralTranslatedJoinVertexEvaluation A x₀ m = 0
  · exact Or.inl ⟨hvertex,
      integralTranslatedJoinImageFourEquationMatrix_rank
        A x₀ m hm hA hvertex⟩
  · right
    have hexists : ∃ i₀ : Fin 4,
        integralTranslatedJoinVertexEvaluation A x₀ m i₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hvertex (funext h)
    obtain ⟨i₀, hi₀⟩ := hexists
    exact ⟨i₀, hi₀,
      integralTranslatedJoinImageThreeEquationMatrix_rank
        A x₀ m hm hA i₀ hi₀⟩

/-- Every supplied affine packet point projects into the integral
four-equation image kernel. -/
theorem integralTranslatedJoinImageFourEquationMatrix_mulVec_affinePoint
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ y : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (hvertex : integralTranslatedJoinVertexEvaluation A x₀ m = 0)
    (hy : A.map ((↑) : ℤ → ℚ) *ᵥ
      rationalHomogeneousAffinePoint y = 0) :
    (integralTranslatedJoinImageFourEquationMatrix A).map
        ((↑) : ℤ → ℚ) *ᵥ
      (fun j ↦ ((x₀ j + m * y j : ℤ) : ℚ)) = 0 := by
  rw [← translatedJoinProjectionFin_rationalHomogeneousAffinePoint]
  rw [integralTranslatedJoinImageFourEquationMatrix_map_intCast]
  apply translatedJoinImageFourEquationMatrixFin_mulVec_projection_eq_zero
    (A.map ((↑) : ℤ → ℚ))
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed]
    funext i
    rw [← integralTranslatedJoinVertexEvaluation_intCast]
    simp [hvertex]
  · exact hy

/-- Every supplied affine packet point projects into the integral
three-equation image kernel in the complementary branch. -/
theorem integralTranslatedJoinImageThreeEquationMatrix_mulVec_affinePoint
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ y : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : integralTranslatedJoinVertexEvaluation A x₀ m i₀ ≠ 0)
    (hy : A.map ((↑) : ℤ → ℚ) *ᵥ
      rationalHomogeneousAffinePoint y = 0) :
    (integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
        ((↑) : ℤ → ℚ) *ᵥ
      (fun j ↦ ((x₀ j + m * y j : ℤ) : ℚ)) = 0 := by
  rw [← translatedJoinProjectionFin_rationalHomogeneousAffinePoint]
  rw [integralTranslatedJoinImageThreeEquationMatrix_map_intCast]
  apply translatedJoinImageThreeEquationMatrixFin_mulVec_projection_eq_zero
    (A.map ((↑) : ℤ → ℚ))
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed,
      ← integralTranslatedJoinVertexEvaluation_intCast]
    exact_mod_cast hpivot
  · exact hy

/-- Projective point containment for the integral codimension-four image
matrix. -/
theorem integralProjectedPoint_mem_fourEquationProjectiveLinearSpace
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (hvertex : integralTranslatedJoinVertexEvaluation A x₀ m = 0)
    (v : Fin 14 → ℚ) (hAv : A.map ((↑) : ℤ → ℚ) *ᵥ v = 0)
    (hprojected : translatedJoinProjectionFin
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ) v ≠ 0) :
    Projectivization.mk ℚ
        (translatedJoinProjectionFin
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ) v) hprojected ∈
      rationalProjectiveLinearSpace
        ((integralTranslatedJoinImageFourEquationMatrix A).map
          ((↑) : ℤ → ℚ)) := by
  rw [integralTranslatedJoinImageFourEquationMatrix_map_intCast]
  apply (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
    _ _ hprojected).2
  apply translatedJoinImageFourEquationMatrixFin_mulVec_projection_eq_zero
    (A.map ((↑) : ℤ → ℚ))
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed]
    funext i
    rw [← integralTranslatedJoinVertexEvaluation_intCast]
    simp [hvertex]
  · exact hAv

/-- Projective point containment for the integral codimension-three image
matrix. -/
theorem integralProjectedPoint_mem_threeEquationProjectiveLinearSpace
    (A : Matrix (Fin 4) (Fin 14) ℤ)
    (x₀ : Fin 13 → ℤ) (m : ℤ) (hm : m ≠ 0)
    (i₀ : Fin 4)
    (hpivot : integralTranslatedJoinVertexEvaluation A x₀ m i₀ ≠ 0)
    (v : Fin 14 → ℚ) (hAv : A.map ((↑) : ℤ → ℚ) *ᵥ v = 0)
    (hprojected : translatedJoinProjectionFin
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ) v ≠ 0) :
    Projectivization.mk ℚ
        (translatedJoinProjectionFin
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ) v) hprojected ∈
      rationalProjectiveLinearSpace
        ((integralTranslatedJoinImageThreeEquationMatrix A x₀ m i₀).map
          ((↑) : ℤ → ℚ)) := by
  rw [integralTranslatedJoinImageThreeEquationMatrix_map_intCast]
  apply (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
    _ _ hprojected).2
  apply translatedJoinImageThreeEquationMatrixFin_mulVec_projection_eq_zero
    (A.map ((↑) : ℤ → ℚ))
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  · exact_mod_cast hm
  · rw [← translatedJoinVertexEvaluation_reindexed,
      ← integralTranslatedJoinVertexEvaluation_intCast]
    exact_mod_cast hpivot
  · exact hAv

end

end TranslatedDepthSeven
