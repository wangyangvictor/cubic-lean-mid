import CubicTenVariables.FixedIntegralSurfaceAffinePencil
import CubicTenVariables.SurfacePointCountByPlaneSlices
import CubicTenVariables.AffinePolynomialSlice
import CubicTenVariables.CubicGradientScaling

/-!
# Point counts for one fixed geometrically integral surface

The fixed projective pencil is assembled into one literal affine change of
the three spatial coordinates.  Its first two coordinates are the affine
coordinates on each plane and its last coordinate is the pencil parameter.
Thus the binary slices of the resulting three-variable polynomial are
definitionally the affine plane-curve fibers constructed in
`FixedIntegralSurfaceAffinePencil`.

The final bound uses only the two stated literature propositions:
`HomogeneousHypersurfaceIntegralityOpen`, to spread geometric integrality,
and `AffinePlaneCurveWeil`, to count the good plane-curve fibers.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedIntegralSurfacePointCount

open MvPolynomial
open HessianTheorem11
open HessianTheorem11.PolynomialRestriction
open BinarySliceCounting BinarySliceGeometry
open FixedIntegralSurfacePencil FixedIntegralSurfaceAffinePencil
open SurfacePointCountByPlaneSlices AffinePolynomialSlice
open scoped Classical

/-- The first two coordinates in the three-variable affine pencil. -/
def planeCoordinates : Fin 2 ↪ Fin 3 := Fin.castLEEmb (by omega)

/-- The unique remaining coordinate, namely the pencil parameter. -/
def parameterIndex : Complement planeCoordinates :=
  ⟨⟨2, by omega⟩, by
    rintro ⟨j, hj⟩
    have hval := congrArg Fin.val hj
    simp [planeCoordinates] at hval
    omega⟩

/-- Read the single pencil parameter from a complementary-coordinate
assignment. -/
def parameterValue {K : Type*} (w : Complement planeCoordinates → K) : K :=
  w parameterIndex

/-- The fixed affine base point: the first column of the integral frame. -/
def affineBase (C : Matrix (Fin 4) (Fin 3) ℤ) : Fin 4 → ℤ :=
  fun i ↦ C i 0

/-- The three spatial directions, with a zero zeroth row.  The columns are
the two directions inside a pencil plane followed by the pencil direction. -/
def affineDirections (C : Matrix (Fin 4) (Fin 3) ℤ) :
    Matrix (Fin 4) (Fin 3) ℤ :=
  fun i j ↦ Fin.cases 0 (fun r ↦ spatialPencilMatrix C r j) i

/-- The literal three-variable equation obtained from `F` by the fixed
affine spatial coordinate change. -/
def affineSurfacePolynomial
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ) :
    MvPolynomial (Fin 3) ℤ :=
  affineSlice F (affineDirections C) (affineBase C)

/-- The exceptional one-variable polynomial, renamed to the actual
complementary-coordinate type used by the slice-counting theorem. -/
def exceptionalPolynomial
    (g : MvPolynomial (Fin 1) ℤ) :
    MvPolynomial (Complement planeCoordinates) ℤ :=
  rename (fun _ ↦ parameterIndex) g

theorem complement_eq_parameterIndex
    (i : Complement planeCoordinates) : i = parameterIndex := by
  have hne0 : i.val.val ≠ 0 := by
    intro h
    apply i.property
    refine ⟨0, ?_⟩
    apply Fin.ext
    simp [planeCoordinates, h]
  have hne1 : i.val.val ≠ 1 := by
    intro h
    apply i.property
    refine ⟨1, ?_⟩
    apply Fin.ext
    simp [planeCoordinates, h]
  apply Subtype.ext
  apply Fin.ext
  change i.val.val = 2
  omega

@[simp] theorem parameterValue_const {K : Type*} (t : K) :
    parameterValue (fun _ ↦ t) = t := rfl

@[simp] theorem combine_planeCoordinates_zero
    {K : Type*} (z : Fin 2 → K)
    (w : Complement planeCoordinates → K) :
    combine planeCoordinates z w 0 = z 0 := by
  simpa [planeCoordinates] using
    (combine_selected planeCoordinates z w (0 : Fin 2))

@[simp] theorem combine_planeCoordinates_one
    {K : Type*} (z : Fin 2 → K)
    (w : Complement planeCoordinates → K) :
    combine planeCoordinates z w 1 = z 1 := by
  simpa [planeCoordinates] using
    (combine_selected planeCoordinates z w (1 : Fin 2))

@[simp] theorem combine_planeCoordinates_two
    {K : Type*} (z : Fin 2 → K)
    (w : Complement planeCoordinates → K) :
    combine planeCoordinates z w 2 = parameterValue w := by
  have h := combine_complement planeCoordinates z w (2 : Fin 3)
    parameterIndex.property
  change combine planeCoordinates z w 2 = w ⟨⟨2, by omega⟩,
    parameterIndex.property⟩ at h
  rw [h]
  exact congrArg w (complement_eq_parameterIndex _)

theorem exceptionalPolynomial_eval
    {K : Type*} [CommRing K]
    (g : MvPolynomial (Fin 1) ℤ)
    (w : Complement planeCoordinates → K) :
    eval w (map (Int.castRingHom K) (exceptionalPolynomial g)) =
      eval (fun _ : Fin 1 ↦ parameterValue w)
        (map (Int.castRingHom K) g) := by
  rw [exceptionalPolynomial, map_rename, eval_rename]
  rfl

theorem exceptionalPolynomial_map_ne_zero
    {K : Type*} [CommRing K]
    (g : MvPolynomial (Fin 1) ℤ)
    (hg : map (Int.castRingHom K) g ≠ 0) :
    map (Int.castRingHom K) (exceptionalPolynomial g) ≠ 0 := by
  rw [exceptionalPolynomial, map_rename]
  intro hz
  apply hg
  apply (rename_injective (R := K) (fun _ : Fin 1 ↦ parameterIndex)
    (fun _ _ _ ↦ Subsingleton.elim _ _))
  simpa only [map_zero] using hz

theorem exceptionalPolynomial_totalDegree_le
    {K : Type*} [CommRing K]
    (g : MvPolynomial (Fin 1) ℤ) :
    (map (Int.castRingHom K) (exceptionalPolynomial g)).totalDegree ≤
      g.totalDegree := by
  rw [exceptionalPolynomial, map_rename]
  exact (totalDegree_rename_le _ _).trans
    (Finset.sup_mono (support_map_subset (Int.castRingHom K) g))

/-- The affine change does not increase the degree of the surface equation. -/
theorem affineSurfacePolynomial_totalDegree_le
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ) :
    (affineSurfacePolynomial F C).totalDegree ≤ F.totalDegree :=
  totalDegree_affineSlice_le F (affineDirections C) (affineBase C)

/-- Every binary slice of the three-variable surface polynomial is the
literal specialized affine curve in the fixed pencil. -/
theorem slice_affineSurfacePolynomial
    {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hC01 : C 0 1 = 0) (hC02 : C 0 2 = 0)
    (w : Complement planeCoordinates → K) :
    BinarySliceGeometry.slice planeCoordinates
        (map (Int.castRingHom K) (affineSurfacePolynomial F C)) w =
      map (eval₂Hom (Int.castRingHom K)
          (fun _ : Fin 1 ↦ parameterValue w))
        (affineCurveFamily F C) := by
  unfold affineSurfacePolynomial
  rw [map_affineSlice]
  rw [specialize_affineCurveFamily]
  unfold BinarySliceGeometry.slice
  change aeval (combine planeCoordinates X (fun i ↦ MvPolynomial.C (w i)))
      (aeval (fun i ↦ MvPolynomial.C (((affineBase C i : ℤ) : K)) +
        linearForms ((affineDirections C).map (Int.castRingHom K)) i)
        (map (Int.castRingHom K) F)) =
    aeval (Fin.cases 1 X)
      (aeval (linearForms (pencilFrame C (parameterValue w)))
        (map (Int.castRingHom K) F))
  rw [comp_aeval_apply, comp_aeval_apply]
  apply congrArg (fun q : Fin 4 → MvPolynomial (Fin 2) K ↦
    aeval q (map (Int.castRingHom K) F))
  funext i
  refine Fin.cases ?_ (fun r ↦ ?_) i
  · simp [affineBase, affineDirections, linearForms, planeCoordinates,
      parameterValue, spatialPencilMatrix, spatialDirections, pencilFrame,
      parameterIndex, hC01, hC02, Fin.sum_univ_succ]
  · simp [affineBase, affineDirections, linearForms,
      parameterValue, spatialPencilMatrix, spatialDirections, pencilFrame,
      parameterIndex, Fin.sum_univ_succ]
    have hcase1 : Fin.cases (1 : MvPolynomial (Fin 2) K) X (1 : Fin 3) = X 0 := rfl
    have hcase2 : Fin.cases (1 : MvPolynomial (Fin 2) K) X (2 : Fin 3) = X 1 := rfl
    rw [hcase1, hcase2]
    ring

/-- Every member of the literal affine pencil has degree at most the degree
of the original homogeneous surface, including exceptional fibers. -/
theorem affineCurveFiber_totalDegree_le
    {K : Type*} [CommRing K] {d : ℕ}
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hC01 : C 0 1 = 0) (hC02 : C 0 2 = 0)
    (hF : F.IsHomogeneous d) (t : K) :
    (map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 ↦ t))
      (affineCurveFamily F C)).totalDegree ≤ d := by
  let w : Complement planeCoordinates → K := fun _ ↦ t
  have hs := slice_affineSurfacePolynomial F C hC01 hC02 w
  have hs' : BinarySliceGeometry.slice planeCoordinates
      (map (Int.castRingHom K) (affineSurfacePolynomial F C)) w =
      map (eval₂Hom (Int.castRingHom K) (fun _ : Fin 1 ↦ t))
        (affineCurveFamily F C) := by
    simpa only [w, parameterValue_const] using hs
  rw [← hs']
  exact (totalDegree_slice_le planeCoordinates
    (map (Int.castRingHom K) (affineSurfacePolynomial F C)) w).trans
      ((Finset.sup_mono (support_map_subset (Int.castRingHom K)
        (affineSurfacePolynomial F C))).trans
        ((affineSurfacePolynomial_totalDegree_le F C).trans hF.totalDegree_le))

/-- Evaluation of the transformed equation is evaluation of `F` on the
actual fixed affine chart `x₀=C₀₀`, after the displayed spatial affine
change of coordinates. -/
theorem eval_affineSurfacePolynomial
    {K : Type*} [CommRing K]
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (y : Fin 3 → K) :
    eval y (map (Int.castRingHom K) (affineSurfacePolynomial F C)) =
      eval (Fin.cases (C 0 0 : K) (fun r ↦
        (C r.succ 0 : K) +
          ((spatialPencilMatrix C).map (Int.castRingHom K)).mulVec y r))
        (map (Int.castRingHom K) F) := by
  unfold affineSurfacePolynomial
  rw [map_affineSlice, eval_affineSlice]
  apply congrArg (fun q : Fin 4 → K ↦
    eval q (map (Int.castRingHom K) F))
  funext i
  refine Fin.cases ?_ (fun r ↦ ?_) i
  · simp [affineBase, affineDirections, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]
  · simp [affineBase, affineDirections, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The spatial affine map used above is bijective whenever the fixed
pencil determinant stays nonzero. -/
theorem spatialAffineMap_bijective
    {K : Type*} [Field K]
    (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hdet : ((spatialPencilMatrix C).det : K) ≠ 0) :
    Function.Bijective (fun y : Fin 3 → K ↦
      (fun r ↦ (C r.succ 0 : K)) +
        ((spatialPencilMatrix C).map (Int.castRingHom K)).mulVec y) := by
  let U : Matrix (Fin 3) (Fin 3) K :=
    (spatialPencilMatrix C).map (Int.castRingHom K)
  have hdetU : U.det ≠ 0 := by
    have hm := (Int.castRingHom K).map_det (spatialPencilMatrix C)
    change (Int.castRingHom K) (spatialPencilMatrix C).det = U.det at hm
    exact fun hz ↦ hdet (hm.trans hz)
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hdetU)
  have hinj : Function.Injective U.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hsurj : Function.Surjective U.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  constructor
  · intro x y hxy
    apply hinj
    exact add_left_cancel hxy
  · intro x
    obtain ⟨y, hy⟩ := hsurj (x - fun r ↦ (C r.succ 0 : K))
    refine ⟨y, ?_⟩
    change (fun r ↦ (C r.succ 0 : K)) + U.mulVec y = x
    rw [hy]
    exact add_sub_cancel _ _

/-- The transformed zero count is exactly the zero count on the original
fixed affine chart. -/
theorem affineSurface_zero_count_eq_chart_zero_count
    {K : Type*} [Field K] [Fintype K]
    (F : MvPolynomial (Fin 4) ℤ) (C : Matrix (Fin 4) (Fin 3) ℤ)
    (hdet : ((spatialPencilMatrix C).det : K) ≠ 0) :
    Nat.card {y : Fin 3 → K //
        eval y (map (Int.castRingHom K) (affineSurfacePolynomial F C)) = 0} =
      Nat.card {x : Fin 3 → K //
        eval (Fin.cases (C 0 0 : K) x) (map (Int.castRingHom K) F) = 0} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  rw [show (Finset.univ.filter fun y : Fin 3 → K ↦
      eval y (map (Int.castRingHom K) (affineSurfacePolynomial F C)) = 0) =
      Finset.univ.filter fun y : Fin 3 → K ↦
        eval (Fin.cases (C 0 0 : K)
          ((fun r ↦ (C r.succ 0 : K)) +
            ((spatialPencilMatrix C).map (Int.castRingHom K)).mulVec y))
          (map (Int.castRingHom K) F) = 0 by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [eval_affineSurfacePolynomial]
    rfl]
  exact BinarySliceCounting.card_filter_comp_bijective _
    (spatialAffineMap_bijective C hdet)
    (fun x : Fin 3 → K ↦
      eval (Fin.cases (C 0 0 : K) x) (map (Int.castRingHom K) F) = 0)

/-- Multiplication of every spatial coordinate by a nonzero field element
is a bijection. -/
theorem spatialScalarMap_bijective
    {K : Type*} [Field K] (a : K) (ha : a ≠ 0) :
    Function.Bijective (fun x : Fin 3 → K ↦ a • x) := by
  constructor
  · intro x y hxy
    funext i
    have hi := congrFun hxy i
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (mul_left_cancel₀ ha hi)
  · intro x
    refine ⟨a⁻¹ • x, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- For a homogeneous equation, any nonzero constant projective chart has
exactly the same number of points as the standard chart `x₀=1`. -/
theorem chart_zero_count_eq_standard_chart_zero_count
    {K : Type*} [Field K] [Fintype K]
    {d : ℕ} (F : MvPolynomial (Fin 4) ℤ) (hF : F.IsHomogeneous d)
    (a : K) (ha : a ≠ 0) :
    Nat.card {x : Fin 3 → K //
        eval (Fin.cases a x) (map (Int.castRingHom K) F) = 0} =
      Nat.card {x : Fin 3 → K //
        eval (Fin.cases 1 x) (map (Int.castRingHom K) F) = 0} := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Fintype.card_subtype]
  let P : (Fin 3 → K) → Prop := fun x ↦
    eval (Fin.cases a x) (map (Int.castRingHom K) F) = 0
  let Q : (Fin 3 → K) → Prop := fun x ↦
    eval (Fin.cases 1 x) (map (Int.castRingHom K) F) = 0
  have hchange := BinarySliceCounting.card_filter_comp_bijective
    (fun x : Fin 3 → K ↦ a • x) (spatialScalarMap_bijective a ha) P
  have hpq (x : Fin 3 → K) : P (a • x) ↔ Q x := by
    have hcoord : Fin.cases a (a • x) =
        a • (Fin.cases 1 x : Fin 4 → K) := by
      funext i
      refine Fin.cases ?_ (fun r ↦ ?_) i
      · simp
      · simp
    change eval (Fin.cases a (a • x)) (map (Int.castRingHom K) F) = 0 ↔
      eval (Fin.cases 1 x) (map (Int.castRingHom K) F) = 0
    rw [hcoord]
    rw [← eval₂_eq_eval_map, ← eval₂_eq_eval_map,
      CubicGradientScaling.homogeneous_eval₂_smul F hF
        (Int.castRingHom K) (Fin.cases 1 x) a, mul_eq_zero]
    simp only [pow_ne_zero d ha, false_or]
  have hfilter : (Finset.univ.filter fun x : Fin 3 → K ↦ P (a • x)) =
      Finset.univ.filter Q := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpq x
  have hcards : (Finset.univ.filter P).card =
      (Finset.univ.filter Q).card :=
    hchange.symm.trans (congrArg Finset.card hfilter)
  simpa only [P, Q] using hcards

/-- A fixed geometrically integral homogeneous surface has leading-one
point count on its displayed nonzero affine chart over every sufficiently
large finite field away from one displayed integer.  The threshold is
literal and depends only on the fixed surface, its fixed pencil, the degree,
and the chosen leading constant `K₀>1`. -/
theorem exists_fixed_integral_surface_point_count
    (integralityOpen : Literature.HomogeneousHypersurfaceIntegralityOpen)
    (curveWeil : Literature.AffinePlaneCurveWeil)
    {d : ℕ} (hd : 2 ≤ d)
    (F : MvPolynomial (Fin 4) ℤ) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous d)
    (hgeom : IsDomain (MvPolynomial (Fin 4) GeometricField ⧸
      Ideal.span {map (Int.castRingHom GeometricField) F}))
    (K₀ : ℝ) (hK₀ : 1 < K₀) :
    ∃ (C : Matrix (Fin 4) (Fin 3) ℤ) (N : ℤ)
        (g : MvPolynomial (Fin 1) ℤ),
      C 0 0 ≠ 0 ∧ C 0 1 = 0 ∧ C 0 2 = 0 ∧ N ≠ 0 ∧
      ∀ (K : Type) [Field K] [Fintype K], (N : K) ≠ 0 →
        surfaceSliceThreshold curveWeil d (by omega) g.totalDegree K₀ ≤
          (Fintype.card K : ℝ) →
        (Nat.card {x : Fin 3 → K //
          eval (Fin.cases 1 x) (map (Int.castRingHom K) F) = 0} : ℝ) ≤
          K₀ * (Fintype.card K : ℝ) ^ 2 := by
  obtain ⟨C, N, g, hC00, hC01, hC02, hN, hcert⟩ :=
    exists_fixed_integral_affine_pencil_certificate
      integralityOpen hd F hF0 hF hgeom
  refine ⟨C, N, g, hC00, hC01, hC02, hN, ?_⟩
  intro K _ _ hNK hcard
  obtain ⟨hC00K, hdet, hgK, hall, hgood⟩ := hcert K hNK
  let fK := map (Int.castRingHom K) (affineSurfacePolynomial F C)
  let gK := map (Int.castRingHom K) (exceptionalPolynomial g)
  have hfdeg : fK.totalDegree ≤ d := by
    dsimp only [fK]
    exact (Finset.sup_mono (support_map_subset (Int.castRingHom K)
      (affineSurfacePolynomial F C))).trans
      ((affineSurfacePolynomial_totalDegree_le F C).trans hF.totalDegree_le)
  have hgdeg : gK.totalDegree ≤ g.totalDegree := by
    exact exceptionalPolynomial_totalDegree_le g
  have hg : gK ≠ 0 := exceptionalPolynomial_map_ne_zero g hgK
  have hslice (w : Complement planeCoordinates → K) :
      slice planeCoordinates fK w =
        map (eval₂Hom (Int.castRingHom K)
          (fun _ : Fin 1 ↦ parameterValue w)) (affineCurveFamily F C) := by
    exact slice_affineSurfacePolynomial F C hC01 hC02 w
  have hall' : ∀ w : Complement planeCoordinates → K,
      slice planeCoordinates fK w ≠ 0 := by
    intro w
    rw [hslice w]
    exact hall (parameterValue w)
  have hgoodDegree : ∀ w : Complement planeCoordinates → K,
      eval w gK ≠ 0 → 1 ≤ (slice planeCoordinates fK w).totalDegree := by
    intro w hw
    rw [hslice w]
    exact (hgood (parameterValue w)
      (by simpa only [gK, exceptionalPolynomial_eval] using hw)).1
  have hgoodIntegral : ∀ w : Complement planeCoordinates → K,
      eval w gK ≠ 0 →
      IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure K) ⧸
        Ideal.span {map (algebraMap K (AlgebraicClosure K))
          (slice planeCoordinates fK w)}) := by
    intro w hw
    rw [hslice w]
    exact (hgood (parameterValue w)
      (by simpa only [gK, exceptionalPolynomial_eval] using hw)).2
  have hcount := surface_zero_count_le_K_mul_sq_of_card_ge
    curveWeil d (by omega) planeCoordinates fK gK g.totalDegree hgdeg
      hfdeg hg hall' hgoodDegree hgoodIntegral K₀ hK₀ hcard
  rw [affineSurface_zero_count_eq_chart_zero_count F C hdet] at hcount
  rw [chart_zero_count_eq_standard_chart_zero_count F hF (C 0 0 : K) hC00K]
    at hcount
  exact hcount

end CubicTenVariables.FixedIntegralSurfacePointCount
