import TranslatedDepthSeven.IsolatedVertexQuotientPacketPlaneHeight
import TranslatedDepthSeven.ProjectiveLinearHeightBound
import TranslatedDepthSeven.JoinProjectionLinearSection

/-!
# Rational source sections from an isolated-vertex quotient plane

Let `A` be four integral homogeneous equations in quotient coordinates
`(s,z)`, let `b` be the integral translation base and let `m` be the
nonzero dilation.  Put

`beta_i = m A_{i0} - sum_j A_{i,j+1} b_j`.

If `beta=0`, the four spatial rows cut out the image plane.  If
`beta_{i0} != 0`, the three alternating combinations

`beta_{i0} A_{i,j+1} - beta_i A_{i0,j+1}`

cut out its span with the cone vertex.  A zero cone-coordinate column is
then prepended, and right multiplication by the fixed unimodular coordinate
change returns the section to the original source coordinates.

All matrices in this file are literal integral matrices.  Their entry,
rank-transport, and Plucker-height bounds are proved directly.  The one
remaining rank statement before the unimodular transport is isolated as a
pure finite-dimensional linear-algebra proposition; it contains no geometry
or counting assertion.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open Matrix

set_option maxHeartbeats 3000000

/-- The spatial twelve columns of four homogeneous quotient equations. -/
def integralQuotientSourceSpatialMatrix
    (A : Matrix (Fin 4) (Fin 13) ℤ) : Matrix (Fin 4) (Fin 12) ℤ :=
  fun i j ↦ A i j.succ

/-- Evaluation of the four quotient equations at the translated cone
vertex `(m,-b)`. -/
def integralQuotientSourceVertexEvaluation
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) : Fin 4 → ℤ :=
  fun i ↦ m * A i 0 -
    ∑ j, integralQuotientSourceSpatialMatrix A i j * b j

/-- The three spatial equations obtained by eliminating the homogenizing
coordinate against a row with nonzero vertex evaluation. -/
def integralQuotientSourceThreeEquationMatrix
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin 12) ℤ :=
  fun k j ↦
    integralQuotientSourceVertexEvaluation A b m i₀ *
        integralQuotientSourceSpatialMatrix A
          (finThreeEquivNonpivotRow i₀ k) j -
      integralQuotientSourceVertexEvaluation A b m
          (finThreeEquivNonpivotRow i₀ k) *
        integralQuotientSourceSpatialMatrix A i₀ j

/-- In transformed source coordinates, the codimension-four section has an
unused cone-coordinate column. -/
def integralQuotientSourceFourSectionMatrix
    (A : Matrix (Fin 4) (Fin 13) ℤ) : Matrix (Fin 4) (Fin 13) ℤ :=
  matrixPrependZeroColumn (integralQuotientSourceSpatialMatrix A)

/-- In transformed source coordinates, the codimension-three section also
has an unused cone-coordinate column. -/
def integralQuotientSourceThreeSectionMatrix
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) (i₀ : Fin 4) :
    Matrix (Fin 3) (Fin 13) ℤ :=
  matrixPrependZeroColumn
    (integralQuotientSourceThreeEquationMatrix A b m i₀)

/-- Return a transformed source section to the original coordinates.  Since
`U.pointEquiv x = U.forward * x`, a row equation `B y=0` becomes
`(B*U.forward) x=0`. -/
def integralQuotientOriginalSourceSectionMatrix {c : ℕ}
    (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ) : Matrix (Fin c) (Fin 13) ℤ :=
  B * U.forward

/-- Coefficient inclusion commutes with the displayed right matrix
multiplication. -/
theorem integralQuotientOriginalSourceSectionMatrix_map_intCast {c : ℕ}
    (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ) :
    (integralQuotientOriginalSourceSectionMatrix U B).map
        (Int.castRingHom ℚ) =
      B.map (Int.castRingHom ℚ) *
        U.forward.map (Int.castRingHom ℚ) := by
  exact Matrix.map_mul

/-- The fixed unimodular coordinate change is invertible after inclusion in
`Q`. -/
theorem integralUnimodularChange_forward_map_intCast_isUnit_det
    (U : IntegralUnimodularChange 13) :
    IsUnit (U.forward.map (Int.castRingHom ℚ)).det := by
  apply Matrix.isUnit_det_of_right_inverse
    (B := U.inverse.map (Int.castRingHom ℚ))
  rw [← Matrix.map_mul, U.forward_mul_inverse]
  simp

/-- Right multiplication by the fixed unimodular coordinate change
preserves the rank of every source section. -/
theorem integralQuotientOriginalSourceSectionMatrix_rank {c : ℕ}
    (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ) :
    ((integralQuotientOriginalSourceSectionMatrix U B).map
        (Int.castRingHom ℚ)).rank =
      (B.map (Int.castRingHom ℚ)).rank := by
  rw [integralQuotientOriginalSourceSectionMatrix_map_intCast]
  exact Matrix.rank_mul_eq_left_of_isUnit_det
    (U.forward.map (Int.castRingHom ℚ))
      (B.map (Int.castRingHom ℚ))
      (integralUnimodularChange_forward_map_intCast_isUnit_det U)

namespace StandardLinearAlgebra

/-- The elementary rank dichotomy for the two literal image matrices.  It
is Gaussian elimination on four independent rows: when all vertex
evaluations vanish the four spatial rows remain independent; after choosing
a nonzero evaluation, the three alternating rows are independent. -/
def IsolatedVertexQuotientSourceSectionRanks : Prop :=
  ∀ (A : Matrix (Fin 4) (Fin 13) ℤ) (b : IntVector 12) (m : ℤ),
    m ≠ 0 →
    (A.map (Int.castRingHom ℚ)).rank = 4 →
      (integralQuotientSourceVertexEvaluation A b m = 0 →
        ((integralQuotientSourceFourSectionMatrix A).map
          (Int.castRingHom ℚ)).rank = 4) ∧
      (∀ i₀ : Fin 4,
        integralQuotientSourceVertexEvaluation A b m i₀ ≠ 0 →
          ((integralQuotientSourceThreeSectionMatrix A b m i₀).map
            (Int.castRingHom ℚ)).rank = 3)

end StandardLinearAlgebra

/-- Every spatial entry is bounded by the corresponding bound for `A`. -/
theorem integralQuotientSourceSpatialMatrix_entry_natAbs_le
    {H : ℕ} (A : Matrix (Fin 4) (Fin 13) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (i : Fin 4) (j : Fin 12) :
    (integralQuotientSourceSpatialMatrix A i j).natAbs ≤ H :=
  hA i j.succ

/-- Elementary bound for each vertex evaluation. -/
theorem integralQuotientSourceVertexEvaluation_natAbs_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ j, (b j).natAbs ≤ X) (hm : m.natAbs ≤ M)
    (i : Fin 4) :
    (integralQuotientSourceVertexEvaluation A b m i).natAbs ≤
      (M + 12 * X) * H := by
  have hfirst : (m * A i 0).natAbs ≤ M * H := by
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul hm (hA i 0)
  have hsum :
      (∑ j, integralQuotientSourceSpatialMatrix A i j * b j).natAbs ≤
        12 * (H * X) := by
    calc
      (∑ j, integralQuotientSourceSpatialMatrix A i j * b j).natAbs ≤
          ∑ j, (integralQuotientSourceSpatialMatrix A i j * b j).natAbs :=
        int_natAbs_sum_le_sum_natAbs Finset.univ _
      _ ≤ ∑ _j : Fin 12, H * X := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul
          (integralQuotientSourceSpatialMatrix_entry_natAbs_le A hA i j)
          (hb j)
      _ = 12 * (H * X) := by simp
  rw [integralQuotientSourceVertexEvaluation]
  calc
    (m * A i 0 -
        ∑ j, integralQuotientSourceSpatialMatrix A i j * b j).natAbs ≤
      (m * A i 0).natAbs +
        (∑ j, integralQuotientSourceSpatialMatrix A i j * b j).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ M * H + 12 * (H * X) := Nat.add_le_add hfirst hsum
    _ = (M + 12 * X) * H := by ring

/-- Elementary coefficient bound for each eliminated equation. -/
theorem integralQuotientSourceThreeEquationMatrix_entry_natAbs_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) (i₀ : Fin 4)
    (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ j, (b j).natAbs ≤ X) (hm : m.natAbs ≤ M)
    (k : Fin 3) (j : Fin 12) :
    (integralQuotientSourceThreeEquationMatrix A b m i₀ k j).natAbs ≤
      2 * ((M + 12 * X) * H) * H := by
  rw [integralQuotientSourceThreeEquationMatrix]
  calc
    (integralQuotientSourceVertexEvaluation A b m i₀ *
          integralQuotientSourceSpatialMatrix A
            (finThreeEquivNonpivotRow i₀ k) j -
        integralQuotientSourceVertexEvaluation A b m
            (finThreeEquivNonpivotRow i₀ k) *
          integralQuotientSourceSpatialMatrix A i₀ j).natAbs ≤
      (integralQuotientSourceVertexEvaluation A b m i₀ *
          integralQuotientSourceSpatialMatrix A
            (finThreeEquivNonpivotRow i₀ k) j).natAbs +
        (integralQuotientSourceVertexEvaluation A b m
            (finThreeEquivNonpivotRow i₀ k) *
          integralQuotientSourceSpatialMatrix A i₀ j).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ ((M + 12 * X) * H) * H + ((M + 12 * X) * H) * H := by
      simp only [Int.natAbs_mul]
      exact Nat.add_le_add
        (Nat.mul_le_mul
          (integralQuotientSourceVertexEvaluation_natAbs_le
            A b m hA hb hm i₀)
          (integralQuotientSourceSpatialMatrix_entry_natAbs_le
            A hA (finThreeEquivNonpivotRow i₀ k) j))
        (Nat.mul_le_mul
          (integralQuotientSourceVertexEvaluation_natAbs_le
            A b m hA hb hm (finThreeEquivNonpivotRow i₀ k))
          (integralQuotientSourceSpatialMatrix_entry_natAbs_le A hA i₀ j))
    _ = 2 * ((M + 12 * X) * H) * H := by ring

/-- Prepending the zero cone-coordinate column does not change the spatial
entry bound. -/
theorem integralQuotientSourceFourSectionMatrix_entry_natAbs_le
    {H : ℕ} (A : Matrix (Fin 4) (Fin 13) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (i : Fin 4) (j : Fin 13) :
    (integralQuotientSourceFourSectionMatrix A i j).natAbs ≤ H := by
  cases j using Fin.cases with
  | zero => simp [integralQuotientSourceFourSectionMatrix,
      matrixPrependZeroColumn]
  | succ j =>
      exact integralQuotientSourceSpatialMatrix_entry_natAbs_le A hA i j

/-- The analogous bound for the codimension-three source section. -/
theorem integralQuotientSourceThreeSectionMatrix_entry_natAbs_le
    {H X M : ℕ} (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) (i₀ : Fin 4)
    (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ j, (b j).natAbs ≤ X) (hm : m.natAbs ≤ M)
    (k : Fin 3) (j : Fin 13) :
    (integralQuotientSourceThreeSectionMatrix A b m i₀ k j).natAbs ≤
      2 * ((M + 12 * X) * H) * H := by
  cases j using Fin.cases with
  | zero => simp [integralQuotientSourceThreeSectionMatrix,
      matrixPrependZeroColumn]
  | succ j =>
      exact integralQuotientSourceThreeEquationMatrix_entry_natAbs_le
        A b m i₀ hA hb hm k j

/-- Multiplying on the right by `U.forward` costs at most its maximum row
`l1` norm times the number of source coordinates.  This deliberately coarse
bound is uniform and completely explicit. -/
theorem integralQuotientOriginalSourceSectionMatrix_entry_natAbs_le
    {c H : ℕ} (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ)
    (hB : ∀ i j, (B i j).natAbs ≤ H) (i : Fin c) (j : Fin 13) :
    (integralQuotientOriginalSourceSectionMatrix U B i j).natAbs ≤
      13 * H * integralMatrixL1Norm U.forward := by
  have hentryU : ∀ k, (U.forward k j).natAbs ≤
      integralMatrixL1Norm U.forward := by
    intro k
    calc
      (U.forward k j).natAbs ≤ integralMatrixRowL1Norm U.forward k := by
        unfold integralMatrixRowL1Norm
        exact Finset.single_le_sum
          (fun l _hl ↦ Nat.zero_le (U.forward k l).natAbs)
          (Finset.mem_univ j)
      _ ≤ integralMatrixL1Norm U.forward :=
        integralMatrixRowL1Norm_le_integralMatrixL1Norm U.forward k
  change (∑ k, B i k * U.forward k j).natAbs ≤ _
  calc
    (∑ k, B i k * U.forward k j).natAbs ≤
        ∑ k, (B i k * U.forward k j).natAbs :=
      int_natAbs_sum_le_sum_natAbs Finset.univ _
    _ ≤ ∑ _k : Fin 13, H * integralMatrixL1Norm U.forward := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hB i k) (hentryU k)
    _ = 13 * H * integralMatrixL1Norm U.forward := by
      simp
      ring

/-- Plucker height of an arbitrary original-coordinate source section from
an entry bound in transformed coordinates. -/
theorem integralQuotientOriginalSourceSectionMatrix_height_le
    {c H : ℕ} (U : IntegralUnimodularChange 13)
    (B : Matrix (Fin c) (Fin 13) ℤ)
    (hB : ∀ i j, (B i j).natAbs ≤ H) :
    rationalProjectiveLinearHeight
        ((integralQuotientOriginalSourceSectionMatrix U B).map
          (Int.castRingHom ℚ)) ≤
      c.factorial *
        (13 * H * integralMatrixL1Norm U.forward) ^ c := by
  exact rationalProjectiveLinearHeight_map_intCast_le _
    (integralQuotientOriginalSourceSectionMatrix_entry_natAbs_le U B hB)

/-- Explicit original-coordinate codimension-four height bound. -/
theorem integralQuotientOriginalSourceFourSectionMatrix_height_le
    {H : ℕ} (U : IntegralUnimodularChange 13)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ H) :
    rationalProjectiveLinearHeight
        ((integralQuotientOriginalSourceSectionMatrix U
          (integralQuotientSourceFourSectionMatrix A)).map
            (Int.castRingHom ℚ)) ≤
      Nat.factorial 4 *
        (13 * H * integralMatrixL1Norm U.forward) ^ 4 := by
  exact integralQuotientOriginalSourceSectionMatrix_height_le U _
    (integralQuotientSourceFourSectionMatrix_entry_natAbs_le A hA)

/-- Explicit original-coordinate codimension-three height bound. -/
theorem integralQuotientOriginalSourceThreeSectionMatrix_height_le
    {H X M : ℕ} (U : IntegralUnimodularChange 13)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (b : IntVector 12) (m : ℤ) (i₀ : Fin 4)
    (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ j, (b j).natAbs ≤ X) (hm : m.natAbs ≤ M) :
    rationalProjectiveLinearHeight
        ((integralQuotientOriginalSourceSectionMatrix U
          (integralQuotientSourceThreeSectionMatrix A b m i₀)).map
            (Int.castRingHom ℚ)) ≤
      Nat.factorial 3 *
        (13 * (2 * ((M + 12 * X) * H) * H) *
          integralMatrixL1Norm U.forward) ^ 3 := by
  exact integralQuotientOriginalSourceSectionMatrix_height_le U _
    (integralQuotientSourceThreeSectionMatrix_entry_natAbs_le
      A b m i₀ hA hb hm)

/-- The pure rank premise plus the kernel-proved unimodular transport gives
the exact ranks of the original-coordinate section matrices. -/
theorem integralQuotientOriginalSourceSection_rank_dichotomy
    (hRank : StandardLinearAlgebra.IsolatedVertexQuotientSourceSectionRanks)
    (U : IntegralUnimodularChange 13)
    (A : Matrix (Fin 4) (Fin 13) ℤ) (b : IntVector 12) (m : ℤ)
    (hm : m ≠ 0) (hA : (A.map (Int.castRingHom ℚ)).rank = 4) :
    (integralQuotientSourceVertexEvaluation A b m = 0 →
      ((integralQuotientOriginalSourceSectionMatrix U
        (integralQuotientSourceFourSectionMatrix A)).map
          (Int.castRingHom ℚ)).rank = 4) ∧
    (∀ i₀ : Fin 4,
      integralQuotientSourceVertexEvaluation A b m i₀ ≠ 0 →
        ((integralQuotientOriginalSourceSectionMatrix U
          (integralQuotientSourceThreeSectionMatrix A b m i₀)).map
            (Int.castRingHom ℚ)).rank = 3) := by
  obtain ⟨hfour, hthree⟩ := hRank A b m hm hA
  constructor
  · intro hv
    rw [integralQuotientOriginalSourceSectionMatrix_rank]
    exact hfour hv
  · intro i₀ hpivot
    rw [integralQuotientOriginalSourceSectionMatrix_rank]
    exact hthree i₀ hpivot

end

end TranslatedDepthSeven
