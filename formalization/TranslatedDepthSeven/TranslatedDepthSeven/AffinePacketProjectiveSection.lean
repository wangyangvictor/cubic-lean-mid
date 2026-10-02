import TranslatedDepthSeven.IntegralPacketSpanBasis
import TranslatedDepthSeven.JacobianCertificatePolynomialHeight
import TranslatedDepthSeven.ProjectiveAffineChange

/-!
# A projective linear section containing an affine packet

Let `B` be an integral `r` by `N` matrix of difference vectors and choose
an invertible `r` by `r` pivot minor.  The matrix
`C = cramerSpanEquationMatrix B J` annihilates every row of `B`.  This file
homogenizes those equations about an integral base point `y₀`:

`C * (X - X₀ y₀) = 0`.

The resulting integral matrix has `N-r` independent rows.  Every point
whose difference from `y₀` is a rational row combination of `B` gives a
point `[1:y]` in its projective kernel.  Its entries and primitive Plücker
height obey explicit elementary bounds.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization
open Matrix

/-- A fixed reindexing of the nonpivot coordinates by `Fin (N-r)`. -/
def finSubEquivMatrixNonpivot {r N : ℕ} (J : Fin r ↪ Fin N) :
    Fin (N - r) ≃ MatrixNonpivot J :=
  (Fintype.equivFinOfCardEq (card_matrixNonpivot J)).symm

/-- Before the harmless finite reindexing of its rows and columns, this is
the integral homogeneous equation matrix
`C * (X - X₀ y₀) = 0`. -/
def cramerAffineHomogeneousEquationMatrix {r N : ℕ}
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) :
    Matrix (MatrixNonpivot J) (Option (Fin N)) ℤ :=
  fun l q ↦
    match q with
    | none => -∑ j, cramerSpanEquationMatrix B J l j * y₀ j
    | some j => cramerSpanEquationMatrix B J l j

/-- The same equation matrix with the standard indices: rows are
`Fin (N-r)` and homogeneous coordinates are `Fin (N+1)`, with coordinate
zero corresponding to the homogenizing variable. -/
def cramerAffineProjectiveSectionMatrix {r N : ℕ}
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) :
    Matrix (Fin (N - r)) (Fin (N + 1)) ℤ :=
  (cramerAffineHomogeneousEquationMatrix y₀ B J).submatrix
    (finSubEquivMatrixNonpivot J) (finSuccEquiv N)

/-- The `Fin (N+1)` representative `(1,y)` of an affine integral point,
regarded over `ℚ`. -/
def rationalHomogeneousAffinePoint {N : ℕ} (y : Fin N → ℤ) :
    Fin (N + 1) → ℚ :=
  fun q ↦
    match finSuccEquiv N q with
    | none => 1
    | some j => (y j : ℚ)

/-- The displayed homogeneous representative is nonzero because its
homogenizing coordinate is one. -/
theorem rationalHomogeneousAffinePoint_ne_zero {N : ℕ} (y : Fin N → ℤ) :
    rationalHomogeneousAffinePoint y ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  simp [rationalHomogeneousAffinePoint] at h

/-- Reindexing the rows of the original Cramer matrix preserves their
linear independence. -/
theorem reindexedCramerSpanEquationMatrix_rows_linearIndependent
    {r N : ℕ} (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    LinearIndependent ℚ
      (fun i : Fin (N - r) ↦
        (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)).row
          (finSubEquivMatrixNonpivot J i)) :=
  (cramerSpanEquationMatrix_rows_linearIndependent B J hdet).comp
    (finSubEquivMatrixNonpivot J) (finSubEquivMatrixNonpivot J).injective

/-- Adding the homogenizing coefficient does not create a linear relation
among the Cramer equation rows. -/
theorem cramerAffineProjectiveSectionMatrix_rows_linearIndependent
    {r N : ℕ} (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    LinearIndependent ℚ
      (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)).row := by
  classical
  have hC := reindexedCramerSpanEquationMatrix_rows_linearIndependent B J hdet
  rw [Fintype.linearIndependent_iff] at hC ⊢
  intro g hg i
  apply hC g
  · funext j
    have hcoordinate := congrFun hg ((finSuccEquiv N).symm (some j))
    simpa [cramerAffineProjectiveSectionMatrix,
      cramerAffineHomogeneousEquationMatrix] using hcoordinate

/-- The homogeneous equation matrix has the expected full row rank `N-r`
over `ℚ`. -/
theorem cramerAffineProjectiveSectionMatrix_rank
    {r N : ℕ} (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
      ((↑) : ℤ → ℚ)).rank = N - r := by
  simpa using
    (cramerAffineProjectiveSectionMatrix_rows_linearIndependent
      y₀ B J hdet).rank_matrix

/-- When at least four Cramer equations are available, retain the first four
under the fixed reindexing `finSubEquivMatrixNonpivot`.  Since all Cramer
rows are independent, this is a literal codimension-four subsystem. -/
def fourRowCramerAffineProjectiveSectionMatrix
    {r N : ℕ} (hfour : 4 ≤ N - r)
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) : Matrix (Fin 4) (Fin (N + 1)) ℤ :=
  (cramerAffineProjectiveSectionMatrix y₀ B J).submatrix
    (Fin.castLE hfour) id

/-- The retained four homogeneous equations have rank four over `ℚ`. -/
theorem fourRowCramerAffineProjectiveSectionMatrix_rank
    {r N : ℕ} (hfour : 4 ≤ N - r)
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hdet : (selectedIntegralPivot B J).det ≠ 0) :
    (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J |>.map
      ((↑) : ℤ → ℚ)).rank = 4 := by
  have hlinear : LinearIndependent ℚ
      (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J |>.map
        ((↑) : ℤ → ℚ)).row := by
    simpa [fourRowCramerAffineProjectiveSectionMatrix] using
      (cramerAffineProjectiveSectionMatrix_rows_linearIndependent
        y₀ B J hdet).comp (Fin.castLE hfour)
          (Fin.castLE_injective hfour)
  simpa using hlinear.rank_matrix

/-- Restricting to four rows preserves every homogeneous-kernel equation. -/
theorem fourRowCramerAffineProjectiveSectionMatrix_mulVec_eq_zero
    {r N : ℕ} (hfour : 4 ≤ N - r)
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N) (v : Fin (N + 1) → ℚ)
    (hv : (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
      ((↑) : ℤ → ℚ)) *ᵥ v = 0) :
    (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J |>.map
      ((↑) : ℤ → ℚ)) *ᵥ v = 0 := by
  funext i
  have hi := congrFun hv (Fin.castLE hfour i)
  simpa [fourRowCramerAffineProjectiveSectionMatrix, Matrix.mulVec,
    dotProduct] using hi

/-- The standard homogeneous representative of the rational affine point
`y₀ + z`. -/
def rationalHomogeneousAffineTranslate {N : ℕ}
    (y₀ : Fin N → ℤ) (z : Fin N → ℚ) : Fin (N + 1) → ℚ :=
  fun q ↦
    match finSuccEquiv N q with
    | none => 1
    | some j => (y₀ j : ℚ) + z j

/-- Before reindexing, evaluation of the homogenized equations at
`[1:y₀+z]` is exactly `C*z`. -/
theorem cramerAffineHomogeneousEquationMatrix_mulVec_affineTranslate
    {r N : ℕ} (y₀ : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (z : Fin N → ℚ) :
    (cramerAffineHomogeneousEquationMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ
        (fun q ↦ match q with
          | none => 1
          | some j => (y₀ j : ℚ) + z j) =
      (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)) *ᵥ z := by
  classical
  funext l
  simp only [Matrix.map_apply, Matrix.mulVec, dotProduct,
    cramerAffineHomogeneousEquationMatrix, Fintype.sum_option,
    Int.cast_neg, Int.cast_sum, Int.cast_mul, mul_one]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- After the standard row and column reindexing, evaluation at
`[1:y₀+z]` remains `C*z`. -/
theorem cramerAffineProjectiveSectionMatrix_mulVec_affineTranslate
    {r N : ℕ} (y₀ : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (z : Fin N → ℚ) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ rationalHomogeneousAffineTranslate y₀ z =
      fun i ↦
        ((cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)) *ᵥ z)
          (finSubEquivMatrixNonpivot J i) := by
  change
    ((cramerAffineHomogeneousEquationMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)).submatrix
      (finSubEquivMatrixNonpivot J) (finSuccEquiv N)) *ᵥ
        rationalHomogeneousAffineTranslate y₀ z = _
  rw [Matrix.submatrix_mulVec_equiv]
  have hvector :
      rationalHomogeneousAffineTranslate y₀ z ∘ (finSuccEquiv N).symm =
        fun q ↦ match q with
          | none => 1
          | some j => (y₀ j : ℚ) + z j := by
    funext q
    cases q <;> simp [rationalHomogeneousAffineTranslate]
  rw [hvector,
    cramerAffineHomogeneousEquationMatrix_mulVec_affineTranslate y₀ B J z]
  rfl

/-- Evaluation of the homogeneous equations at `[1:y]` is exactly
`C * (y-y₀)`, up to the fixed row reindexing. -/
theorem cramerAffineProjectiveSectionMatrix_mulVec_affinePoint
    {r N : ℕ} (y₀ y : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ rationalHomogeneousAffinePoint y =
      fun i ↦
        ((cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)) *ᵥ
          (fun j ↦ ((y j - y₀ j : ℤ) : ℚ)))
            (finSubEquivMatrixNonpivot J i) := by
  let z : Fin N → ℚ := fun j ↦ ((y j - y₀ j : ℤ) : ℚ)
  have hpoint : rationalHomogeneousAffinePoint y =
      rationalHomogeneousAffineTranslate y₀ z := by
    funext q
    cases hq : finSuccEquiv N q with
    | none => simp [rationalHomogeneousAffinePoint,
        rationalHomogeneousAffineTranslate, hq]
    | some j =>
        simp [rationalHomogeneousAffinePoint,
          rationalHomogeneousAffineTranslate, z, hq]
  rw [hpoint]
  exact cramerAffineProjectiveSectionMatrix_mulVec_affineTranslate y₀ B J z

/-- Every rational row combination of `B` is annihilated by the Cramer
equation matrix. -/
theorem cramerSpanEquationMatrix_mulVec_rationalRowCombination_eq_zero
    {r N : ℕ} (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : Fin r → ℚ) :
    (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)) *ᵥ
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) = 0 := by
  have hproduct :
      (cramerSpanEquationMatrix B J |>.map ((↑) : ℤ → ℚ)) *
          (B.map ((↑) : ℤ → ℚ)).transpose = 0 := by
    ext l i
    have hrow := congrFun (cramerSpanEquationMatrix_mulVec_row_eq_zero B J i) l
    have hrowQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hrow
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using hrowQ
  rw [Matrix.mulVec_mulVec, hproduct, Matrix.zero_mulVec]

/-- The homogenized Cramer equations contain every point obtained from
`y₀` by a rational row combination of `B`. -/
theorem cramerAffineProjectiveSectionMatrix_mulVec_rowCombination_eq_zero
    {r N : ℕ} (y₀ : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : Fin r → ℚ) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ
      rationalHomogeneousAffineTranslate y₀
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) = 0 := by
  rw [cramerAffineProjectiveSectionMatrix_mulVec_affineTranslate]
  rw [cramerSpanEquationMatrix_mulVec_rationalRowCombination_eq_zero]
  rfl

/-- A supplied integral point lies in the homogeneous kernel whenever its
difference from `y₀` is the displayed rational row combination of `B`. -/
theorem cramerAffineProjectiveSectionMatrix_mulVec_packetPoint_eq_zero
    {r N : ℕ} (y₀ y : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : Fin r → ℚ)
    (hy : ∀ j,
      (y j : ℚ) = (y₀ j : ℚ) +
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) j) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ rationalHomogeneousAffinePoint y = 0 := by
  rw [show rationalHomogeneousAffinePoint y =
      rationalHomogeneousAffineTranslate y₀
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) by
    funext q
    cases hq : finSuccEquiv N q with
    | none => simp [rationalHomogeneousAffinePoint,
        rationalHomogeneousAffineTranslate, hq]
    | some j =>
        simp [rationalHomogeneousAffinePoint,
          rationalHomogeneousAffineTranslate, hq, hy j]]
  exact cramerAffineProjectiveSectionMatrix_mulVec_rowCombination_eq_zero
    y₀ B J a

/-- Coordinate-free span form of the packet-point statement.  This is the
direct interface with `IntegralPacketSpanBasis`: no row coefficients have to
be supplied by the caller. -/
theorem cramerAffineProjectiveSectionMatrix_mulVec_of_difference_mem_span
    {r N : ℕ} (y₀ y : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hy : rationalIntegralDifference y₀ y ∈
      Submodule.span ℚ
        (Set.range (B.map ((↑) : ℤ → ℚ)).row)) :
    (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
        ((↑) : ℤ → ℚ)) *ᵥ rationalHomogeneousAffinePoint y = 0 := by
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℚ).mp hy
  have hcombination :
      (B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a =
        rationalIntegralDifference y₀ y := by
    funext j
    have hj := congrFun ha j
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hj
  apply cramerAffineProjectiveSectionMatrix_mulVec_packetPoint_eq_zero
    y₀ y B J a
  intro j
  have hj := congrFun hcombination j
  rw [rationalIntegralDifference] at hj
  push_cast at hj
  linarith

/-- In projective language, the affine point `[1:y]` belongs to the
projective linear space cut out by the homogeneous Cramer equations. -/
theorem affineChartPoint_mem_cramerAffineProjectiveSection
    {r N : ℕ} (y₀ y : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : Fin r → ℚ)
    (hy : ∀ j,
      (y j : ℚ) = (y₀ j : ℚ) +
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) j) :
    Projectivization.mk ℚ (rationalHomogeneousAffinePoint y)
        (rationalHomogeneousAffinePoint_ne_zero y) ∈
      rationalProjectiveLinearSpace
        (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
          ((↑) : ℤ → ℚ)) := by
  exact
    (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
      _ _ (rationalHomogeneousAffinePoint_ne_zero y)).2
      (cramerAffineProjectiveSectionMatrix_mulVec_packetPoint_eq_zero
        y₀ y B J a hy)

/-- The same point lies in the fixed codimension-four subsystem whenever
`4 ≤ N-r`. -/
theorem affineChartPoint_mem_fourRowCramerAffineProjectiveSection
    {r N : ℕ} (hfour : 4 ≤ N - r)
    (y₀ y : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : Fin r → ℚ)
    (hy : ∀ j,
      (y j : ℚ) = (y₀ j : ℚ) +
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a) j) :
    Projectivization.mk ℚ (rationalHomogeneousAffinePoint y)
        (rationalHomogeneousAffinePoint_ne_zero y) ∈
      rationalProjectiveLinearSpace
        (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J |>.map
          ((↑) : ℤ → ℚ)) := by
  apply
    (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
      _ _ (rationalHomogeneousAffinePoint_ne_zero y)).2
  apply fourRowCramerAffineProjectiveSectionMatrix_mulVec_eq_zero
  exact cramerAffineProjectiveSectionMatrix_mulVec_packetPoint_eq_zero
    y₀ y B J a hy

/-- Simultaneous packet form of projective-kernel membership. -/
theorem packet_mem_cramerAffineProjectiveSection
    {index : Type*} {r N : ℕ}
    (y₀ : Fin N → ℤ) (y : index → Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (a : index → Fin r → ℚ)
    (hy : ∀ i j,
      (y i j : ℚ) = (y₀ j : ℚ) +
        ((B.map ((↑) : ℤ → ℚ)).transpose *ᵥ a i) j) :
    ∀ i,
      Projectivization.mk ℚ (rationalHomogeneousAffinePoint (y i))
          (rationalHomogeneousAffinePoint_ne_zero (y i)) ∈
        rationalProjectiveLinearSpace
          (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
            ((↑) : ℤ → ℚ)) := by
  intro i
  exact affineChartPoint_mem_cramerAffineProjectiveSection
    y₀ (y i) B J (a i) (hy i)

/-- Every member of a finite packet lies in the projective Cramer section
when the rows of `B` span the packet's rational difference space. -/
theorem finitePacket_mem_cramerAffineProjectiveSection_of_span_eq
    {r N : ℕ} (Z : Finset (IntVector N)) (base : IntVector N)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hspan : Submodule.span ℚ
        (Set.range (B.map ((↑) : ℤ → ℚ)).row) =
      Submodule.span ℚ
        (Set.range fun z : {z // z ∈ Z} ↦
          rationalIntegralDifference base z.1)) :
    ∀ z : {z // z ∈ Z},
      Projectivization.mk ℚ (rationalHomogeneousAffinePoint z.1)
          (rationalHomogeneousAffinePoint_ne_zero z.1) ∈
        rationalProjectiveLinearSpace
          (cramerAffineProjectiveSectionMatrix base B J |>.map
            ((↑) : ℤ → ℚ)) := by
  intro z
  apply
    (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
      _ _ (rationalHomogeneousAffinePoint_ne_zero z.1)).2
  apply cramerAffineProjectiveSectionMatrix_mulVec_of_difference_mem_span
  rw [hspan]
  exact Submodule.subset_span (Set.mem_range_self z)

/-- Fixed-codimension form: if `4 ≤ N-r`, the same finite packet lies in
the projective kernel of four independent Cramer equations. -/
theorem finitePacket_mem_fourRowCramerAffineProjectiveSection_of_span_eq
    {r N : ℕ} (hfour : 4 ≤ N - r)
    (Z : Finset (IntVector N)) (base : IntVector N)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hspan : Submodule.span ℚ
        (Set.range (B.map ((↑) : ℤ → ℚ)).row) =
      Submodule.span ℚ
        (Set.range fun z : {z // z ∈ Z} ↦
          rationalIntegralDifference base z.1)) :
    ∀ z : {z // z ∈ Z},
      Projectivization.mk ℚ (rationalHomogeneousAffinePoint z.1)
          (rationalHomogeneousAffinePoint_ne_zero z.1) ∈
        rationalProjectiveLinearSpace
          (fourRowCramerAffineProjectiveSectionMatrix hfour base B J |>.map
            ((↑) : ℤ → ℚ)) := by
  intro z
  apply
    (projectivization_mk_mem_rationalProjectiveLinearSpace_iff
      _ _ (rationalHomogeneousAffinePoint_ne_zero z.1)).2
  apply fourRowCramerAffineProjectiveSectionMatrix_mulVec_eq_zero
  apply cramerAffineProjectiveSectionMatrix_mulVec_of_difference_mem_span
  rw [hspan]
  exact Submodule.subset_span (Set.mem_range_self z)

/-- If `B` and `y₀` are bounded by `M` and `Y`, every entry of the
homogeneous equation matrix is bounded by
`(N*Y+1) * r! * M^r`. -/
theorem cramerAffineProjectiveSectionMatrix_entry_natAbs_le
    {r N M Y : ℕ} (y₀ : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M)
    (hy₀ : ∀ j, (y₀ j).natAbs ≤ Y)
    (i : Fin (N - r)) (q : Fin (N + 1)) :
    (cramerAffineProjectiveSectionMatrix y₀ B J i q).natAbs ≤
      (N * Y + 1) * (r.factorial * M ^ r) := by
  classical
  let l := finSubEquivMatrixNonpivot J i
  change (cramerAffineHomogeneousEquationMatrix y₀ B J l
    (finSuccEquiv N q)).natAbs ≤ _
  cases hq : finSuccEquiv N q with
  | none =>
      change (-∑ j, cramerSpanEquationMatrix B J l j * y₀ j).natAbs ≤ _
      rw [Int.natAbs_neg]
      calc
        (∑ j, cramerSpanEquationMatrix B J l j * y₀ j).natAbs ≤
            ∑ j, (cramerSpanEquationMatrix B J l j * y₀ j).natAbs := by
          simpa using
            int_natAbs_sum_le_sum_natAbs Finset.univ
              (fun j ↦ cramerSpanEquationMatrix B J l j * y₀ j)
        _ ≤ ∑ _j : Fin N, (r.factorial * M ^ r) * Y := by
          apply Finset.sum_le_sum
          intro j _hj
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul
            (cramerSpanEquationMatrix_entry_natAbs_le B J hB l j) (hy₀ j)
        _ = (N * Y) * (r.factorial * M ^ r) := by
          simp [mul_assoc, mul_comm]
        _ ≤ (N * Y + 1) * (r.factorial * M ^ r) := by
          exact Nat.mul_le_mul_right _ (Nat.le_succ (N * Y))
  | some j =>
      change (cramerSpanEquationMatrix B J l j).natAbs ≤ _
      exact (cramerSpanEquationMatrix_entry_natAbs_le B J hB l j).trans
        (by
          calc
            r.factorial * M ^ r = 1 * (r.factorial * M ^ r) := by simp
            _ ≤ (N * Y + 1) * (r.factorial * M ^ r) :=
              Nat.mul_le_mul_right _ (by omega))

/-- The resulting primitive Plücker height has the explicit determinant
bound obtained from the preceding entry estimate. -/
theorem cramerAffineProjectiveSectionMatrix_height_le
    {r N M Y : ℕ} (y₀ : Fin N → ℤ)
    (B : Matrix (Fin r) (Fin N) ℤ) (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M)
    (hy₀ : ∀ j, (y₀ j).natAbs ≤ Y) :
    rationalProjectiveLinearHeight
        (cramerAffineProjectiveSectionMatrix y₀ B J |>.map
          ((↑) : ℤ → ℚ)) ≤
      (N - r).factorial *
        ((N * Y + 1) * (r.factorial * M ^ r)) ^ (N - r) := by
  exact rationalProjectiveLinearHeight_map_intCast_le
    (cramerAffineProjectiveSectionMatrix y₀ B J)
    (cramerAffineProjectiveSectionMatrix_entry_natAbs_le y₀ B J hB hy₀)

/-- Every entry of the codimension-four subsystem has the same explicit
bound as the full Cramer equation matrix. -/
theorem fourRowCramerAffineProjectiveSectionMatrix_entry_natAbs_le
    {r N M Y : ℕ} (hfour : 4 ≤ N - r)
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M)
    (hy₀ : ∀ j, (y₀ j).natAbs ≤ Y)
    (i : Fin 4) (q : Fin (N + 1)) :
    (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J i q).natAbs ≤
      (N * Y + 1) * (r.factorial * M ^ r) := by
  exact cramerAffineProjectiveSectionMatrix_entry_natAbs_le
    y₀ B J hB hy₀ (Fin.castLE hfour i) q

/-- The four selected equations have the fixed-codimension Plücker bound
`4! ((N Y+1) r! M^r)^4`. -/
theorem fourRowCramerAffineProjectiveSectionMatrix_height_le
    {r N M Y : ℕ} (hfour : 4 ≤ N - r)
    (y₀ : Fin N → ℤ) (B : Matrix (Fin r) (Fin N) ℤ)
    (J : Fin r ↪ Fin N)
    (hB : ∀ i j, (B i j).natAbs ≤ M)
    (hy₀ : ∀ j, (y₀ j).natAbs ≤ Y) :
    rationalProjectiveLinearHeight
        (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J |>.map
          ((↑) : ℤ → ℚ)) ≤
      Nat.factorial 4 * ((N * Y + 1) * (r.factorial * M ^ r)) ^ 4 := by
  exact rationalProjectiveLinearHeight_map_intCast_le
    (fourRowCramerAffineProjectiveSectionMatrix hfour y₀ B J)
    (fourRowCramerAffineProjectiveSectionMatrix_entry_natAbs_le
      hfour y₀ B J hB hy₀)

end

end TranslatedDepthSeven
