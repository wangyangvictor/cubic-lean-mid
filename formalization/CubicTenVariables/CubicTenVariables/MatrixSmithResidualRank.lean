import CubicTenVariables.MatrixSmithKernel
import HessianTheorem11.MatrixRankBounds
import Mathlib.Logic.Equiv.Sum

/-!
# Residual Smith blocks and a fixed affine rank comparison

The translating matrix is constructed from integral changes of basis and
diagonal data before the perturbing matrix is chosen. Deleting the old rows
and columns costs at most twice their number. No symmetry, ordering of Smith
factors, or restriction on the characteristic is used.
-/

noncomputable section
namespace CubicTenVariables.MatrixSmithResidualRank

open Matrix

section Field
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Deleting the rows and columns outside a chosen subtype costs at most
twice the size of its complement. The matrix need not be symmetric. -/
theorem rank_le_tail_add_twice_complement (M : Matrix ι ι K)
    (P : ι → Prop) [DecidablePred P] :
    M.rank ≤ 2 * Fintype.card {i // ¬ P i} +
      (M.submatrix (Subtype.val : {i // P i} → ι)
        (Subtype.val : {i // P i} → ι)).rank := by
  classical
  let e := Equiv.sumCompl P
  let R := M.submatrix e e
  have h := HessianTheorem11.MatrixRankBounds.rank_fromBlocks_le
    R.toBlocks₁₁ R.toBlocks₁₂ R.toBlocks₂₁ R.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at h
  have hr : R.rank = M.rank := Matrix.rank_submatrix M e e
  have ht : R.toBlocks₁₁ = M.submatrix
      (Subtype.val : {i // P i} → ι) (Subtype.val : {i // P i} → ι) := rfl
  rw [hr, ht] at h
  omega

/-- Actual invertible row and column operations preserve matrix rank. -/
theorem rank_mul_units (M : Matrix ι ι K)
    (U V : (Matrix ι ι K)ˣ) :
    ((U : Matrix ι ι K) * M * V).rank = M.rank := by
  apply Nat.le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have h : M = (↑U⁻¹ : Matrix ι ι K) *
        ((U : Matrix ι ι K) * M * V) * (↑V⁻¹ : Matrix ι ι K) := by
      simp only [mul_assoc, Units.mul_inv, mul_one]
      rw [← mul_assoc, Units.inv_mul, one_mul]
    calc
      M.rank = ((↑U⁻¹ : Matrix ι ι K) *
          ((U : Matrix ι ι K) * M * V) * (↑V⁻¹ : Matrix ι ι K)).rank := congrArg Matrix.rank h
      _ ≤ ((U : Matrix ι ι K) * M * V).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- A fixed matrix transported back through actual invertible coordinates. -/
def inverseTransport (D : Matrix ι ι K) (U V : (Matrix ι ι K)ˣ) :
    Matrix ι ι K := (↑U⁻¹ : Matrix ι ι K) * D * (↑V⁻¹ : Matrix ι ι K)

theorem transport_inverseTransport_add (D B : Matrix ι ι K)
    (U V : (Matrix ι ι K)ˣ) :
    (U : Matrix ι ι K) * (inverseTransport D U V + B) * V =
      D + (U : Matrix ι ι K) * B * V := by
  simp only [inverseTransport, mul_add, add_mul, mul_assoc,
    Units.inv_mul, mul_one]
  simp only [← mul_assoc, Units.mul_inv, one_mul]

/-- The same translating matrix works for every perturbation. -/
theorem rank_inverseTransport_add_le (D B : Matrix ι ι K)
    (U V : (Matrix ι ι K)ˣ) (P : ι → Prop) [DecidablePred P] :
    (inverseTransport D U V + B).rank ≤ 2 * Fintype.card {i // ¬ P i} +
      ((D + (U : Matrix ι ι K) * B * V).submatrix
        (Subtype.val : {i // P i} → ι) (Subtype.val : {i // P i} → ι)).rank := by
  rw [← rank_mul_units (inverseTransport D U V + B) U V,
    transport_inverseTransport_add]
  exact rank_le_tail_add_twice_complement _ P

end Field

variable {n : ℕ}

/-- The indices whose diagonal entries are divisible by the full old modulus. -/
abbrev tailIndices (p m : ℕ) (d : Fin n → ℤ) :=
  {i : Fin n // (p : ℤ)^m ∣ d i}

/-- The complementary old indices. Zero diagonal entries are never old. -/
abbrev oldIndices (p m : ℕ) (d : Fin n → ℤ) :=
  {i : Fin n // ¬ (p : ℤ)^m ∣ d i}

/-- The literal one-digit residual matrix in the diagonal coordinates. -/
def residualMatrix (p m : ℕ) (d : Fin n → ℤ) (E : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (tailIndices p m d) (tailIndices p m d) (ZMod p) :=
  Matrix.diagonal (fun i : tailIndices p m d =>
    ((d i.val / (p : ℤ)^m : ℤ) : ZMod p)) +
      (E.map (Int.castRingHom (ZMod p))).submatrix Subtype.val Subtype.val

/-- The residual diagonal extended by zero on the old indices. -/
def residualDiagonal (p m : ℕ) (d : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  Matrix.diagonal (fun i => if (p : ℤ)^m ∣ d i then
    ((d i / (p : ℤ)^m : ℤ) : ZMod p) else 0)

/-- This matrix depends on the diagonal data and changes of basis, not on `B`. -/
def translatedMatrix (p m : ℕ) (d : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  (↑(MatrixSmithKernel.reduceUnit p U)⁻¹ : Matrix (Fin n) (Fin n) (ZMod p)) *
    residualDiagonal p m d *
      (↑(MatrixSmithKernel.reduceUnit p V)⁻¹ : Matrix (Fin n) (Fin n) (ZMod p))

theorem residualDiagonal_tail (p m : ℕ) (d : Fin n → ℤ) :
    (residualDiagonal p m d).submatrix
      (Subtype.val : tailIndices p m d → Fin n) Subtype.val =
      Matrix.diagonal (fun i : tailIndices p m d =>
        ((d i.val / (p : ℤ)^m : ℤ) : ZMod p)) := by
  rw [residualDiagonal, Matrix.submatrix_diagonal _ _ Subtype.val_injective]
  congr 1
  funext i
  simp only [Function.comp_apply, i.property, ↓reduceIte]

theorem tail_add_eq_residualMatrix (p m : ℕ) (d : Fin n → ℤ)
    (E : Matrix (Fin n) (Fin n) ℤ) :
    (residualDiagonal p m d + E.map (Int.castRingHom (ZMod p))).submatrix
      (Subtype.val : tailIndices p m d → Fin n) Subtype.val =
      residualMatrix p m d E := by
  change (residualDiagonal p m d).submatrix
      (Subtype.val : tailIndices p m d → Fin n) Subtype.val +
    (E.map (Int.castRingHom (ZMod p))).submatrix Subtype.val Subtype.val = _
  rw [residualDiagonal_tail]
  rfl

/-- Literal rank comparison over every prime field. Neither a Smith equation
nor a positive level is needed for this matrix inequality. In a Smith
application `E = U*B*V` and the displayed residual is exactly the tail block. -/
theorem rank_translatedMatrix_add_le (p m : ℕ) [Fact p.Prime]
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (B : Matrix (Fin n) (Fin n) ℤ) :
    (translatedMatrix p m d U V + B.map (Int.castRingHom (ZMod p))).rank ≤
      2 * Fintype.card (oldIndices p m d) +
        (residualMatrix p m d ((U : Matrix (Fin n) (Fin n) ℤ) * B * V)).rank := by
  have h := rank_inverseTransport_add_le (residualDiagonal p m d)
    (B.map (Int.castRingHom (ZMod p)))
    (MatrixSmithKernel.reduceUnit p U) (MatrixSmithKernel.reduceUnit p V)
    (fun i => (p : ℤ)^m ∣ d i)
  change (translatedMatrix p m d U V + B.map (Int.castRingHom (ZMod p))).rank ≤ _ at h
  simpa only [MatrixSmithKernel.reduceUnit_val, ← Matrix.map_mul,
    tail_add_eq_residualMatrix] using h

/-- The translating matrix is chosen before all integral perturbations. -/
theorem exists_translatedMatrix (p m : ℕ) [Fact p.Prime]
    (d : Fin n → ℤ) (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    ∃ T : Matrix (Fin n) (Fin n) (ZMod p),
      ∀ B : Matrix (Fin n) (Fin n) ℤ,
        (T + B.map (Int.castRingHom (ZMod p))).rank ≤
          2 * Fintype.card (oldIndices p m d) +
            (residualMatrix p m d ((U : Matrix (Fin n) (Fin n) ℤ) * B * V)).rank :=
  ⟨translatedMatrix p m d U V, rank_translatedMatrix_add_le p m d U V⟩

end CubicTenVariables.MatrixSmithResidualRank
