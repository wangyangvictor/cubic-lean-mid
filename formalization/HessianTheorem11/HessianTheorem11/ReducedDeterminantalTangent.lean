import HessianTheorem11.ReducedDeterminantalDifferential
import HessianTheorem11.MatrixRankMinors
import HessianTheorem11.HessianDeterminant
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! The determinantal tangent input is proved from an actual bordered minor.
The argument works over every field, for arbitrary sets of rational points. -/
noncomputable section
namespace HessianTheorem11.ReducedDeterminantal
open MvPolynomial Matrix

variable {K : Type*} [Field K] {n m : ℕ}

def borderRows {r : ℕ} (u : Fin m → K) (rows : Fin r → Fin m) :
    Matrix (Unit ⊕ Fin r) (Fin m) K :=
  fun i k => Sum.elim (fun _ => u k) (fun j => if rows j = k then 1 else 0) i

def borderCols {r : ℕ} (v : Fin m → K) (cols : Fin r → Fin m) :
    Matrix (Fin m) (Unit ⊕ Fin r) K :=
  fun k j => Sum.elim (fun _ => v k) (fun i => if k = cols i then 1 else 0) j

def borderedPencil {r : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) (rows cols : Fin r → Fin m) :
    (Fin n → K) →ₗ[K] Matrix (Unit ⊕ Fin r) (Unit ⊕ Fin r) K where
  toFun z := borderRows u rows * (M z * borderCols v cols)
  map_add' z w := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c z := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem borderedPencil_inl_inl {r : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) (rows cols : Fin r → Fin m) (z : Fin n → K) :
    borderedPencil M u v rows cols z (Sum.inl ()) (Sum.inl ()) =
      dotProduct u ((M z).mulVec v) := by
  rfl

@[simp] theorem borderedPencil_inl_inr {r : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) (rows cols : Fin r → Fin m) (z : Fin n → K) (j : Fin r) :
    borderedPencil M u v rows cols z (Sum.inl ()) (Sum.inr j) =
      (u ᵥ* M z) (cols j) := by
  simp [borderedPencil, borderRows, borderCols, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, mul_ite]

@[simp] theorem borderedPencil_inr_inl {r : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) (rows cols : Fin r → Fin m) (z : Fin n → K) (i : Fin r) :
    borderedPencil M u v rows cols z (Sum.inr i) (Sum.inl ()) =
      (M z).mulVec v (rows i) := by
  simp [borderedPencil, borderRows, borderCols, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, ite_mul]

@[simp] theorem borderedPencil_inr_inr {r : ℕ}
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) (rows cols : Fin r → Fin m) (z : Fin n → K) (i j : Fin r) :
    borderedPencil M u v rows cols z (Sum.inr i) (Sum.inr j) =
      M z (rows i) (cols j) := by
  simp [borderedPencil, borderRows, borderCols, Matrix.mul_apply, ite_mul, mul_ite]

theorem tangent_left_right_kernel_pairing
    (M : (Fin n → K) →ₗ[K] Matrix (Fin m) (Fin m) K)
    (Z : Set (Fin n → K)) (x : Fin n → K)
    (hmax : ∀ y ∈ Z, (M y).rank ≤ (M x).rank)
    (t : Fin n → K) (ht : t ∈ affineTangentSpace Z x)
    (u v : Fin m → K) (hu : u ᵥ* M x = 0) (hv : (M x).mulVec v = 0) :
    dotProduct u ((M t).mulVec v) = 0 := by
  classical
  obtain ⟨rows, cols, hminor⟩ := MatrixRankMinors.exists_rank_minor (M x)
  let N := borderedPencil M u v rows cols
  let p := (pencilPolynomial N).det
  have heval (y : Fin n → K) : eval y p = (N y).det := by
    change eval y (pencilPolynomial N).det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact eval_pencilPolynomial N y i j
  have hp : p ∈ vanishingIdeal K Z := by
    intro y hy
    change eval y p = 0
    rw [heval]
    apply PolynomialSchurVanishing.det_eq_zero_of_rank_lt
    have hr : (N y).rank ≤ (M y).rank := by
      change (borderRows u rows * (M y * borderCols v cols)).rank ≤ _
      exact (rank_mul_le_right (borderRows u rows) (M y * borderCols v cols)).trans
        (rank_mul_le_left (M y) (borderCols v cols))
    have hc : Fintype.card (Unit ⊕ Fin (M x).rank) = (M x).rank + 1 := by simp; omega
    rw [hc]
    exact (hr.trans (hmax y hy)).trans_lt (Nat.lt_succ_self _)
  have hz := mem_affineTangentSpace.mp ht p hp
  change differentialAt x t (pencilPolynomial N).det = 0 at hz
  have hcol : ∀ i, eval x (pencilPolynomial N i (Sum.inl ())) = 0 := by
    intro i
    rw [eval_pencilPolynomial]
    rcases i with ⟨⟨⟩⟩ | i
    · simp [N, hv]
    · simp [N, hv]
  rw [differentialAt_det_zero_column _ x t (Sum.inl ()) hcol] at hz
  have hblock :
      (fun i j => if j = Sum.inl () then differentialAt x t (pencilPolynomial N i j)
        else eval x (pencilPolynomial N i j)) =
      fromBlocks
        (fun (_ _ : Unit) => dotProduct u ((M t).mulVec v))
        (0 : Matrix Unit (Fin (M x).rank) K)
        (fun (i : Fin (M x).rank) (_ : Unit) => (M t).mulVec v (rows i))
        ((M x).submatrix rows cols) := by
    ext i j
    rcases i with ⟨⟨⟩⟩ | i <;> rcases j with ⟨⟨⟩⟩ | j <;>
      simp [N, hu, Matrix.submatrix_apply]
  rw [hblock, det_fromBlocks_zero₁₂, det_unique] at hz
  exact (mul_eq_zero.mp hz).resolve_right hminor

end ReducedDeterminantal

/-- A theorem supplies the full determinantal tangent package over any field.
No algebraic-geometric input, infinitude, or characteristic assumption occurs. -/
theorem provedDeterminantalTangentOver (K : Type*) [Field K] : DeterminantalTangentOver K where
  tangent_kernel_pairing M hsym Z x _ hmax t ht u hu v hv := by
    apply ReducedDeterminantal.tangent_left_right_kernel_pairing M Z x hmax t ht u v
    · rw [← hsym x, Matrix.vecMul_transpose]
      exact hu
    · exact hv

/-- The geometric determinantal tangent package is now an unconditional theorem. -/
theorem provedSymmetricDeterminantalTangent : SymmetricDeterminantalTangentInput :=
  (provedDeterminantalTangentOver GeometricField).toGeometric

end HessianTheorem11
