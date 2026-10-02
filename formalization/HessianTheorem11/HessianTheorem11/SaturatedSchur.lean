import HessianTheorem11.PolynomialSchurVanishing
import HessianTheorem11.SchurSecondOrder
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Exact block elimination for the saturated incidence pencil. All three
remainder blocks meeting the final normal space are retained. -/
noncomputable section
namespace HessianTheorem11.SaturatedSchur
open Matrix

variable {R α β : Type*} [CommRing R] [Fintype α] [Fintype β]

/-- A zero final diagonal block in the inverse forces the first Schur block
to vanish. The two final blocks have equal size; no remainder is suppressed. -/
theorem schur_zero_of_inverse_final_zero [DecidableEq α] [DecidableEq β]
    (B B' : Matrix α α R) (hB : B' * B = 1)
    (F H : Matrix α β R) (E I : Matrix β α R)
    (C L M N : Matrix β β R)
    (J : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) R)
    (hG : Matrix.fromBlocks B (Matrix.fromCols F H) (Matrix.fromRows E I)
      (Matrix.fromBlocks C L M N) * J = 1)
    (hDD : J.submatrix (fun i => Sum.inr (Sum.inr i))
      (fun i => Sum.inr (Sum.inr i)) = 0) :
    C - E * B' * F = 0 := by
  let U := J.submatrix Sum.inl (fun i => Sum.inr (Sum.inr i))
  let V := J.submatrix (fun i => Sum.inr (Sum.inl i))
    (fun i => Sum.inr (Sum.inr i))
  have hzero (i j : β) : J (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = 0 :=
    congrFun (congrFun hDD i) j
  have h1 : B * U + F * V = 0 := by
    ext i j
    have h := congrFun (congrFun hG (Sum.inl i)) (Sum.inr (Sum.inr j))
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, U, V, hzero] using h
  have h2 : E * U + C * V = 0 := by
    ext i j
    have h := congrFun (congrFun hG (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr j))
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, U, V, hzero] using h
  have h3 : I * U + M * V = 1 := by
    ext i j
    have h := congrFun (congrFun hG (Sum.inr (Sum.inr i))) (Sum.inr (Sum.inr j))
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, U, V, hzero, Matrix.one_apply] using h
  have hU : U = -(B' * F * V) := by
    have hh := congrArg (fun W => B' * W) h1
    simpa [Matrix.mul_add, ← Matrix.mul_assoc, hB, eq_neg_iff_add_eq_zero] using hh
  have hCV : (C - E * B' * F) * V = 0 := by
    rw [hU] at h2
    simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_eq_sub,
      Matrix.sub_mul] using h2
  have hMV : (M - I * B' * F) * V = 1 := by
    rw [hU] at h3
    simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_eq_sub,
      Matrix.sub_mul] using h3
  have hVM := Matrix.mul_eq_one_comm.mp hMV
  calc
    C - E * B' * F = (C - E * B' * F) * (V * (M - I * B' * F)) := by rw [hVM, Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, hCV, Matrix.zero_mul]

/-- A left inverse of the normal Jacobian cancels the two exterior factors. -/
theorem cancel_outer_of_left_inverse [DecidableEq β]
    (P : Matrix α β R) (L : Matrix β α R) (hLP : L * P = 1)
    (D : Matrix β β R) (h : P * D * P.transpose = 0) : D = 0 := by
  have ht : P.transpose * L.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hLP
  calc
    D = L * (P * D * P.transpose) * L.transpose := by
      simp only [← Matrix.mul_assoc, hLP, Matrix.one_mul]
      rw [Matrix.mul_assoc, ht, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

end HessianTheorem11.SaturatedSchur
