import CubicTenVariables.QuadraticGaussBound
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The actual annihilator of a matrix kernel over a finite residue ring

A double sum of the literal standard additive character identifies the
annihilator of `ker H` with `image Hᵀ`. This holds at every positive modulus,
including composite/even moduli and modulus one. No normal-form theorem,
field assumption, or PID structure on the residue ring is required.
-/

noncomputable section
namespace CubicTenVariables.FiniteKernelDuality
open scoped BigOperators Matrix
open QuadraticGaussBound

variable (q n : ℕ) [NeZero q]

/-- The finite dot pairing transfers an actual matrix to its transpose. -/
theorem dot_mulVec_transpose (H : Matrix (Fin n) (Fin n) (ZMod q))
    (x y : Fin n → ZMod q) :
    dotProduct y (H.transpose.mulVec x) = dotProduct x (H.mulVec y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

/-- Exact double-character identity under the displayed annihilation property. -/
theorem double_sum_of_annihilates_kernel
    (H : Matrix (Fin n) (Fin n) (ZMod q)) (b : Fin n → ZMod q)
    (hb : ∀ y, H.mulVec y = 0 → dotProduct y b = 0) :
    (∑ x : Fin n → ZMod q, ∑ y : Fin n → ZMod q,
      ZMod.stdAddChar (dotProduct y (H.transpose.mulVec x - b))) =
      (q : ℂ)^n * (kernelVectors q n H).card := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ y : Fin n → ZMod q, ∑ x : Fin n → ZMod q,
        ZMod.stdAddChar (dotProduct y (H.transpose.mulVec x - b))) =
      ∑ y : Fin n → ZMod q, if H.mulVec y = 0 then (q : ℂ)^n else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp_rw [dotProduct_sub, sub_eq_add_neg, dot_mulVec_transpose,
        AddChar.map_add_eq_mul, ← Finset.sum_mul, sum_linear_phase]
      by_cases hy : H.mulVec y = 0
      · simp [hy, hb y hy]
      · simp [hy]
    _ = (q : ℂ)^n * (kernelVectors q n H).card := by
      simp [kernelVectors, ← Finset.sum_filter, mul_comm]

/-- The literal orthogonal complement of the actual kernel equals the
actual image of the transpose, for every positive modulus. -/
theorem annihilates_kernel_iff_mem_range_transpose
    (H : Matrix (Fin n) (Fin n) (ZMod q)) (b : Fin n → ZMod q) :
    (∀ y, H.mulVec y = 0 → dotProduct y b = 0) ↔
      ∃ x, H.transpose.mulVec x = b := by
  classical
  constructor
  · intro hb
    by_contra! hn
    have hzero : (∑ x : Fin n → ZMod q, ∑ y : Fin n → ZMod q,
        ZMod.stdAddChar (dotProduct y (H.transpose.mulVec x - b))) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [sum_linear_phase, if_neg (sub_ne_zero.mpr (hn x))]
    rw [double_sum_of_annihilates_kernel q n H b hb] at hzero
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    have hk : (kernelVectors q n H).card ≠ 0 := by
      apply Finset.card_ne_zero.mpr
      exact ⟨0, by simp [kernelVectors]⟩
    exact (mul_ne_zero (pow_ne_zero n hq) (by exact_mod_cast hk)) hzero
  · rintro ⟨x, rfl⟩ y hy
    rw [dot_mulVec_transpose, hy, dotProduct_zero]

/-- Symmetry identifies the transpose image with the image itself. -/
theorem annihilates_kernel_iff_mem_range
    (H : Matrix (Fin n) (Fin n) (ZMod q)) (hH : H.IsSymm)
    (b : Fin n → ZMod q) :
    (∀ y, H.mulVec y = 0 → dotProduct y b = 0) ↔ ∃ x, H.mulVec x = b := by
  simpa only [hH.eq] using annihilates_kernel_iff_mem_range_transpose q n H b

/-- The equality of actual subsets, with no supplied annihilator premise. -/
theorem kernel_orthogonal_eq_range
    (H : Matrix (Fin n) (Fin n) (ZMod q)) (hH : H.IsSymm) :
    {b | ∀ y, H.mulVec y = 0 → dotProduct y b = 0} = Set.range H.mulVec := by
  ext b
  exact annihilates_kernel_iff_mem_range q n H hH b

end CubicTenVariables.FiniteKernelDuality
