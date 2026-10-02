import CubicTenVariables.FiniteKernelDuality
import CubicTenVariables.CubicTaylorExpansion
import Mathlib.Data.Nat.Prime.Basic

/-!
# Exact support of finite quadratic sums when two is invertible

Translation by a polar-kernel vector changes the sum by its literal linear
character. The displayed doubling identity forces the quadratic term to
vanish on that kernel. Finite pairing duality then places the support
inside the actual polar-matrix image. No residue-ring PID assumption is used.
-/

noncomputable section
namespace CubicTenVariables.QuadraticSumSupport
open scoped BigOperators Matrix
open FiniteKernelDuality QuadraticGaussBound

variable (q n : ℕ) [NeZero q]

/-- A quadratic function vanishes on its polar kernel if two is invertible. -/
theorem quadratic_eq_zero_on_kernel
    (Q : (Fin n → ZMod q) → ZMod q) (H : Matrix (Fin n) (Fin n) (ZMod q))
    (hQ2 : ∀ h, 2 * Q h = dotProduct h (H.mulVec h))
    (h2 : IsUnit (2 : ZMod q)) (h : Fin n → ZMod q) (hh : H.mulVec h = 0) :
    Q h = 0 := by
  apply h2.mul_right_eq_zero.mp
  rw [hQ2, hh, dotProduct_zero]

/-- Exact translation by a vector in the actual polar kernel. -/
theorem sum_eq_character_mul_of_kernel
    (Q : (Fin n → ZMod q) → ZMod q) (H : Matrix (Fin n) (Fin n) (ZMod q))
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + dotProduct x (H.mulVec h))
    (hQ2 : ∀ h, 2 * Q h = dotProduct h (H.mulVec h))
    (h2 : IsUnit (2 : ZMod q)) (ell : Fin n → ZMod q) (alpha : ZMod q)
    (h : Fin n → ZMod q) (hh : H.mulVec h = 0) :
    (∑ x : Fin n → ZMod q, ZMod.stdAddChar (dotProduct ell x + alpha * Q x)) =
      ZMod.stdAddChar (dotProduct ell h) *
        ∑ x : Fin n → ZMod q, ZMod.stdAddChar (dotProduct ell x + alpha * Q x) := by
  classical
  have hzero := quadratic_eq_zero_on_kernel q n Q H hQ2 h2 h hh
  calc
    _ = ∑ x : Fin n → ZMod q,
        ZMod.stdAddChar (dotProduct ell (x + h) + alpha * Q (x + h)) :=
      (Equiv.sum_comp (Equiv.addRight h)
        (fun x => ZMod.stdAddChar (dotProduct ell x + alpha * Q x))).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hQ, hh, hzero, dotProduct_zero, add_zero, add_zero, dotProduct_add]
      have he : dotProduct ell x + dotProduct ell h + alpha * Q x =
          dotProduct ell h + (dotProduct ell x + alpha * Q x) := by ring
      rw [he, AddChar.map_add_eq_mul]

/-- Nonvanishing forces the linear term to annihilate every kernel vector. -/
theorem annihilates_kernel_of_sum_ne_zero
    (Q : (Fin n → ZMod q) → ZMod q) (H : Matrix (Fin n) (Fin n) (ZMod q))
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + dotProduct x (H.mulVec h))
    (hQ2 : ∀ h, 2 * Q h = dotProduct h (H.mulVec h))
    (h2 : IsUnit (2 : ZMod q)) (ell : Fin n → ZMod q) (alpha : ZMod q)
    (hs : (∑ x : Fin n → ZMod q,
      ZMod.stdAddChar (dotProduct ell x + alpha * Q x)) ≠ 0) :
    ∀ h, H.mulVec h = 0 → dotProduct h ell = 0 := by
  intro h hh
  have he := sum_eq_character_mul_of_kernel q n Q H hQ hQ2 h2 ell alpha h hh
  have hc : ZMod.stdAddChar (dotProduct ell h) = 1 := by
    apply mul_right_cancel₀ hs
    simpa only [one_mul] using he.symm
  apply ZMod.injective_stdAddChar
  simpa only [dotProduct_comm h ell, AddChar.map_zero_eq_one] using hc

/-- The literal sum vanishes outside the actual transpose-matrix image. -/
theorem sum_eq_zero_of_not_mem_transpose_image
    (Q : (Fin n → ZMod q) → ZMod q) (H : Matrix (Fin n) (Fin n) (ZMod q))
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + dotProduct x (H.mulVec h))
    (hQ2 : ∀ h, 2 * Q h = dotProduct h (H.mulVec h))
    (h2 : IsUnit (2 : ZMod q)) (ell : Fin n → ZMod q) (alpha : ZMod q)
    (hell : ¬∃ x, H.transpose.mulVec x = ell) :
    (∑ x : Fin n → ZMod q, ZMod.stdAddChar (dotProduct ell x + alpha * Q x)) = 0 := by
  by_contra hs
  exact hell ((annihilates_kernel_iff_mem_range_transpose q n H ell).mp
    (annihilates_kernel_of_sum_ne_zero q n Q H hQ hQ2 h2 ell alpha hs))

/-- For a symmetric polar matrix, support is contained in its literal image. -/
theorem sum_eq_zero_of_not_mem_image
    (Q : (Fin n → ZMod q) → ZMod q) (H : Matrix (Fin n) (Fin n) (ZMod q))
    (hH : H.IsSymm)
    (hQ : ∀ x h, Q (x + h) = Q x + Q h + dotProduct x (H.mulVec h))
    (hQ2 : ∀ h, 2 * Q h = dotProduct h (H.mulVec h))
    (h2 : IsUnit (2 : ZMod q)) (ell : Fin n → ZMod q) (alpha : ZMod q)
    (hell : ¬∃ x, H.mulVec x = ell) :
    (∑ x : Fin n → ZMod q, ZMod.stdAddChar (dotProduct ell x + alpha * Q x)) = 0 := by
  apply sum_eq_zero_of_not_mem_transpose_image q n Q H hQ hQ2 h2 ell alpha
  simpa only [hH.eq] using hell

/-- The concrete scaled cubic quadratic term used by the high-terminal split.
Its actual polar matrix is `L • Hessian(F)(y)`, including nonunit `L`. -/
theorem cubic_quadratic_sum_eq_zero_of_not_mem_image
    (F : MvPolynomial (Fin n) (ZMod q)) (hF : F.IsHomogeneous 3)
    (y ell : Fin n → ZMod q) (L alpha : ZMod q) (h2 : IsUnit (2 : ZMod q))
    (hell : ¬∃ x, (L • HessianTheorem11.hessian F y).mulVec x = ell) :
    (∑ x : Fin n → ZMod q,
      ZMod.stdAddChar (dotProduct ell x + alpha * L * CubicTaylorExpansion.quadraticAt F y x)) = 0 := by
  have hH : (HessianTheorem11.hessian F y).IsSymm := HessianTheorem11.hessian_symmetric F y
  have hQ : ∀ x h, L * CubicTaylorExpansion.quadraticAt F y (x + h) =
      L * CubicTaylorExpansion.quadraticAt F y x +
      L * CubicTaylorExpansion.quadraticAt F y h +
      dotProduct x ((L • HessianTheorem11.hessian F y).mulVec h) := by
    intro x h
    rw [CubicTaylorExpansion.quadraticAt_add F hF, Matrix.smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have hQ2 : ∀ h, 2 * (L * CubicTaylorExpansion.quadraticAt F y h) =
      dotProduct h ((L • HessianTheorem11.hessian F y).mulVec h) := by
    intro h
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← CubicTaylorExpansion.two_mul_quadraticAt F hF]
    ring
  simpa only [mul_assoc] using sum_eq_zero_of_not_mem_image q n
    (fun x => L * CubicTaylorExpansion.quadraticAt F y x)
    (L • HessianTheorem11.hessian F y) (hH.smul L) hQ hQ2 h2 ell alpha hell

/-- The required invertibility of two for every odd prime power, including exponent zero. -/
theorem isUnit_two_primePower (p t : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    IsUnit (2 : ZMod (p^t)) := by
  apply (ZMod.isUnit_iff_coprime 2 (p^t)).mpr
  exact (hp.odd_of_ne_two hp2).coprime_two_left.pow_right t

end CubicTenVariables.QuadraticSumSupport
