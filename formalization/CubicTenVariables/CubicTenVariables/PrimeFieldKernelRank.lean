import CubicTenVariables.HessianKernelCRT
import HessianTheorem11.HessianLinearity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-! Exact cardinalities of the actual prime-field matrix kernel, using
rank-nullity. The Hessian is the actual reduced polynomial Hessian. -/

noncomputable section
namespace CubicTenVariables.PrimeFieldKernelRank
open MvPolynomial HessianTheorem11 HessianKernelCRT

variable {n p : ℕ}

/-- Rank-nullity and the cardinality of a finite-dimensional vector space,
applied to the literal coefficient matrix equation. -/
theorem card_kernel_eq_pow_finrank {K : Type*} [Field K]
    (B : Matrix (Fin n) (Fin n) K) :
    Nat.card {z : Fin n → K // B.mulVec z = 0} = (Nat.card K)^(n-B.rank) := by
  change Nat.card (LinearMap.ker B.mulVecLin) = _
  rw [Module.natCard_eq_pow_finrank (K := K)]
  congr 1
  have hd := B.mulVecLin.finrank_range_add_finrank_ker
  have hd' : B.rank + Module.finrank K (LinearMap.ker B.mulVecLin) = n := by
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] using hd
  omega

/-- The exact prime-field kernel count, including p=2 and rank zero. -/
theorem card_kernel_eq_pow [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) (ZMod p)) :
    Nat.card {z : Fin n → ZMod p // B.mulVec z = 0} = p^(n-B.rank) := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using card_kernel_eq_pow_finrank B

/-- A lower bound on the actual matrix rank gives the corresponding
upper bound on its kernel cardinality. -/
theorem card_kernel_le_pow_of_rank_le [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) (ZMod p)) {r : ℕ} (hr : r ≤ B.rank) :
    Nat.card {z : Fin n → ZMod p // B.mulVec z = 0} ≤ p^(n-r) := by
  rw [card_kernel_eq_pow]
  exact Nat.pow_le_pow_right (Nat.Prime.one_le Fact.out) (Nat.sub_le_sub_left hr n)

/-- Exact cardinality for the literal Hessian-kernel definition. -/
theorem hessianKernelCard_eq_pow
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) :
    hessianKernelCard F p x =
      p^(n-(hessian (map (Int.castRingHom (ZMod p)) F) x).rank) :=
  card_kernel_eq_pow _

theorem hessianKernelCard_le_pow_of_rank_le
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (x : Fin n → ZMod p) {r : ℕ}
    (hr : r ≤ (hessian (map (Int.castRingHom (ZMod p)) F) x).rank) :
    hessianKernelCard F p x ≤ p^(n-r) :=
  card_kernel_le_pow_of_rank_le _ hr

/-- Homogeneity makes the actual Hessian zero at the origin, so its
kernel is the entire residue vector space. -/
theorem hessianKernelCard_origin
    (F : MvPolynomial (Fin n) ℤ) (hF : F.IsHomogeneous 3)
    (q : ℕ) [NeZero q] : hessianKernelCard F q 0 = q^n := by
  simp only [hessianKernelCard, hessian_zero (hF.map _), Matrix.zero_mulVec]
  simp [Nat.card_eq_fintype_card]

end CubicTenVariables.PrimeFieldKernelRank
