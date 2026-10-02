import CubicTenVariables.PrimeFrogZeroMass
import CubicTenVariables.PrimeFieldKernelRank

/-! Finite j=2 weighted-root decomposition. The singular subsum retains
both the polynomial-zero condition and exclusion of the origin. -/

noncomputable section
namespace CubicTenVariables.PrimeFrogTwoMass
open MvPolynomial PrimeFrogZeroMass HessianKernelCRT PrimeFieldKernelRank
open scoped BigOperators

variable {n : ℕ}

/-- The literal nonzero singular root set used in the weighted bound. -/
def singularRootPoints (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [NeZero p] :
    Finset (Fin n → ZMod p) := by
  classical
  exact Finset.univ.filter fun x =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧ x ≠ 0 ∧
      ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0

@[simp] theorem mem_singularRootPoints (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) [NeZero p] (x : Fin n → ZMod p) :
    x ∈ singularRootPoints F p ↔
      eval₂ (Int.castRingHom (ZMod p)) x F = 0 ∧ x ≠ 0 ∧
        ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0 := by
  simp [singularRootPoints]

/-- The origin is not included in the gradient-zero error term. -/
theorem rootWeight_le_nonzero (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) [NeZero p] (x : Fin n → ZMod p) :
    rootWeight F p x ≤ 1 +
      (if x ≠ 0 ∧ ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0
        then p else 0) + (if x = 0 then p^2 else 0) := by
  classical
  rw [rootWeight_eq F p hp x]
  by_cases hx : x = 0
  · have hn : ¬(x ≠ 0 ∧ ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0) := fun h => h.1 hx
    rw [if_pos hx, if_neg hn]
    split_ifs <;> nlinarith [hp.two_le]
  · by_cases hg : ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0
    · rw [if_pos hg, if_neg hx, if_pos ⟨hx,hg⟩]
      omega
    · have hn : ¬(x ≠ 0 ∧ ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0) := fun h => hg h.2
      rw [if_neg hg, if_neg hx, if_neg hn]
      omega

/-- A generic natural weight preserves the exact root-restricted
nonzero singular subsum. No estimate for any of these sums is assumed. -/
theorem sum_weighted_rootWeight_le (F : MvPolynomial (Fin n) ℤ)
    (p : ℕ) (hp : p.Prime) [NeZero p] (N : (Fin n → ZMod p) → ℕ) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0), N x * rootWeight F p x) ≤
    (∑ x : Fin n → ZMod p, N x) +
      p * (∑ x ∈ singularRootPoints F p, N x) + p^2 * N 0 := by
  classical
  let S := Finset.univ.filter (fun x : Fin n → ZMod p =>
    eval₂ (Int.castRingHom (ZMod p)) x F = 0)
  let G := fun x : Fin n → ZMod p => x ≠ 0 ∧
    ∀ i, eval₂ (Int.castRingHom (ZMod p)) x (pderiv i F) = 0
  have hpoint (x : Fin n → ZMod p) : N x * rootWeight F p x ≤
      N x + p * (if G x then N x else 0) + (if x = 0 then p^2 * N 0 else 0) := by
    calc
      _ ≤ N x * (1 + (if G x then p else 0) + (if x = 0 then p^2 else 0)) :=
        Nat.mul_le_mul_left _ (rootWeight_le_nonzero F p hp x)
      _ = _ := by
        by_cases hx : x = 0
        · subst x
          simp [G]
          ring
        · by_cases hg : G x
          · simp [hx, hg]
            ring
          · simp [hx, hg]
  have hsum := Finset.sum_le_sum (s := S) (fun x _ => hpoint x)
  have hmain : (∑ x ∈ S, N x) ≤ ∑ x : Fin n → ZMod p, N x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
  have hsing : (∑ x ∈ S, if G x then N x else 0) =
      ∑ x ∈ singularRootPoints F p, N x := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp [S, G, singularRootPoints]
  have horigin : (∑ x ∈ S, if x = 0 then p^2 * N 0 else 0) ≤ p^2 * N 0 := by
    calc
      _ ≤ ∑ x : Fin n → ZMod p, if x = 0 then p^2 * N 0 else 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
      _ = _ := by simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsing] at hsum
  exact hsum.trans (Nat.add_le_add (Nat.add_le_add_right hmain _) horigin)

/-- The literal Hessian-kernel weighted mass, with the exact homogeneous
origin contribution p^(n+2). No field-point-count estimate is a premise. -/
theorem sum_kernel_mul_rootWeight_le (F : MvPolynomial (Fin n) ℤ)
    (hF : F.IsHomogeneous 3) (p : ℕ) (hp : p.Prime) [NeZero p] :
    (∑ x ∈ Finset.univ.filter (fun x : Fin n → ZMod p =>
      eval₂ (Int.castRingHom (ZMod p)) x F = 0),
      hessianKernelCard F p x * rootWeight F p x) ≤
    (∑ x : Fin n → ZMod p, hessianKernelCard F p x) +
      p * (∑ x ∈ singularRootPoints F p, hessianKernelCard F p x) + p^(n+2) := by
  simpa only [hessianKernelCard_origin F hF, pow_add, Nat.mul_comm] using
    sum_weighted_rootWeight_le F p hp (hessianKernelCard F p)

end CubicTenVariables.PrimeFrogTwoMass
