import CubicTenVariables.FiniteFieldPolynomialZeros

/-! Finite variance assembly with a literal polynomial exceptional set.
The good-fiber estimate stays an explicit hypothesis; it is supplied by
the separate geometric-integrality and Weil-bound application. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SecondMomentDeviation
open MvPolynomial FiniteFieldPolynomialZeros
open scoped BigOperators Classical

/-- Elementary contribution of a cubic plane fiber. The proof candidate
was generated locally by DeepSeek and independently checked by Lean. -/
theorem trivial_deviation_sq
    (q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (hupper : t ≤ 3*q) :
    (t-q)^2 ≤ 4*q^2 := by
  have h₁ : (t - q) ^ 2 ≤ 4 * q ^ 2 := by
    nlinarith [sq_nonneg (t - 2 * q), sq_nonneg (t + q), sq_nonneg (t - 3 * q),
      sq_nonneg (q - t), sq_nonneg (2 * q - t), sq_nonneg (3 * q - t)]
  linarith

theorem sum_sq_le_of_exceptional_set {α : Type*} [Fintype α]
    (E : Finset α) (ν : α → ℕ) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (htriv : ∀ x, (ν x : ℝ) ≤ 3*q)
    (hgood : ∀ x, x ∉ E → ((ν x : ℝ)-q)^2 ≤ B*q) :
    ∑ x, ((ν x : ℝ)-q)^2 ≤
      (Fintype.card α : ℝ)*(B*q) + (E.card : ℝ)*(4*q^2) := by
  have hpoint (x : α) : ((ν x : ℝ)-q)^2 ≤
      B*q + if x ∈ E then 4*q^2 else 0 := by
    by_cases hx : x ∈ E
    · rw [if_pos hx]
      exact (trivial_deviation_sq q (ν x) hq (Nat.cast_nonneg _) (htriv x)).trans
        (le_add_of_nonneg_left (mul_nonneg hB hq))
    · simpa only [if_neg hx, add_zero] using hgood x hx
  calc
    _ ≤ ∑ x : α, (B*q + if x ∈ E then 4*q^2 else 0) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [← Finset.sum_filter]
      simp

/-- A nonzero exceptional polynomial and a good-fiber variance bound
give the exact power q^(m+1), uniformly over arbitrary finite fields. -/
theorem sum_sq_le_of_polynomial {K σ : Type*} [Field K] [Fintype K] [Fintype σ]
    [DecidableEq σ]
    (hm : 1 ≤ Fintype.card σ) (G : MvPolynomial σ K) (hG : G ≠ 0)
    (ν : (σ → K) → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (htriv : ∀ x, (ν x : ℝ) ≤ 3*(Fintype.card K : ℝ))
    (hgood : ∀ x, eval x G ≠ 0 →
      ((ν x : ℝ)-(Fintype.card K : ℝ))^2 ≤ B*(Fintype.card K : ℝ)) :
    ∑ x : σ → K, ((ν x : ℝ)-(Fintype.card K : ℝ))^2 ≤
      (B+4*(G.totalDegree : ℝ)) * (Fintype.card K : ℝ)^(Fintype.card σ+1) := by
  let q : ℝ := Fintype.card K
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have h := sum_sq_le_of_exceptional_set (zeros G) ν q B hq hB htriv
    (fun x hx => hgood x (by simpa only [mem_zeros] using hx))
  have hz : ((zeros G).card : ℝ) ≤
      (G.totalDegree : ℝ)*q^(Fintype.card σ-1) := by
    dsimp [q]
    exact_mod_cast card_zeros_le_totalDegree_mul G hG
  have hcard : (Fintype.card (σ → K) : ℝ) = q^(Fintype.card σ) := by
    simp only [Fintype.card_fun, Nat.cast_pow, q]
  rw [hcard] at h
  apply h.trans
  calc
    _ ≤ q^(Fintype.card σ)*(B*q) +
        ((G.totalDegree : ℝ)*q^(Fintype.card σ-1))*(4*q^2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hz (show 0 ≤ 4*q^2 by positivity))
    _ = _ := by
      obtain ⟨m,hm'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Fintype.card σ ≠ 0)
      rw [hm', Nat.succ_sub_one]
      simp only [pow_succ]
      ring

end CubicTenVariables.SecondMomentDeviation
