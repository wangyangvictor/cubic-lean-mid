import TranslatedDepthSeven.AffinePlaneMonomialWeights
import Mathlib.Data.Fintype.Card

/-!
# Affine weights of the standard monomials for one plane equation

If its leading affine monomial is `x^a y^b`, the standard monomials of
degree at most `k` are exactly those not divisible by it. Multiplication by
`x^a y^b` identifies the omitted block with all monomials of degree at most
`k-a-b`. The count and the sum of affine weights below are literal finite
combinatorics, independent of polynomial coefficients.
-/

namespace TranslatedDepthSeven

noncomputable section
open scoped BigOperators

/-- Divisibility of an affine monomial by `x^a y^b`. -/
def affinePlaneMonomialDivisible (a b : ℕ) {k : ℕ}
    (u : AffinePlaneMonomialIndex k) : Prop :=
  a ≤ u.2.1 ∧ b ≤ u.1.1 - u.2.1

instance (a b k : ℕ) : DecidablePred (@affinePlaneMonomialDivisible a b k) :=
  fun u => inferInstanceAs (Decidable (a ≤ u.2.1 ∧ b ≤ u.1.1 - u.2.1))

abbrev FilteredAffinePlaneCurveMonomialIndex (a b k : ℕ) :=
  {u : AffinePlaneMonomialIndex k // ¬ affinePlaneMonomialDivisible a b u}

/-- The removed block is a translated triangular block. -/
def affinePlaneDivisibleMonomialEquiv (a b k : ℕ) (hab : a + b ≤ k) :
    AffinePlaneMonomialIndex (k - (a + b)) ≃
      {u : AffinePlaneMonomialIndex k // affinePlaneMonomialDivisible a b u} where
  toFun u :=
    ⟨⟨⟨u.1.1 + (a + b), by have := u.1.2; omega⟩,
      ⟨u.2.1 + a, by have := u.2.2; dsimp; omega⟩⟩,
      by
        dsimp [affinePlaneMonomialDivisible]
        have := u.2.2
        omega⟩
  invFun u :=
    ⟨⟨u.1.1.1 - (a + b), by have := u.1.1.2; omega⟩,
      ⟨u.1.2.1 - a, by
        have := u.1.2.2
        have := u.2
        dsimp [affinePlaneMonomialDivisible] at this
        dsimp
        omega⟩⟩
  left_inv u := by
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      omega
    · apply (Fin.heq_ext_iff (by dsimp; omega)).mpr
      dsimp
      omega
  right_inv u := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext
      have := u.2
      dsimp [affinePlaneMonomialDivisible] at this ⊢
      omega
    · apply (Fin.heq_ext_iff (by
        have := u.2
        dsimp [affinePlaneMonomialDivisible] at this ⊢
        omega)).mpr
      have := u.2
      dsimp [affinePlaneMonomialDivisible] at this ⊢
      omega

theorem affinePlaneDivisibleMonomialEquiv_weight
    (a b k : ℕ) (hab : a + b ≤ k)
    (u : AffinePlaneMonomialIndex (k - (a + b))) :
    affinePlaneMonomialIndexWeight (affinePlaneDivisibleMonomialEquiv a b k hab u).1 =
      affinePlaneMonomialIndexWeight u + (a + b) := rfl

/-- The exact number of standard monomials, without natural subtraction. -/
theorem card_filteredAffinePlaneCurveMonomialIndex_add
    (a b k : ℕ) (hab : a + b ≤ k) :
    Fintype.card (FilteredAffinePlaneCurveMonomialIndex a b k) +
        affinePlaneMonomialCount (k - (a + b)) =
      affinePlaneMonomialCount k := by
  classical
  rw [← card_affinePlaneMonomialIndex (k - (a + b)),
    Fintype.card_congr (affinePlaneDivisibleMonomialEquiv a b k hab),
    ← card_affinePlaneMonomialIndex k]
  rw [Fintype.card_subtype_compl]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

/-- The affine weight lost by removing the divisible block. -/
theorem sum_divisibleAffinePlaneMonomialWeight
    (a b k : ℕ) (hab : a + b ≤ k) :
    (∑ u : {u : AffinePlaneMonomialIndex k // affinePlaneMonomialDivisible a b u},
      affinePlaneMonomialIndexWeight u.1) =
        affinePlaneMonomialWeight (k - (a + b)) +
          (a + b) * affinePlaneMonomialCount (k - (a + b)) := by
  classical
  rw [← Equiv.sum_comp (affinePlaneDivisibleMonomialEquiv a b k hab)]
  simp only [affinePlaneDivisibleMonomialEquiv_weight, Finset.sum_add_distrib,
    sum_affinePlaneMonomialIndexWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_affinePlaneMonomialIndex, Nat.cast_id]
  ring

/-- Exact total affine weight of the standard monomials. -/
theorem sum_filteredAffinePlaneCurveMonomialWeight_add
    (a b k : ℕ) (hab : a + b ≤ k) :
    (∑ u : FilteredAffinePlaneCurveMonomialIndex a b k,
      affinePlaneMonomialIndexWeight u.1) +
        (affinePlaneMonomialWeight (k - (a + b)) +
          (a + b) * affinePlaneMonomialCount (k - (a + b))) =
      affinePlaneMonomialWeight k := by
  classical
  rw [← sum_divisibleAffinePlaneMonomialWeight a b k hab,
    ← sum_affinePlaneMonomialIndexWeight k]
  simpa only [add_comm] using Fintype.sum_subtype_add_sum_subtype
    (fun u : AffinePlaneMonomialIndex k => affinePlaneMonomialDivisible a b u)
    (fun u => affinePlaneMonomialIndexWeight u)

/-- The usual linear Hilbert function, in division-free form. -/
theorem two_mul_card_filteredAffinePlaneCurveMonomialIndex
    (a b k : ℕ) (hab : a + b ≤ k) :
    2 * Fintype.card (FilteredAffinePlaneCurveMonomialIndex a b k) +
      (a + b) * (a + b - 1) = 2 * (a + b) * (k + 1) := by
  have hcard := card_filteredAffinePlaneCurveMonomialIndex_add a b k hab
  have hfull := two_mul_affinePlaneMonomialCount k
  have hremoved := two_mul_affinePlaneMonomialCount (k - (a + b))
  have hk : k = (k - (a + b)) + (a + b) := by omega
  by_cases hzero : a + b = 0
  · simp only [hzero, Nat.sub_zero] at hcard ⊢
    omega
  · have hpred : a + b = (a + b - 1) + 1 := by omega
    nlinarith [hcard, hfull, hremoved]

/-- The sum of affine weights, in division-free form. -/
theorem six_mul_sum_filteredAffinePlaneCurveMonomialWeight
    (a b k : ℕ) (hab : a + b ≤ k) (hdegree : 2 ≤ a + b) :
    6 * (∑ u : FilteredAffinePlaneCurveMonomialIndex a b k,
      affinePlaneMonomialIndexWeight u.1) +
      (a + b) * (a + b - 1) * (a + b - 2) =
        3 * (a + b) * k * (k + 1) := by
  have hweight := sum_filteredAffinePlaneCurveMonomialWeight_add a b k hab
  have hfull := three_mul_affinePlaneMonomialWeight k
  have hremoved := three_mul_affinePlaneMonomialWeight (k - (a + b))
  have hremovedCard := congrArg (fun n : ℕ => 3 * (a + b) * n)
    (two_mul_affinePlaneMonomialCount (k - (a + b)))
  have hk : k = (k - (a + b)) + (a + b) := by omega
  have hpred : a + b = (a + b - 1) + 1 := by omega
  have hpred2 : a + b = (a + b - 2) + 2 := by omega
  generalize hδ : a + b = δ at *
  generalize hl : k - δ = l at *
  subst k
  have hpred' : δ - 1 = (δ - 2) + 1 := by omega
  rw [hpred']
  generalize ht : δ - 2 = t at *
  subst δ
  rw [hpred2] at hweight hfull hremovedCard ⊢
  dsimp only at hremovedCard
  nlinarith [hweight, hfull, hremoved, hremovedCard]

/-- A quadratic forbidden monomial leaves exactly `2k+1` columns. -/
theorem card_filteredAffinePlaneCurveMonomialIndex_quadratic
    (a b k : ℕ) (hab : a + b = 2) (hk : 2 ≤ k) :
    Fintype.card (FilteredAffinePlaneCurveMonomialIndex a b k) = 2 * k + 1 := by
  have h := two_mul_card_filteredAffinePlaneCurveMonomialIndex a b k (by omega)
  rw [hab] at h
  omega

/-- Their total affine weight is `k(k+1)`. -/
theorem sum_filteredAffinePlaneCurveMonomialWeight_quadratic
    (a b k : ℕ) (hab : a + b = 2) (hk : 2 ≤ k) :
    (∑ u : FilteredAffinePlaneCurveMonomialIndex a b k,
      affinePlaneMonomialIndexWeight u.1) = k * (k + 1) := by
  have h := six_mul_sum_filteredAffinePlaneCurveMonomialWeight a b k
    (by omega) (by omega)
  rw [hab] at h
  norm_num at h
  nlinarith

end
end TranslatedDepthSeven
