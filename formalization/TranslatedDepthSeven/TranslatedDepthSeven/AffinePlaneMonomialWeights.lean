import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous monomials and affine weights for a surface normalization

A homogeneous polynomial algebra in three degree-one variables has, in
degree `k`, the monomials

`X₀^(k-j) X₁^a X₂^(j-a)`,  `0 ≤ j ≤ k`, `0 ≤ a ≤ j`.

On the affine chart `X₀ = 1`, such a monomial has affine weight `j`.
This file gives a literal finite index type and proves the two exact sums

`2 * count = (k+1)(k+2)`,
`3 * totalWeight = k(k+1)(k+2)`.

Their quotient is the `2/3` archimedean exponent in the surface case of the
affine determinant method.  No Hilbert polynomial or monomial ordering is
used.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial

/-- The number of monomials in two affine variables of total degree at most
`k`, written as the sum over their exact affine degrees. -/
def affinePlaneMonomialCount (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), (j + 1)

/-- The sum of the affine total degrees of those monomials. -/
def affinePlaneMonomialWeight (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), j * (j + 1)

/-- Twice the triangular monomial count has this division-free closed
form. -/
theorem two_mul_affinePlaneMonomialCount (k : ℕ) :
    2 * affinePlaneMonomialCount k = (k + 1) * (k + 2) := by
  induction k with
  | zero => simp [affinePlaneMonomialCount]
  | succ k ih =>
      rw [affinePlaneMonomialCount, Finset.sum_range_succ,
        show k + 1 + 1 = k + 2 by omega]
      rw [← affinePlaneMonomialCount, mul_add, ih]
      ring

/-- Three times the total affine weight has this division-free closed
form. -/
theorem three_mul_affinePlaneMonomialWeight (k : ℕ) :
    3 * affinePlaneMonomialWeight k = k * (k + 1) * (k + 2) := by
  induction k with
  | zero => simp [affinePlaneMonomialWeight]
  | succ k ih =>
      rw [affinePlaneMonomialWeight, Finset.sum_range_succ,
        show k + 1 + 1 = k + 2 by omega]
      rw [← affinePlaneMonomialWeight, mul_add, ih]
      ring

/-- A literal index for the homogeneous monomial
`X₀^(k-j) X₁^a X₂^(j-a)`. -/
abbrev AffinePlaneMonomialIndex (k : ℕ) :=
  Σ j : Fin (k + 1), Fin (j.1 + 1)

/-- The affine degree `j` of a surface-normalization monomial. -/
def affinePlaneMonomialIndexWeight {k : ℕ}
    (u : AffinePlaneMonomialIndex k) : ℕ := u.1

/-- The cardinality of the literal monomial index is the cumulative count. -/
theorem card_affinePlaneMonomialIndex (k : ℕ) :
    Fintype.card (AffinePlaneMonomialIndex k) =
      affinePlaneMonomialCount k := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, affinePlaneMonomialCount]
  rw [← Fin.sum_univ_eq_sum_range]

/-- Summing the displayed affine weights over the literal index gives the
exact cumulative weight. -/
theorem sum_affinePlaneMonomialIndexWeight (k : ℕ) :
    ∑ u : AffinePlaneMonomialIndex k,
      affinePlaneMonomialIndexWeight u = affinePlaneMonomialWeight k := by
  classical
  rw [Fintype.sum_sigma]
  simp only [affinePlaneMonomialIndexWeight, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [affinePlaneMonomialWeight, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  exact Nat.mul_comm (j + 1) j

/-- The exponent vector associated to the displayed monomial. -/
def affinePlaneMonomialExponent (k : ℕ)
    (u : AffinePlaneMonomialIndex k) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![k - u.1.1, u.2.1, u.1.1 - u.2.1]

/-- The three exponents add to the homogeneous degree `k`. -/
theorem affinePlaneMonomialExponent_degree (k : ℕ)
    (u : AffinePlaneMonomialIndex k) :
    Finsupp.degree (affinePlaneMonomialExponent k u) = k := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
  have hzero : (affinePlaneMonomialExponent k u) 0 = k - u.1.1 := by
    simp [affinePlaneMonomialExponent]
  have hone : (affinePlaneMonomialExponent k u) 1 = u.2.1 := by
    simp [affinePlaneMonomialExponent]
  have htwo :
      (affinePlaneMonomialExponent k u) 2 = u.1.1 - u.2.1 := by
    simp [affinePlaneMonomialExponent]
  rw [hzero, hone, htwo]
  have huj : u.2.1 ≤ u.1.1 := Nat.lt_succ_iff.mp u.2.2
  have hjk : u.1.1 ≤ k := Nat.lt_succ_iff.mp u.1.2
  omega

/-- The corresponding polynomial monomial. -/
def affinePlaneHomogeneousMonomial
    (K : Type*) [CommSemiring K] (k : ℕ)
    (u : AffinePlaneMonomialIndex k) : MvPolynomial (Fin 3) K :=
  MvPolynomial.monomial (affinePlaneMonomialExponent k u) 1

/-- Every displayed monomial is homogeneous of degree `k`. -/
theorem affinePlaneHomogeneousMonomial_isHomogeneous
    (K : Type*) [CommSemiring K] (k : ℕ)
    (u : AffinePlaneMonomialIndex k) :
    (affinePlaneHomogeneousMonomial K k u).IsHomogeneous k := by
  intro d hd
  rw [affinePlaneHomogeneousMonomial,
    MvPolynomial.coeff_monomial] at hd
  split_ifs at hd with h
  · subst d
    simpa only [Finsupp.degree_eq_weight_one] using
      affinePlaneMonomialExponent_degree k u
  · simp at hd

end

end TranslatedDepthSeven
