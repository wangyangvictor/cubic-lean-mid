import TranslatedDepthSeven.AffinePlaneMonomialWeights
import TranslatedDepthSeven.ColumnwiseDeterminantBound
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Evaluation bounds for the surface-normalization monomials

When the distinguished homogeneous coordinate is one and the other two
normalization coordinates are bounded by `R`, a degree-`k` normalization
monomial of affine weight `j` has absolute value at most `R^j`.  This is the
literal pointwise estimate whose product enters the columnwise determinant
bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped BigOperators

/-- Exact evaluation after substituting three arbitrary linear forms. -/
theorem eval_aeval_affinePlaneHomogeneousMonomial
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (k : ℕ) (u : AffinePlaneMonomialIndex k) :
    MvPolynomial.eval y
        (MvPolynomial.aeval L (affinePlaneHomogeneousMonomial ℤ k u)) =
      MvPolynomial.eval y (L 0) ^ (k - u.1.1) *
        MvPolynomial.eval y (L 1) ^ u.2.1 *
          MvPolynomial.eval y (L 2) ^ (u.1.1 - u.2.1) := by
  rw [affinePlaneHomogeneousMonomial, MvPolynomial.aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype]
  · rw [Fin.prod_univ_three]
    have hzero : (affinePlaneMonomialExponent k u) 0 = k - u.1.1 := by
      simp [affinePlaneMonomialExponent]
    have hone : (affinePlaneMonomialExponent k u) 1 = u.2.1 := by
      simp [affinePlaneMonomialExponent]
    have htwo :
        (affinePlaneMonomialExponent k u) 2 = u.1.1 - u.2.1 := by
      simp [affinePlaneMonomialExponent]
    rw [hzero, hone, htwo]
    simp
  · intro i
    simp

/-- On the affine chart, the natural absolute value is bounded by the radius
to the exact affine weight. -/
theorem eval_aeval_affinePlaneHomogeneousMonomial_natAbs_le
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℤ)
    (y : σ → ℤ) (R k : ℕ) (u : AffinePlaneMonomialIndex k)
    (hzero : MvPolynomial.eval y (L 0) = 1)
    (hone : (MvPolynomial.eval y (L 1)).natAbs ≤ R)
    (htwo : (MvPolynomial.eval y (L 2)).natAbs ≤ R) :
    (MvPolynomial.eval y
        (MvPolynomial.aeval L
          (affinePlaneHomogeneousMonomial ℤ k u))).natAbs ≤
      R ^ affinePlaneMonomialIndexWeight u := by
  rw [eval_aeval_affinePlaneHomogeneousMonomial, hzero, one_pow, one_mul,
    Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
  calc
    (MvPolynomial.eval y (L 1)).natAbs ^ u.2.1 *
        (MvPolynomial.eval y (L 2)).natAbs ^ (u.1.1 - u.2.1) ≤
      R ^ u.2.1 * R ^ (u.1.1 - u.2.1) := by
        gcongr
    _ = R ^ (u.2.1 + (u.1.1 - u.2.1)) := by rw [pow_add]
    _ = R ^ affinePlaneMonomialIndexWeight u := by
      have hu : u.2.1 ≤ u.1.1 := Nat.lt_succ_iff.mp u.2.2
      congr 1
      simp only [affinePlaneMonomialIndexWeight]
      omega

/-- The complete square evaluation determinant for all degree-`k`
normalization monomials has the sharp total affine-weight bound. -/
theorem det_affinePlaneMonomialEvaluation_natAbs_le
    {σ : Type*} (L : Fin 3 → MvPolynomial σ ℤ)
    (R k : ℕ) (y : AffinePlaneMonomialIndex k → σ → ℤ)
    (hzero : ∀ v, MvPolynomial.eval (y v) (L 0) = 1)
    (hone : ∀ v, (MvPolynomial.eval (y v) (L 1)).natAbs ≤ R)
    (htwo : ∀ v, (MvPolynomial.eval (y v) (L 2)).natAbs ≤ R) :
    let A : Matrix (AffinePlaneMonomialIndex k)
        (AffinePlaneMonomialIndex k) ℤ :=
      Matrix.of (fun v u ↦
        MvPolynomial.eval (y v)
          (MvPolynomial.aeval L
            (affinePlaneHomogeneousMonomial ℤ k u)))
    A.det.natAbs ≤
      (Fintype.card (AffinePlaneMonomialIndex k)).factorial *
        R ^ affinePlaneMonomialWeight k := by
  classical
  dsimp only
  have hdet := det_natAbs_le_factorial_mul_prod_column_bounds
    (Matrix.of (fun v u ↦
      MvPolynomial.eval (y v)
        (MvPolynomial.aeval L
          (affinePlaneHomogeneousMonomial ℤ k u))))
    (fun u ↦ R ^ affinePlaneMonomialIndexWeight u)
    (fun v u ↦
      eval_aeval_affinePlaneHomogeneousMonomial_natAbs_le
        L (y v) R k u (hzero v) (hone v) (htwo v))
  rw [Finset.prod_pow_eq_pow_sum Finset.univ
    affinePlaneMonomialIndexWeight R,
    sum_affinePlaneMonomialIndexWeight] at hdet
  exact hdet

end

end TranslatedDepthSeven
