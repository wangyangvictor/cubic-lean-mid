import HessianTheorem11.NonzeroLimitTransport
import Mathlib.Algebra.Polynomial.Roots

/-! Actual diagonal weight curves, including their polynomial specialization.
These lemmas supply the elementary affine-line part of the orbit/big-cell
argument and have no external mathematical input. -/
noncomputable section
namespace HessianTheorem11.ReducedWeightCurve
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open scoped BigOperators
variable {K : Type*} [Field K] {n : ℕ}

def diagonalWeight (w : Fin n → ℤ) (t : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i => t ^ w i)

def curve (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) (t : K) :
    MvPolynomial (Fin n) K :=
  F.sum fun d c => monomial d (c * t ^ (monomialWeight w d).toNat)

@[simp] theorem coeff_curve (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (t : K) (d : Fin n →₀ ℕ) :
    coeff d (curve F w t) = coeff d F * t ^ (monomialWeight w d).toNat := by
  classical
  simp [curve, Finsupp.sum, coeff_sum, coeff_monomial, Finset.sum_ite_eq',
    Finsupp.mem_support_iff]
  split_ifs with h
  · change (0 : K) = coeff d F * _
    have hd : coeff d F = 0 := h
    rw [hd, zero_mul]
  · rfl

theorem curve_zero (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hF : HasNonnegativeWeights F w) : curve F w 0 = zeroWeightPart F w := by
  classical
  ext d
  rw [coeff_curve, coeff_zeroWeightPart]
  by_cases hc : coeff d F = 0
  · simp [hc]
  have hw := hF d (Finsupp.mem_support_iff.mpr hc)
  by_cases hz : monomialWeight w d = 0
  · simp [hz]
  · have hpos : 0 < (monomialWeight w d).toNat := by omega
    simp [hz, Nat.ne_of_gt hpos]

@[simp] theorem curve_one (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    curve F w 1 = F := by ext d; simp

@[simp] theorem linearForms_diagonalWeight (w : Fin n → ℤ) (t : K) (i : Fin n) :
    linearForms (diagonalWeight w t) i = C (t ^ w i) * X i := by
  classical
  simp [linearForms, diagonalWeight, Matrix.diagonal_apply, apply_ite, ite_mul]

theorem prod_zpow_nonzero {ι : Type*} (t : K) (ht : t ≠ 0)
    (s : Finset ι) (a : ι → ℤ) :
    (∏ i ∈ s, t ^ a i) = t ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi,
      ih, zpow_add₀ ht]

theorem restrict_diagonal_monomial (w : Fin n → ℤ) (t : K) (ht : t ≠ 0)
    (d : Fin n →₀ ℕ) (c : K) :
    restrict (diagonalWeight w t) (monomial d c) =
      monomial d (c * t ^ monomialWeight w d) := by
  classical
  change aeval (linearForms (diagonalWeight w t)) (monomial d c) = _
  rw [aeval_monomial]
  simp only [linearForms_diagonalWeight, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, Finsupp.prod]
  have hp : (∏ i ∈ d.support, (t ^ w i) ^ d i) = t ^ monomialWeight w d := by
    simp_rw [← zpow_natCast, ← zpow_mul]
    rw [prod_zpow_nonzero t ht]
    congr 1
    unfold monomialWeight
    calc
      (∑ i ∈ d.support, w i * (d i : ℤ)) = ∑ i ∈ d.support, (d i : ℤ) * w i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
      _ = ∑ i, (d i : ℤ) * w i := Finset.sum_subset (Finset.subset_univ _) (by
        intro i hi hnot
        simp [Finsupp.notMem_support_iff.mp hnot])
  rw [hp]
  rw [← C_mul_monomial, monomial_eq]
  simp [Finsupp.prod, mul_assoc]

theorem curve_eq_restrict (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hF : HasNonnegativeWeights F w) (t : K) (ht : t ≠ 0) :
    curve F w t = restrict (diagonalWeight w t) F := by
  classical
  calc
    curve F w t = ∑ d ∈ F.support,
        restrict (diagonalWeight w t) (monomial d (coeff d F)) := by
      unfold curve Finsupp.sum
      apply Finset.sum_congr rfl
      intro d hd
      rw [restrict_diagonal_monomial w t ht]
      change monomial d (coeff d F * t ^ (monomialWeight w d).toNat) =
        monomial d (coeff d F * t ^ monomialWeight w d)
      rw [← zpow_natCast, Int.toNat_of_nonneg (hF d hd)]
    _ = restrict (diagonalWeight w t) F := by
      simpa only [restrict, map_sum] using
        (congrArg (restrict (diagonalWeight w t)) F.as_sum).symm

theorem diagonalWeight_det (w : Fin n → ℤ) (hsum : ∑ i, w i = 0)
    (t : K) (ht : t ≠ 0) : (diagonalWeight w t).det = 1 := by
  rw [diagonalWeight, Matrix.det_diagonal, prod_zpow_nonzero t ht, hsum, zpow_zero]

/-- Every polynomial function in coefficients pulls back to an actual
univariate polynomial on the weight curve. -/
def curveTest (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (P : MvPolynomial (Fin n →₀ ℕ) K) : Polynomial K :=
  eval₂ Polynomial.C
    (fun d => Polynomial.C (coeff d F) * Polynomial.X ^ (monomialWeight w d).toNat) P

theorem eval_curveTest (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (P : MvPolynomial (Fin n →₀ ℕ) K) (t : K) :
    (curveTest F w P).eval t = eval (fun d => coeff d (curve F w t)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [curveTest]
  | add P Q hP hQ =>
    simp only [curveTest, eval₂_add, Polynomial.eval_add, map_add] at hP hQ ⊢
    rw [hP, hQ]
  | mul_X P d hP =>
    simp only [curveTest, eval₂_mul, eval₂_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hP ⊢
    rw [hP]
    simp

theorem polynomial_zero_of_nonzero_values [Infinite K] (P : Polynomial K)
    (hP : ∀ t : K, t ≠ 0 → P.eval t = 0) : P = 0 := by
  apply P.eq_zero_of_infinite_isRoot
  apply (Set.infinite_univ.diff (Set.finite_singleton (0 : K))).mono
  intro t ht
  apply hP
  simpa only [Set.mem_singleton_iff] using ht.2

theorem exists_nonzero_curve_test [Infinite K]
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hF : HasNonnegativeWeights F w) (P : MvPolynomial (Fin n →₀ ℕ) K)
    (hP : eval (fun d => coeff d (zeroWeightPart F w)) P ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ eval (fun d => coeff d (curve F w t)) P ≠ 0 := by
  by_contra h
  push_neg at h
  have hz := polynomial_zero_of_nonzero_values (curveTest F w P) (by
    intro t ht
    rw [eval_curveTest]
    exact h t ht)
  have he := congrArg (fun Q : Polynomial K => Q.eval 0) hz
  dsimp only at he
  rw [eval_curveTest, curve_zero F w hF, Polynomial.eval_zero] at he
  exact hP he

/-- The actual weight-zero form lies in the actual coefficient-polynomial
closure of the special-linear orbit. No orbit theorem is assumed. -/
theorem zeroWeightPart_mem_slOrbitClosure [Infinite K]
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (hsum : ∑ i, w i = 0) (hF : HasNonnegativeWeights F w) :
    zeroWeightPart F w ∈ slOrbitClosure F := by
  intro P hP
  have hz := polynomial_zero_of_nonzero_values (curveTest F w P) (by
    intro t ht
    rw [eval_curveTest, curve_eq_restrict F w hF t ht]
    exact hP _ ⟨diagonalWeight w t, diagonalWeight_det w hsum t ht, rfl⟩)
  have he := congrArg (fun Q : Polynomial K => Q.eval 0) hz
  simpa only [eval_curveTest, curve_zero F w hF, Polynomial.eval_zero] using he

theorem diagonal_fixes_zeroWeightPart (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (t : K) (ht : t ≠ 0) :
    restrict (diagonalWeight w t) (zeroWeightPart F w) = zeroWeightPart F w := by
  have hw : HasNonnegativeWeights (zeroWeightPart F w) w := by
    intro e he
    rw [zeroWeightPart_weights F w e he]
  rw [← curve_eq_restrict _ w hw t ht]
  ext e
  rw [coeff_curve]
  by_cases he : coeff e (zeroWeightPart F w) = 0
  · simp [he]
  · rw [zeroWeightPart_weights F w e (Finsupp.mem_support_iff.mpr he)]
    simp

end HessianTheorem11.ReducedWeightCurve
