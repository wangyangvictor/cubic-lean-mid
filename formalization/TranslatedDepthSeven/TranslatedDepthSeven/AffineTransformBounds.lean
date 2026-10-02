import TranslatedDepthSeven.AffineIntegralPointTransport
import TranslatedDepthSeven.StarEquationBounds

/-!
# Literal bounds for an integral affine substitution

The substitution `X i ↦ x₀ i + r X i` is identified with evaluation of
the already-defined symbolic line polynomial.  Expanding that univariate
polynomial in its literal support gives source-sensitive support and integral
coefficient bounds.  No geometric or counting hypothesis occurs here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open Finset MvPolynomial Polynomial

/-- The integral affine transform is evaluation of the symbolic line
polynomial at the constant polynomial `r`. -/
theorem integralAffineTransform_eq_eval_symbolicLinePolynomial
    {n : ℕ} (x₀ : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integralAffineTransform x₀ r f =
      Polynomial.eval (MvPolynomial.C (r : ℤ))
        (symbolicLinePolynomial f x₀) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [integralAffineTransform, symbolicLinePolynomial]
  | add f g hf hg =>
      unfold integralAffineTransform at hf hg ⊢
      rw [map_add, symbolicLinePolynomial_add, Polynomial.eval_add, hf, hg]
  | mul_X f i hf =>
      unfold integralAffineTransform at hf ⊢
      rw [map_mul, symbolicLinePolynomial_mul, Polynomial.eval_mul, hf]
      rw [symbolicLinePolynomial_X]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, MvPolynomial.aeval_X]

/-- Equivalently, the affine transform is the finite sum of the literal star
coefficients, with the line parameter specialized to `r`. -/
theorem integralAffineTransform_eq_sum_starCoefficient
    {n : ℕ} (x₀ : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integralAffineTransform x₀ r f =
      ∑ k ∈ (symbolicLinePolynomial f x₀).support,
        starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k) := by
  rw [integralAffineTransform_eq_eval_symbolicLinePolynomial,
    Polynomial.eval_eq_sum]
  simp [Polynomial.sum, starCoefficient]

/-- The symbolic line restriction has at most `d+1` nonzero coefficient
polynomials when the source has total degree at most `d`. -/
theorem symbolicLinePolynomial_support_card_le
    {n d : ℕ} (x₀ : IntVector n) (f : MvPolynomial (Fin n) ℤ)
    (hdegree : f.totalDegree ≤ d) :
    (symbolicLinePolynomial f x₀).support.card ≤ d + 1 := by
  have hnatDegree : (symbolicLinePolynomial f x₀).natDegree ≤ d := by
    calc
      (symbolicLinePolynomial f x₀).natDegree =
          (symbolicLineMvPolynomial f x₀).degreeOf none := by
        rw [← optionEquivLeft_symbolicLineMvPolynomial]
        exact MvPolynomial.natDegree_optionEquivLeft
          ℤ (symbolicLineMvPolynomial f x₀)
      _ ≤ f.totalDegree := symbolicLineMvPolynomial_degreeOf_none_le f x₀
      _ ≤ d := hdegree
  calc
    (symbolicLinePolynomial f x₀).support.card ≤
        (Finset.range ((symbolicLinePolynomial f x₀).natDegree + 1)).card :=
      Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ
    _ = (symbolicLinePolynomial f x₀).natDegree + 1 := Finset.card_range _
    _ ≤ d + 1 := Nat.add_le_add_right hnatDegree 1

/-- A literal support bound for the integral affine transform.  The extra
factor `d+1` comes only from summing its star coefficients; the estimate is
deliberately insensitive to cancellations after specializing the line
parameter. -/
theorem integralAffineTransform_support_card_le
    {n d : ℕ} (x₀ : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (hdegree : f.totalDegree ≤ d) :
    (integralAffineTransform x₀ r f).support.card ≤
      (d + 1) * (f.support.card * 2 ^ d) := by
  classical
  rw [integralAffineTransform_eq_sum_starCoefficient]
  calc
    (∑ k ∈ (symbolicLinePolynomial f x₀).support,
        starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k)).support.card ≤
        ∑ k ∈ (symbolicLinePolynomial f x₀).support,
          (starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k)).support.card := by
      exact (Finset.card_le_card MvPolynomial.support_sum).trans
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ (symbolicLinePolynomial f x₀).support,
          f.support.card * 2 ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k)).support.card ≤
            (starCoefficient f x₀ k).support.card := by
          rw [mul_comm]
          rw [← MvPolynomial.smul_eq_C_mul]
          exact Finset.card_le_card MvPolynomial.support_smul
        _ ≤ f.support.card * 2 ^ d :=
          starCoefficient_support_card_le f x₀ k d hdegree
    _ = (symbolicLinePolynomial f x₀).support.card *
          (f.support.card * 2 ^ d) := by simp
    _ ≤ (d + 1) * (f.support.card * 2 ^ d) :=
      Nat.mul_le_mul_right _ (symbolicLinePolynomial_support_card_le x₀ f hdegree)

/-- Every coefficient of the integral affine transform has a completely
literal polynomial bound in the source support and coefficient height, the
source degree, the translation height, and the scale. -/
theorem integralAffineTransform_coeff_natAbs_le
    {n d C H : ℕ} (x₀ : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ d)
    (hx₀ : ∀ i, (x₀ i).natAbs ≤ H)
    (mu : Fin n →₀ ℕ) :
    ((integralAffineTransform x₀ r f).coeff mu).natAbs ≤
      (d + 1) * (f.support.card * C * (2 * max 1 H) ^ d) *
        max 1 r ^ d := by
  classical
  rw [integralAffineTransform_eq_sum_starCoefficient,
    MvPolynomial.coeff_sum]
  calc
    (∑ k ∈ (symbolicLinePolynomial f x₀).support,
        (starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k)).coeff mu).natAbs ≤
        ∑ k ∈ (symbolicLinePolynomial f x₀).support,
          ((starCoefficient f x₀ k * MvPolynomial.C ((r : ℤ) ^ k)).coeff mu).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _k ∈ (symbolicLinePolynomial f x₀).support,
          (f.support.card * C * (2 * max 1 H) ^ d) * max 1 r ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      rw [mul_comm, MvPolynomial.coeff_C_mul, Int.natAbs_mul]
      have hkdegree : k ≤ d := by
        exact (Polynomial.le_natDegree_of_mem_supp _ hk).trans
          (by
            calc
              (symbolicLinePolynomial f x₀).natDegree =
                  (symbolicLineMvPolynomial f x₀).degreeOf none := by
                rw [← optionEquivLeft_symbolicLineMvPolynomial]
                exact MvPolynomial.natDegree_optionEquivLeft
                  ℤ (symbolicLineMvPolynomial f x₀)
              _ ≤ f.totalDegree := symbolicLineMvPolynomial_degreeOf_none_le f x₀
              _ ≤ d := hdegree)
      have hscale : ((r : ℤ) ^ k).natAbs ≤ max 1 r ^ d := by
          rw [Int.natAbs_pow, Int.natAbs_natCast]
          exact (Nat.pow_le_pow_left (Nat.le_max_right 1 r) _).trans
            (pow_le_pow_right₀ (Nat.le_max_left 1 r) hkdegree)
      have hstar :=
        starCoefficient_coeff_natAbs_le f x₀ k mu d C H hcoeff hdegree hx₀
      exact (Nat.mul_le_mul hscale hstar).trans_eq (Nat.mul_comm _ _)
    _ = (symbolicLinePolynomial f x₀).support.card *
          ((f.support.card * C * (2 * max 1 H) ^ d) * max 1 r ^ d) := by simp
    _ ≤ (d + 1) * (f.support.card * C * (2 * max 1 H) ^ d) *
          max 1 r ^ d := by
      rw [mul_assoc]
      simpa [mul_assoc] using Nat.mul_le_mul_right
        ((f.support.card * C * (2 * max 1 H) ^ d) * max 1 r ^ d)
        (symbolicLinePolynomial_support_card_le x₀ f hdegree)

end

end TranslatedDepthSeven
