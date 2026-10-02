import TranslatedDepthSeven.JacobianCertificatePolynomialHeight
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ

/-!
# Coefficient bounds for characteristic polynomials of bounded matrices

Point-local Noether normalization represents multiplication by a remaining
coordinate by a finite matrix.  Its characteristic polynomial is one source
of the triangular equations.  This file proves a literal polynomial bound
for its coefficients.  The constants are the support size and largest
integral coefficient of the fixed universal characteristic polynomial.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset MvPolynomial Polynomial

/-- The elementary monomial evaluation bound, with an arbitrary finite
support index type. -/
theorem int_natAbs_finsupp_prod_pow_le_generic
    {ι : Type*} {e Y : ℕ} (y : ι → ℤ) (m : ι →₀ ℕ)
    (hy : ∀ i, (y i).natAbs ≤ Y)
    (hdegree : m.sum (fun _ exponent => exponent) ≤ e) :
    (m.prod fun i exponent => y i ^ exponent).natAbs ≤
      max 1 Y ^ e := by
  classical
  rw [Finsupp.prod]
  change Int.natAbsHom (∏ i ∈ m.support, y i ^ m i) ≤ _
  rw [map_prod]
  simp only [Int.natAbsHom_apply, Int.natAbs_pow]
  calc
    (∏ i ∈ m.support, (y i).natAbs ^ m i) ≤
        ∏ i ∈ m.support, max 1 Y ^ m i := by
      apply Finset.prod_le_prod'
      intro i _hi
      exact Nat.pow_le_pow_left
        ((hy i).trans (Nat.le_max_right 1 Y)) _
    _ = max 1 Y ^ ∑ i ∈ m.support, m i :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = max 1 Y ^ m.sum (fun _ exponent => exponent) := by
      rfl
    _ ≤ max 1 Y ^ e :=
      pow_le_pow_right₀ (Nat.le_max_left 1 Y) hdegree

/-- Direct evaluation bound from literal support, coefficient, degree, and
coordinate bounds. -/
theorem eval_natAbs_le_support_mul_coeff_mul_pow_generic
    {ι : Type*} {e C Y : ℕ} (f : MvPolynomial ι ℤ) (y : ι → ℤ)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ e)
    (hy : ∀ i, (y i).natAbs ≤ Y) :
    (MvPolynomial.eval y f).natAbs ≤
      f.support.card * C * max 1 Y ^ e := by
  classical
  have heval :
      MvPolynomial.eval y f =
        ∑ m ∈ f.support,
          f.coeff m * m.prod (fun i exponent => y i ^ exponent) := by
    conv_lhs => rw [f.as_sum]
    simp only [map_sum, MvPolynomial.eval_monomial]
  rw [heval]
  calc
    (∑ m ∈ f.support,
        f.coeff m * m.prod (fun i exponent => y i ^ exponent)).natAbs ≤
        ∑ m ∈ f.support,
          (f.coeff m *
            m.prod (fun i exponent => y i ^ exponent)).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _m ∈ f.support, C * max 1 Y ^ e := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hcoeff m hm)
        (int_natAbs_finsupp_prod_pow_le_generic y m hy
          ((MvPolynomial.le_totalDegree hm).trans hdegree))
    _ = f.support.card * C * max 1 Y ^ e := by
      simp [mul_assoc]

/-- Largest natural absolute value of a coefficient occurring in a literal
integral multivariate polynomial. -/
def mvPolynomialCoefficientNatAbsMax
    {ι : Type*} (f : MvPolynomial ι ℤ) : ℕ :=
  f.support.sup fun m => (f.coeff m).natAbs

theorem coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax
    {ι : Type*} (f : MvPolynomial ι ℤ) {m : ι →₀ ℕ}
    (hm : m ∈ f.support) :
    (f.coeff m).natAbs ≤ mvPolynomialCoefficientNatAbsMax f := by
  classical
  exact Finset.le_sup (s := f.support)
    (f := fun m => (f.coeff m).natAbs) hm

/-- The fixed support-size constant for one coefficient of the universal
`k × k` characteristic polynomial. -/
def universalCharpolyCoefficientSupportCard (k i : ℕ) : ℕ :=
  (((Matrix.charpoly.univ ℤ (Fin k)).coeff i) :
    MvPolynomial (Fin k × Fin k) ℤ).support.card

/-- The fixed coefficient-size constant for one coefficient of the
universal `k × k` characteristic polynomial. -/
def universalCharpolyCoefficientNatAbsMax (k i : ℕ) : ℕ :=
  mvPolynomialCoefficientNatAbsMax
    (((Matrix.charpoly.univ ℤ (Fin k)).coeff i) :
      MvPolynomial (Fin k × Fin k) ℤ)

/-- Every coefficient of the characteristic polynomial of an integral
matrix with entries bounded by `M` has an explicit polynomial bound.  For
fixed `k`, both constants preceding `max 1 M ^ k` are fixed natural
numbers. -/
theorem charpoly_coeff_natAbs_le_universal
    {k M : ℕ} (A : Matrix (Fin k) (Fin k) ℤ)
    (hentry : ∀ i j, (A i j).natAbs ≤ M) (i : ℕ) :
    (A.charpoly.coeff i).natAbs ≤
      universalCharpolyCoefficientSupportCard k i *
        universalCharpolyCoefficientNatAbsMax k i * max 1 M ^ k := by
  classical
  let f : MvPolynomial (Fin k × Fin k) ℤ :=
    (Matrix.charpoly.univ ℤ (Fin k)).coeff i
  let y : Fin k × Fin k → ℤ := fun ij => A ij.1 ij.2
  have heval : MvPolynomial.eval y f = A.charpoly.coeff i := by
    have h := Matrix.charpoly.univ_coeff_eval₂Hom
      (n := Fin k) (RingHom.id ℤ) y i
    change MvPolynomial.eval₂ (RingHom.id ℤ) y
        ((Matrix.charpoly.univ ℤ (Fin k)).coeff i) =
      (Matrix.of y.curry).charpoly.coeff i at h
    rw [MvPolynomial.eval₂_id] at h
    simpa [f, y] using h
  have hdegree : f.totalDegree ≤ k := by
    by_cases hi : i ≤ k
    · have hhom : f.IsHomogeneous (k - i) := by
        exact Matrix.charpoly.univ_coeff_isHomogeneous ℤ (Fin k)
          i (k - i) (by simpa using Nat.add_sub_of_le hi)
      exact hhom.totalDegree_le.trans (by omega)
    · have hzero : f = 0 := by
        have hnatDegree : (Matrix.charpoly.univ ℤ (Fin k)).natDegree = k := by
          simp
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (by simpa [hnatDegree] using (Nat.lt_of_not_ge hi))
      simp [hzero]
  rw [← heval]
  simpa [f, universalCharpolyCoefficientSupportCard,
    universalCharpolyCoefficientNatAbsMax] using
    (eval_natAbs_le_support_mul_coeff_mul_pow_generic f y
      (fun m hm =>
        coeff_natAbs_le_mvPolynomialCoefficientNatAbsMax f hm)
      hdegree (fun ij => hentry ij.1 ij.2))

end

end TranslatedDepthSeven
