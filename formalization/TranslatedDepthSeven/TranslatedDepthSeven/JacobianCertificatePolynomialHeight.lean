import TranslatedDepthSeven.JacobianCertificateHeight

/-!
# Coefficient-height bounds for integral Jacobian certificates

The hypotheses in this file are literal bounds on the support, coefficients,
degree, and evaluation point of an integral multivariable polynomial.  They
give a deliberately crude pointwise bound for every evaluated partial
derivative, which can then be inserted directly into the determinant estimate
from `JacobianCertificateHeight`.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

/-- Triangle inequality for the natural absolute value of a finite sum of
integers. -/
theorem int_natAbs_sum_le_sum_natAbs
    {ι : Type*} (s : Finset ι) (g : ι → ℤ) :
    (∑ i ∈ s, g i).natAbs ≤ ∑ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- If every coordinate of `y` has absolute value at most `Y`, then a
monomial whose sum of exponents is at most `e` has absolute value at most
`max 1 Y ^ e`. -/
theorem int_natAbs_finsupp_prod_pow_le
    {N e Y : ℕ} (y : Fin N → ℤ) (m : Fin N →₀ ℕ)
    (hy : ∀ i, (y i).natAbs ≤ Y)
    (hdegree : m.sum (fun _ exponent ↦ exponent) ≤ e) :
    (m.prod fun i exponent ↦ y i ^ exponent).natAbs ≤
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
    _ = max 1 Y ^ m.sum (fun _ exponent ↦ exponent) := by
      rfl
    _ ≤ max 1 Y ^ e :=
      pow_le_pow_right₀ (Nat.le_max_left 1 Y) hdegree

/-- Literal support/degree/coefficient/point bounds imply a pointwise bound
for an evaluated partial derivative.  No assertion about the support or
coefficients of the derivative polynomial is used: the proof differentiates
the displayed monomial expansion of `f` term by term. -/
theorem eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow
    {N e C Y : ℕ} (f : MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (j : Fin N)
    (hcoeff : ∀ m ∈ f.support, (f.coeff m).natAbs ≤ C)
    (hdegree : f.totalDegree ≤ e)
    (hy : ∀ i, (y i).natAbs ≤ Y) :
    (MvPolynomial.eval y (MvPolynomial.pderiv j f)).natAbs ≤
      f.support.card * e * C * max 1 Y ^ e := by
  classical
  have heval :
      MvPolynomial.eval y (MvPolynomial.pderiv j f) =
        ∑ m ∈ f.support,
          MvPolynomial.eval y
            (MvPolynomial.pderiv j
              (MvPolynomial.monomial m (f.coeff m))) := by
    conv_lhs =>
      rw [f.as_sum]
    simp only [map_sum]
  rw [heval]
  calc
    (∑ m ∈ f.support,
        MvPolynomial.eval y
          (MvPolynomial.pderiv j
            (MvPolynomial.monomial m (f.coeff m)))).natAbs ≤
        ∑ m ∈ f.support,
          (MvPolynomial.eval y
            (MvPolynomial.pderiv j
              (MvPolynomial.monomial m (f.coeff m)))).natAbs :=
      int_natAbs_sum_le_sum_natAbs _ _
    _ ≤ ∑ _m ∈ f.support, e * C * max 1 Y ^ e := by
      apply Finset.sum_le_sum
      intro m hm
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.eval_monomial]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      have hmdegree :
          m.sum (fun _ exponent ↦ exponent) ≤ e :=
        (MvPolynomial.le_totalDegree hm).trans hdegree
      have hmj : m j ≤ e := by
        by_cases hmjzero : m j = 0
        · simp [hmjzero]
        · have hjmem : j ∈ m.support :=
            Finsupp.mem_support_iff.mpr hmjzero
          have hmjSum : m j ≤ ∑ i ∈ m.support, m i :=
            Finset.single_le_sum_of_canonicallyOrdered hjmem
          exact hmjSum.trans hmdegree
      have hmonomial :
          ((m - Finsupp.single j 1).prod
            fun i exponent ↦ y i ^ exponent).natAbs ≤ max 1 Y ^ e := by
        apply int_natAbs_finsupp_prod_pow_le y
        · exact hy
        · have hsubsum :
              (m - Finsupp.single j 1).sum
                  (fun _ exponent ↦ exponent) ≤
                m.sum (fun _ exponent ↦ exponent) := by
              rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl),
                Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
              apply Finset.sum_le_sum
              intro i _hi
              exact Nat.sub_le _ _
          exact hsubsum.trans hmdegree
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (hcoeff m hm) hmj) hmonomial |>.trans_eq (by ac_rfl)
    _ = f.support.card * e * C * max 1 Y ^ e := by
      simp [mul_assoc]

/-- Uniform literal support/degree/coefficient/point bounds for a displayed
family of equations, together with the rational Jacobian-rank hypothesis,
produce an honest nonzero integral Jacobian minor and an explicit height
bound for it. -/
theorem exists_bounded_nonzero_integralJacobianMinor_of_polynomial_bounds
    {c N r S e C Y : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (hrank : r ≤
      ((integralJacobianMatrix F y).map
        (Int.castRingHom ℚ)).rank)
    (hsupport : ∀ i, (F i).support.card ≤ S)
    (hcoeff : ∀ i m, m ∈ (F i).support → ((F i).coeff m).natAbs ≤ C)
    (hdegree : ∀ i, (F i).totalDegree ≤ e)
    (hy : ∀ j, (y j).natAbs ≤ Y) :
    ∃ rows : Fin r → Fin c, ∃ cols : Fin r → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor F y rows cols ≠ 0 ∧
        (integralJacobianMinor F y rows cols).natAbs ≤
          r.factorial *
            (S * e * C * max 1 Y ^ e) ^ r := by
  apply exists_bounded_nonzero_integralJacobianMinor F y hrank
  intro i j
  change (MvPolynomial.eval y (MvPolynomial.pderiv j (F i))).natAbs ≤ _
  calc
    (MvPolynomial.eval y (MvPolynomial.pderiv j (F i))).natAbs ≤
        (F i).support.card * e * C * max 1 Y ^ e :=
      eval_pderiv_natAbs_le_support_mul_degree_mul_coeff_mul_pow
        (F i) y j (hcoeff i) (hdegree i) hy
    _ = (F i).support.card * (e * C * max 1 Y ^ e) := by ac_rfl
    _ ≤ S * (e * C * max 1 Y ^ e) :=
      Nat.mul_le_mul_right _ (hsupport i)
    _ = S * e * C * max 1 Y ^ e := by ac_rfl

end

end TranslatedDepthSeven
