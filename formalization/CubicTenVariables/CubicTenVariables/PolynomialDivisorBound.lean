import CubicTenVariables.PrimeFactorEpsilonBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Group.Constructions

/-! Elementary divisor estimates at nonzero values of fixed integral
polynomials. Constants precede the integer value, or all translated boxes.
The coordinate convention is the usual supremum norm on `Fin n → ℝ`. -/

noncomputable section
namespace CubicTenVariables.PolynomialDivisorBound
open MvPolynomial
open scoped BigOperators

/-- All positive divisors are bounded; no squarefreeness is needed. -/
theorem exists_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℤ, a ≠ 0 →
      (a.natAbs.divisors.card : ℝ) ≤ C * |(a : ℝ)| ^ ε := by
  classical
  obtain ⟨C,hC,hbound⟩ :=
    PrimeFactorEpsilonBound.exists_uniform_prime_factor_bound 2 (by norm_num) ε hε
  refine ⟨C,hC,?_⟩
  intro a ha
  have ha0 : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have hcard : a.natAbs.divisors.card ≤
      ∏ p ∈ a.natAbs.primeFactors, 2*a.natAbs.factorization p := by
    rw [Nat.card_divisors ha0]
    apply Finset.prod_le_prod'
    intro p hp
    have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd ha0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hcast : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs]
  exact (show (a.natAbs.divisors.card : ℝ) ≤
    ((∏ p ∈ a.natAbs.primeFactors, 2*a.natAbs.factorization p : ℕ) : ℝ)
      by exact_mod_cast hcard).trans (by simpa only [hcast] using hbound a.natAbs (by omega))

/-- The same constant bounds any finite family of positive integer divisors. -/
theorem exists_finite_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℤ, a ≠ 0 → ∀ Q : Finset ℕ,
      (∀ q ∈ Q, 0 < q ∧ (q : ℤ) ∣ a) →
      (Q.card : ℝ) ≤ C * |(a : ℝ)| ^ ε := by
  obtain ⟨C,hC,hbound⟩ := exists_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro a ha Q hQ
  have hsub : Q ⊆ a.natAbs.divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp (hQ q hq).2,
      Int.natAbs_ne_zero.mpr ha⟩
  exact (show (Q.card : ℝ) ≤ (a.natAbs.divisors.card : ℝ)
    by exact_mod_cast Finset.card_le_card hsub).trans (hbound a ha)

/-- A concrete positive coefficient bound. -/
def coefficientBound {n : ℕ} (P : MvPolynomial (Fin n) ℤ) : ℝ :=
  1 + ∑ d ∈ P.support, |((coeff d P : ℤ) : ℝ)|

theorem one_le_coefficientBound {n : ℕ} (P : MvPolynomial (Fin n) ℤ) :
    1 ≤ coefficientBound P := by
  unfold coefficientBound
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Actual evaluation is bounded by its coefficient sum and total degree. -/
theorem eval_abs_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (B : ℝ) (hB : 1 ≤ B) (x : Fin n → ℤ)
    (hx : ∀ i, |(x i : ℝ)| ≤ B) :
    |(eval x P : ℝ)| ≤ coefficientBound P * B^P.totalDegree := by
  classical
  have he : (eval x P : ℝ) =
      ∑ d ∈ P.support, ((coeff d P : ℤ) : ℝ) * ∏ i ∈ d.support, (x i : ℝ)^d i := by
    rw [eval_eq]
    push_cast
    rfl
  rw [he]
  calc
    _ ≤ ∑ d ∈ P.support, |((coeff d P : ℤ) : ℝ) *
        ∏ i ∈ d.support, (x i : ℝ)^d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, |((coeff d P : ℤ) : ℝ)| * B^P.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul,Finset.abs_prod]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        (∏ i ∈ d.support, |(x i : ℝ)^d i|) ≤ ∏ i ∈ d.support, B^d i := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro i _
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
        _ = B^(d.sum fun _ k => k) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ B^P.totalDegree := pow_le_pow_right₀ hB (le_totalDegree hd)
    _ = (∑ d ∈ P.support, |((coeff d P : ℤ) : ℝ)|) * B^P.totalDegree :=
      (Finset.sum_mul ..).symm
    _ ≤ coefficientBound P * B^P.totalDegree := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hB) _)
      unfold coefficientBound
      linarith

/-- Rescale the divisor exponent by the degree. The resulting constant is
chosen before the coordinate radius and the integer point. -/
theorem exists_coordinate_divisor_bound {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ x : Fin n → ℤ,
      (∀ i, |(x i : ℝ)| ≤ B) → eval x P ≠ 0 →
      ((eval x P).natAbs.divisors.card : ℝ) ≤ C * B^ε := by
  let η : ℝ := ε / ((P.totalDegree : ℝ)+1)
  have hden : 0 < (P.totalDegree : ℝ)+1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨A,hA,hdiv⟩ := exists_divisor_bound η hη
  have hcoeff := one_le_coefficientBound P
  have hcoeff0 : 0 ≤ coefficientBound P := zero_le_one.trans hcoeff
  have hcη : 1 ≤ coefficientBound P ^ η := Real.one_le_rpow hcoeff hη.le
  have hC : 1 ≤ A * coefficientBound P ^ η := by nlinarith
  refine ⟨A * coefficientBound P ^ η,hC,?_⟩
  intro B hB x hx hxP
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hexp : (P.totalDegree : ℝ)*η ≤ ε := by
    have he : ((P.totalDegree : ℝ)+1)*η = ε := by
      dsimp [η]
      field_simp
    nlinarith
  calc
    _ ≤ A * |(eval x P : ℝ)|^η := hdiv _ hxP
    _ ≤ A * (coefficientBound P * B^P.totalDegree)^η :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (eval_abs_le P B hB x hx) hη.le)
        (zero_le_one.trans hA)
    _ = (A * coefficientBound P^η) * B^((P.totalDegree : ℝ)*η) := by
      rw [Real.mul_rpow hcoeff0 (pow_nonneg hB0 _),← Real.rpow_natCast_mul hB0]
      ring
    _ ≤ (A * coefficientBound P^η) * B^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hB hexp)
        (zero_le_one.trans hC)

/-- The source-shaped translated-box bound uses the supremum norm of its
real center. It includes arbitrary finite sets of positive divisors. -/
theorem exists_translated_box_divisor_bound {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u : Fin n → ℝ, ∀ L : ℝ, 1 ≤ L →
      ∀ x : Fin n → ℤ, (∀ i, |(x i : ℝ)-u i| ≤ L) → eval x P ≠ 0 →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, 0 < q ∧ (q : ℤ) ∣ eval x P) →
      (Q.card : ℝ) ≤ C * (L+‖u‖)^ε := by
  obtain ⟨C,hC,hbound⟩ := exists_coordinate_divisor_bound P ε hε
  refine ⟨C,hC,?_⟩
  intro u L hL x hx hxP Q hQ
  have hB : 1 ≤ L+‖u‖ := hL.trans (le_add_of_nonneg_right (norm_nonneg _))
  have hxB (i : Fin n) : |(x i : ℝ)| ≤ L+‖u‖ := by
    have hui : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
    calc
      _ ≤ |(x i : ℝ)-u i| + |u i| := by
        simpa only [sub_add_cancel] using abs_add_le ((x i : ℝ)-u i) (u i)
      _ ≤ _ := add_le_add (hx i) hui
  have hsub : Q ⊆ (eval x P).natAbs.divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp (hQ q hq).2,
      Int.natAbs_ne_zero.mpr hxP⟩
  exact (show (Q.card : ℝ) ≤ ((eval x P).natAbs.divisors.card : ℝ)
    by exact_mod_cast Finset.card_le_card hsub).trans (hbound _ hB x hxB hxP)

/-- Polynomial growth in every nonnegative-radius translated real box. -/
theorem eval_abs_le_translated_box {n : ℕ} (P : MvPolynomial (Fin n) ℤ)
    (u : Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L) (x : Fin n → ℤ)
    (hx : ∀ i, |(x i : ℝ)-u i| ≤ L) :
    |(eval x P : ℝ)| ≤ coefficientBound P * (1+L+‖u‖)^P.totalDegree := by
  apply eval_abs_le P _ (by linarith [norm_nonneg u]) x
  intro i
  have hui : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i
  have he : |(x i : ℝ)| ≤ |(x i : ℝ)-u i| + |u i| := by
    simpa only [sub_add_cancel] using abs_add_le ((x i : ℝ)-u i) (u i)
  linarith [hx i]

/-- A single constant covers a fixed finite defining family. The nonvanishing
condition chooses a genuine nonzero value before applying any divisor bound. -/
theorem exists_family_translated_box_divisor_bound {n t : ℕ}
    (P : Fin t → MvPolynomial (Fin n) ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u : Fin n → ℝ, ∀ L : ℝ, 1 ≤ L →
      ∀ x : Fin n → ℤ, (∀ i, |(x i : ℝ)-u i| ≤ L) →
      (∃ j, eval x (P j) ≠ 0) → ∀ Q : Finset ℕ,
      (∀ q ∈ Q, 0 < q ∧ ∀ j, (q : ℤ) ∣ eval x (P j)) →
      (Q.card : ℝ) ≤ C * (L+‖u‖)^ε := by
  classical
  choose C hC hbound using fun j => exists_translated_box_divisor_bound (P j) ε hε
  have hnonneg (j : Fin t) : 0 ≤ C j := zero_le_one.trans (hC j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => hnonneg j
  refine ⟨1+∑ j, C j,by linarith,?_⟩
  intro u L hL x hx hnonzero Q hQ
  obtain ⟨j,hj⟩ := hnonzero
  have hCj : C j ≤ 1+∑ k, C k := by
    have he : C j ≤ ∑ k, C k :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
    linarith
  exact (hbound j u L hL x hx hj Q (fun q hq => ⟨(hQ q hq).1,
    (hQ q hq).2 j⟩)).trans
      (mul_le_mul_of_nonneg_right hCj (Real.rpow_nonneg (by linarith [norm_nonneg u]) _))

end CubicTenVariables.PolynomialDivisorBound
