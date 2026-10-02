import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The integral Taylor-to-tangent implication

This file proves, directly from the algebra of multivariate polynomials, the
first-order congruence used in the tangent-packet argument.  There is no
geometric hypothesis or external counting input here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators

open MvPolynomial Polynomial

variable {σ : Type*}

/-- Restrict a multivariate integral polynomial to the affine line
`y + T z`. -/
def linePolynomial (f : MvPolynomial σ ℤ) (y z : σ → ℤ) : Polynomial ℤ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i ↦ Polynomial.C (y i) + Polynomial.X * Polynomial.C (z i)) f

@[simp]
theorem linePolynomial_C (a : ℤ) (y z : σ → ℤ) :
    linePolynomial (MvPolynomial.C a) y z = Polynomial.C a := by
  simp [linePolynomial]

@[simp]
theorem linePolynomial_X (i : σ) (y z : σ → ℤ) :
    linePolynomial (MvPolynomial.X i) y z =
      Polynomial.C (y i) + Polynomial.X * Polynomial.C (z i) := by
  simp [linePolynomial]

@[simp]
theorem linePolynomial_add (f g : MvPolynomial σ ℤ) (y z : σ → ℤ) :
    linePolynomial (f + g) y z = linePolynomial f y z + linePolynomial g y z := by
  simp [linePolynomial]

@[simp]
theorem linePolynomial_mul (f g : MvPolynomial σ ℤ) (y z : σ → ℤ) :
    linePolynomial (f * g) y z = linePolynomial f y z * linePolynomial g y z := by
  simp [linePolynomial]

/-- Evaluating the line restriction at `t` gives evaluation of the original
polynomial at `y + t z`. -/
theorem linePolynomial_eval (f : MvPolynomial σ ℤ) (y z : σ → ℤ) (t : ℤ) :
    (linePolynomial f y z).eval t = MvPolynomial.eval (fun i ↦ y i + t * z i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [linePolynomial]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
      rw [linePolynomial_mul, Polynomial.eval_mul, hf]
      simp [linePolynomial]

variable [Fintype σ] [DecidableEq σ]

/-- The derivative at the origin of the line restriction is the directional
derivative of the multivariate polynomial. -/
theorem linePolynomial_derivative_eval_zero (f : MvPolynomial σ ℤ) (y z : σ → ℤ) :
    (linePolynomial f y z).derivative.eval 0 =
      ∑ i, MvPolynomial.eval y (MvPolynomial.pderiv i f) * z i := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [linePolynomial]
  | add f g hf hg =>
      simpa [hf, hg, add_mul] using
        (Finset.sum_add_distrib.symm :
          (∑ i, MvPolynomial.eval y (MvPolynomial.pderiv i f) * z i) +
              ∑ i, MvPolynomial.eval y (MvPolynomial.pderiv i g) * z i =
            ∑ i, (MvPolynomial.eval y (MvPolynomial.pderiv i f) * z i +
              MvPolynomial.eval y (MvPolynomial.pderiv i g) * z i))
  | mul_X f j hf =>
      classical
      rw [linePolynomial_mul, Polynomial.derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_mul]
      rw [linePolynomial_eval f y z 0]
      simp only [linePolynomial_X, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, one_mul, zero_mul, add_zero,
        MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib]
      rw [hf]
      simp [Pi.single_apply]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- A univariate polynomial taking the same value at `0` and at a nonzero
multiple of `p` has derivative at `0` divisible by `p`. -/
theorem dvd_derivative_eval_zero_of_eval_eq
    (g : Polynomial ℤ) {p q : ℤ} (hq : q ≠ 0) (hpq : p ∣ q)
    (heval : g.eval q = g.eval 0) :
    p ∣ g.derivative.eval 0 := by
  obtain ⟨h, hh⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := g) (a := (0 : ℤ))
  have hh' : g - Polynomial.C (g.eval 0) = Polynomial.X * h := by
    simpa using hh
  have hqzero : h.eval q = 0 := by
    have hev := congrArg (fun k : Polynomial ℤ ↦ k.eval q) hh'
    simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X] at hev
    rw [heval] at hev
    exact (mul_eq_zero.mp (by simpa using hev)).resolve_left hq
  have hp_diff : p ∣ h.eval q - h.eval 0 :=
    dvd_trans hpq (by simpa using Polynomial.sub_dvd_eval_sub q 0 h)
  have hp_hzero : p ∣ h.eval 0 := by
    rw [hqzero, zero_sub, dvd_neg] at hp_diff
    exact hp_diff
  have hderiv : g.derivative.eval 0 = h.eval 0 := by
    have hd := congrArg Polynomial.derivative hh'
    have hd0 := congrArg (fun k : Polynomial ℤ ↦ k.eval 0) hd
    simpa [Polynomial.derivative_mul] using hd0
  rwa [hderiv]

/-- **Integral Taylor-to-tangent bridge.** If two integral points `y` and
`y + qz` lie on the hypersurface `f = 0`, and `p ∣ q`, then the reduction
of `z` modulo `p` lies in the tangent hyperplane at `y` modulo `p`.

No primality assumption on `p` is needed for this algebraic implication.
-/
theorem tangent_congruence_of_two_zeros
    (f : MvPolynomial σ ℤ) (y z : σ → ℤ) {p q : ℤ}
    (hq : q ≠ 0) (hpq : p ∣ q)
    (hy : MvPolynomial.eval y f = 0)
    (hyqz : MvPolynomial.eval (fun i ↦ y i + q * z i) f = 0) :
    p ∣ ∑ i, MvPolynomial.eval y (MvPolynomial.pderiv i f) * z i := by
  rw [← linePolynomial_derivative_eval_zero f y z]
  apply dvd_derivative_eval_zero_of_eval_eq (linePolynomial f y z) hq hpq
  rw [linePolynomial_eval, linePolynomial_eval, hyqz]
  simpa using hy.symm

/-- The same tangent conclusion written literally over `ZMod p`: the
gradient row at `y` annihilates the displacement `z` modulo `p`. -/
theorem tangent_zmod_of_two_zeros
    (f : MvPolynomial σ ℤ) (y z : σ → ℤ) {p : ℕ} {q : ℤ}
    (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hy : MvPolynomial.eval y f = 0)
    (hyqz : MvPolynomial.eval (fun i ↦ y i + q * z i) f = 0) :
    ∑ i, (MvPolynomial.eval y (MvPolynomial.pderiv i f) : ZMod p) * (z i : ZMod p) = 0 := by
  have hdvd := tangent_congruence_of_two_zeros f y z hq hpq hy hyqz
  simpa only [← Int.cast_mul, ← Int.cast_sum, ZMod.intCast_zmod_eq_zero_iff_dvd] using hdvd

/-- Finite-family form of `tangent_congruence_of_two_zeros`, i.e. the
Jacobian of every defining equation annihilates the displacement modulo
`p`. -/
theorem jacobian_congruence_of_two_zeros
    {ι : Type*} (F : ι → MvPolynomial σ ℤ) (y z : σ → ℤ) {p q : ℤ}
    (hq : q ≠ 0) (hpq : p ∣ q)
    (hy : ∀ r, MvPolynomial.eval y (F r) = 0)
    (hyqz : ∀ r, MvPolynomial.eval (fun i ↦ y i + q * z i) (F r) = 0) :
    ∀ r, p ∣ ∑ i, MvPolynomial.eval y (MvPolynomial.pderiv i (F r)) * z i := by
  intro r
  exact tangent_congruence_of_two_zeros (F r) y z hq hpq (hy r) (hyqz r)

/-- Finite-family/Jacobian form written over `ZMod p`. -/
theorem jacobian_zmod_of_two_zeros
    {ι : Type*} (F : ι → MvPolynomial σ ℤ) (y z : σ → ℤ) {p : ℕ} {q : ℤ}
    (hq : q ≠ 0) (hpq : (p : ℤ) ∣ q)
    (hy : ∀ r, MvPolynomial.eval y (F r) = 0)
    (hyqz : ∀ r, MvPolynomial.eval (fun i ↦ y i + q * z i) (F r) = 0) :
    ∀ r, ∑ i, (MvPolynomial.eval y (MvPolynomial.pderiv i (F r)) : ZMod p) *
      (z i : ZMod p) = 0 := by
  intro r
  exact tangent_zmod_of_two_zeros (F r) y z hq hpq (hy r) (hyqz r)

end

end TranslatedDepthSeven
