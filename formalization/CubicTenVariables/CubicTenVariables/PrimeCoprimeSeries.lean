import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact separation of one prime from a series over positive natural numbers.
The coefficient factorization and convergence hypotheses are explicit; no
arithmetic singular-series estimate is asserted by this general adapter. -/

noncomputable section
namespace CubicTenVariables.PrimeCoprimeSeries
open scoped BigOperators

/-- Positive integers coprime to the selected prime. -/
abbrev CoprimePart (p : ℕ) := {m : ℕ // m ≠ 0 ∧ Nat.Coprime p m}

theorem factorization_prime_power_mul (p k m : ℕ) (hp : p.Prime)
    (hm : m ≠ 0) (hc : Nat.Coprime p m) : (p^k*m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm,
    Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hc), add_zero]

/-- Every positive integer has a unique prime-power part and coprime part. -/
def primeCoprimeEquiv (p : ℕ) (hp : p.Prime) : ℕ × CoprimePart p ≃ ℕ+ where
  toFun x := ⟨p^x.1*x.2, mul_pos (pow_pos hp.pos _) (Nat.pos_of_ne_zero x.2.2.1)⟩
  invFun n := (n.val.factorization p,
    ⟨ordCompl[p] n.val, (Nat.ordCompl_pos p n.pos.ne').ne',
      Nat.coprime_ordCompl hp n.pos.ne'⟩)
  left_inv := by
    rintro ⟨k,m,hm,hc⟩
    apply Prod.ext
    · exact factorization_prime_power_mul p k m hp hm hc
    · apply Subtype.ext
      change (p^k*m)/p^((p^k*m).factorization p) = m
      rw [factorization_prime_power_mul p k m hp hm hc]
      exact Nat.mul_div_cancel_left m (pow_pos hp.pos k)
  right_inv := by
    intro n
    apply Subtype.ext
    exact Nat.ordProj_mul_ordCompl_eq_self n.val p

@[simp] theorem primeCoprimeEquiv_apply (p : ℕ) (hp : p.Prime)
    (x : ℕ × CoprimePart p) :
    ((primeCoprimeEquiv p hp x : ℕ+) : ℕ) = p^x.1*x.2 := rfl

theorem summable_norm_pnat_iff (f : ℕ → ℂ) :
    Summable (fun q : ℕ+ => ‖f q‖) ↔ Summable (fun q : ℕ => ‖f q‖) :=
  (summable_pnat_iff_summable_succ (f := fun q => ‖f q‖)).trans
    (summable_nat_add_iff (f := fun q => ‖f q‖) 1)

/-- Absolute convergence follows from the literal prime/coprime split.
The prime-power coefficient may have an arbitrary constant term. -/
theorem summable_norm_of_split (p : ℕ) (hp : p.Prime)
    (f u : ℕ → ℂ) (v : CoprimePart p → ℂ)
    (hsplit : ∀ (k : ℕ) (m : CoprimePart p), f (p^k*m) = u k*v m)
    (hu : Summable (fun k => ‖u k‖)) (hv : Summable (fun m => ‖v m‖)) :
    Summable (fun q => ‖f q‖) := by
  apply (summable_norm_pnat_iff f).mp
  apply (primeCoprimeEquiv p hp).summable_iff.mp
  change Summable (fun x : ℕ × CoprimePart p => ‖f (p^x.1*x.2)‖)
  simp_rw [hsplit, norm_mul]
  exact hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- Exact factorization of the convergent series; no Euler factor is
normalized by silently replacing its constant term with one. -/
theorem tsum_of_split (p : ℕ) (hp : p.Prime)
    (f u : ℕ → ℂ) (v : CoprimePart p → ℂ) (hzero : f 0 = 0)
    (hsplit : ∀ (k : ℕ) (m : CoprimePart p), f (p^k*m) = u k*v m)
    (hu : Summable (fun k => ‖u k‖)) (hv : Summable (fun m => ‖v m‖)) :
    (∑' q : ℕ, f q) = (∑' k : ℕ, u k) * ∑' m : CoprimePart p, v m := by
  have hf := summable_norm_of_split p hp f u v hsplit hu hv
  calc
    (∑' q : ℕ, f q) = ∑' q : ℕ+, f q := by
      simpa only [hzero, zero_add] using (tsum_zero_pnat_eq_tsum_nat hf.of_norm).symm
    _ = ∑' x : ℕ × CoprimePart p, f (p^x.1*x.2) :=
      ((primeCoprimeEquiv p hp).tsum_eq (fun q : ℕ+ => f q)).symm
    _ = _ := by
      simp_rw [hsplit]
      exact (tsum_mul_tsum_of_summable_norm hu hv).symm

/-- Specialization to ordinary multiplicative coefficients. -/
theorem tsum_multiplicative (p : ℕ) (hp : p.Prime) (f : ℕ → ℂ)
    (hzero : f 0 = 0)
    (hmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a*b) = f a*f b)
    (hf : Summable (fun q => ‖f q‖)) :
    (∑' q : ℕ, f q) = (∑' k : ℕ, f (p^k)) * ∑' m : CoprimePart p, f m := by
  exact tsum_of_split p hp f (fun k => f (p^k)) (fun m => f m) hzero
    (fun k m => hmul (m.2.2.pow_left k))
    (hf.comp_injective (Nat.pow_right_injective hp.one_lt)) (hf.subtype _)

/-- Removing a nonnegative real prime factor preserves positivity of the
real part of a positive global series, without assuming the factor nonzero. -/
theorem coprime_tsum_re_pos (p : ℕ) (hp : p.Prime) (f : ℕ → ℂ)
    (hzero : f 0 = 0)
    (hmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a*b) = f a*f b)
    (hf : Summable (fun q => ‖f q‖)) (hpos : 0 < (∑' q, f q).re)
    (σ : ℝ) (hσ : 0 ≤ σ) (hlocal : (∑' k : ℕ, f (p^k)) = (σ : ℂ)) :
    0 < σ ∧ 0 < (∑' m : CoprimePart p, f m).re := by
  rw [tsum_multiplicative p hp f hzero hmul hf, hlocal] at hpos
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hpos
  have hv : 0 < (∑' m : CoprimePart p, f m).re := by nlinarith
  exact ⟨by nlinarith, hv⟩

end CubicTenVariables.PrimeCoprimeSeries
