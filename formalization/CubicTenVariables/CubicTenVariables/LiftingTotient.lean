import CubicTenVariables.MixedRadixLifting
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Exact unit counts for first lifting

The finite unit count uses the literal representatives a : Fin M with
Coprime a.val M. Mixed-radix reindexing proves totient(A*M)=A*totient(M)
when A divides M; no radical or asymptotic estimate is an input.
-/

namespace CubicTenVariables.LiftingTotient
open scoped BigOperators
open MixedRadixLifting

theorem card_coprime_fin (M : ℕ) :
    (Finset.univ.filter (fun a : Fin M => Nat.Coprime a.val M)).card = Nat.totient M := by
  simp only [Nat.totient, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.coprime_comm]
  exact Fin.sum_univ_eq_sum_range (fun a => if M.Coprime a then (1 : ℕ) else 0) M

theorem natCard_coprime_fin (M : ℕ) :
    Nat.card {a : Fin M // Nat.Coprime a.val M} = Nat.totient M := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using card_coprime_fin M

theorem sum_coprime_indicator (M : ℕ) :
    (∑ a : Fin M, if Nat.Coprime a.val M then 1 else 0) = Nat.totient M := by
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using card_coprime_fin M

/-- The exact multiplicative factor from the high unit digit. The proof
also handles zero moduli; the lifting application supplies positivity. -/
theorem totient_mul_of_dvd (A M : ℕ) (hAM : A ∣ M) :
    A * Nat.totient M = Nat.totient (A*M) := by
  rw [← sum_coprime_indicator (A*M), sum_mixedRadix A M]
  simp_rw [coprime_mixedRadix_iff A M hAM]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.mul_sum, sum_coprime_indicator]

theorem sum_coprime_const (M : ℕ) (z : ℝ) :
    (∑ a : Fin M, if Nat.Coprime a.val M then z else 0) = (Nat.totient M : ℝ)*z := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, card_coprime_fin, nsmul_eq_mul]

theorem real_lifting_factor (A M n : ℕ) (hAM : A ∣ M) :
    (A : ℝ)^(n+1)*(Nat.totient M : ℝ) = (A : ℝ)^n*(Nat.totient (A*M) : ℝ) := by
  have h : A^(n+1)*Nat.totient M = A^n*Nat.totient (A*M) := by
    rw [pow_succ, mul_assoc, totient_mul_of_dvd A M hAM]
  exact_mod_cast h

/-- The source's M=A*T specialization, with exactly the coefficient A. -/
theorem totient_firstLift (A T : ℕ) :
    A * Nat.totient (A*T) = Nat.totient (A^2*T) := by
  simpa only [pow_two, mul_assoc] using totient_mul_of_dvd A (A*T) (dvd_mul_right A T)

end CubicTenVariables.LiftingTotient
