import CubicTenVariables.FiniteVariableEquations
import Mathlib.Data.ZMod.Basic

/-! Actual common-zero counts of fixed integral equation families, and
elementary absorption of a fixed finite set of exceptional primes. -/

noncomputable section
namespace CubicTenVariables.IntegralEquationCounts
open MvPolynomial

/-- The count is of all residue solutions of the original integral
equations; it is not the reduction of a set of integral solutions. -/
def zeroCount {σ ι : Type*} (f : ι → MvPolynomial σ ℤ) (q : ℕ) : ℕ :=
  Nat.card {x : σ → ZMod q // ∀ i, eval₂ (Int.castRingHom (ZMod q)) x (f i) = 0}

theorem zeroCount_rename {σ τ ι : Type*} (e : σ ≃ τ)
    (f : ι → MvPolynomial σ ℤ) (q : ℕ) :
    zeroCount f q = zeroCount (fun i => rename e (f i)) q :=
  FiniteVariableEquations.natCard_zeros_rename e f (Int.castRingHom (ZMod q))

/-- The ambient residue space bounds every common-zero set. -/
theorem zeroCount_le_ambient {σ ι : Type*} [Fintype σ]
    (f : ι → MvPolynomial σ ℤ) (q : ℕ) [NeZero q] :
    zeroCount f q ≤ q^(Fintype.card σ) := by
  calc
    _ ≤ Nat.card (σ → ZMod q) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = _ := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]

/-- A single all-prime constant absorbs the fixed exceptional primes.
The good-prime bound is the explicit premise of this elementary helper;
the normalization endpoint supplies it in the final theorem. -/
theorem exists_all_prime_bound_of_good_prime_bound {σ ι : Type*} [Fintype σ]
    (f : ι → MvPolynomial σ ℤ) (r C D : ℕ) (hD : 1 ≤ D)
    (hgood : ∀ (p : ℕ), p.Prime → ¬ p ∣ D → zeroCount f p ≤ C*p^r) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (p : ℕ), p.Prime → zeroCount f p ≤ A*p^r := by
  refine ⟨1+C+D^(Fintype.card σ), by omega, ?_⟩
  intro p hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hpd : p ∣ D
  · have hpD : p ≤ D := Nat.le_of_dvd (by omega) hpd
    have hpow : p^(Fintype.card σ) ≤ D^(Fintype.card σ) := Nat.pow_le_pow_left hpD _
    have hp1 : 1 ≤ p^r := Nat.one_le_pow _ _ hp.one_lt.le
    calc
      _ ≤ p^(Fintype.card σ) := zeroCount_le_ambient f p
      _ ≤ D^(Fintype.card σ) := hpow
      _ ≤ 1+C+D^(Fintype.card σ) := by omega
      _ ≤ (1+C+D^(Fintype.card σ))*p^r := Nat.le_mul_of_pos_right _ (by omega)
  · exact (hgood p hp hpd).trans (Nat.mul_le_mul_right _ (by omega))

end CubicTenVariables.IntegralEquationCounts
