import CubicTenVariables.LiftingCharacters
import CubicTenVariables.MixedRadixLifting

/-!
# Primitive scalar characters at prime-power modulus

The exact Ramanujan identity uses the original integer representatives and
positive exponential convention. The lower modulus is allowed to be one.
No estimate or convergence hypothesis enters this finite identity.
-/

noncomputable section

namespace CubicTenVariables.PrimePowerRamanujan

open scoped BigOperators

private theorem coprime_mixedRadix_iff_ne_zero (p s : ℕ) [Fact p.Prime]
    (a : Fin p) (e : Fin (p ^ s)) :
    Nat.Coprime (MixedRadixLifting.mixedRadixEquiv (p ^ s) p (a, e)).val
      (p ^ s * p) ↔ a.val ≠ 0 := by
  rw [MixedRadixLifting.mixedRadixEquiv_val, ← pow_succ,
    Nat.coprime_pow_right_iff (Nat.succ_pos s), Nat.coprime_add_mul_left_left,
    Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd,
    Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt a.isLt]

/-- The imprimitive scalar residues at level `s + 1` have exactly the
complete scalar character sum at level `s`. This includes `s = 0`. -/
theorem sum_nonprimitive_scalar (p s : ℕ) [Fact p.Prime] (b : ℤ) :
    (∑ a : Fin (p ^ (s + 1)),
      if Nat.Coprime a.val (p ^ (s + 1)) then (0 : ℂ)
      else residueExponential (p ^ (s + 1)) ((a.val : ℤ) * b)) =
      if (p ^ s : ℤ) ∣ b then (p ^ s : ℂ) else 0 := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ s) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  rw [pow_succ, MixedRadixLifting.sum_mixedRadix]
  simp_rw [coprime_mixedRadix_iff_ne_zero]
  have hzero : ∀ a : Fin p, a.val = 0 ↔ a = 0 := by
    intro a
    constructor
    · exact fun h => Fin.ext h
    · exact fun h => congrArg Fin.val h
  simp_rw [ne_eq, hzero, ite_not]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [MixedRadixLifting.mixedRadixEquiv_val, Fin.val_zero, zero_add,
    Nat.cast_mul]
  simp_rw [mul_assoc, LiftingCharacters.residueExponential_mul_modulus]
  simpa only [Nat.cast_pow] using LiftingCharacters.sum_scalar_phase (p ^ s) b

/-- Exact primitive scalar character sum for every prime-power modulus,
including the prime modulus when `s = 0`. -/
theorem sum_primitive_scalar (p s : ℕ) [Fact p.Prime] (b : ℤ) :
    (∑ a : Fin (p ^ (s + 1)),
      if Nat.Coprime a.val (p ^ (s + 1)) then
        residueExponential (p ^ (s + 1)) ((a.val : ℤ) * b) else 0) =
      (if (p ^ (s + 1) : ℤ) ∣ b then (p ^ (s + 1) : ℂ) else 0) -
        (if (p ^ s : ℤ) ∣ b then (p ^ s : ℂ) else 0) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hfull : (∑ a : Fin (p ^ (s + 1)),
      residueExponential (p ^ (s + 1)) ((a.val : ℤ) * b)) =
        if (p ^ (s + 1) : ℤ) ∣ b then (p ^ (s + 1) : ℂ) else 0 := by
    simpa only [Nat.cast_pow] using
      LiftingCharacters.sum_scalar_phase (p ^ (s + 1)) b
  rw [← hfull,
    ← sum_nonprimitive_scalar p s b, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end CubicTenVariables.PrimePowerRamanujan
