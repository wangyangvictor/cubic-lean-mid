import CubicTenVariables.DyadicFrequencyError
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-! Exact finite dyadic decomposition of the positive integer moduli.
The isolated modulus one and the final cutoff q≤Q are both retained. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteDyadicModuli
open DyadicFrequencyError
open scoped BigOperators

/-- The part of one real dyadic modulus block below the actual cutoff. -/
def block (Q j : ℕ) : Finset ℕ :=
  (moduli ((2:ℝ)^j)).filter (fun q => q ≤ Q)

@[simp] theorem mem_block (Q j q : ℕ) :
    q ∈ block Q j ↔ 2^j < q ∧ q ≤ 2^(j+1) ∧ q ≤ Q := by
  rw [block,Finset.mem_filter,mem_moduli]
  have hcast : ((2:ℝ)^j < (q:ℝ) ∧ (q:ℝ) ≤ 2*(2:ℝ)^j) ↔
      2^j < q ∧ q ≤ 2^(j+1) := by
    rw [pow_succ]
    constructor
    · intro h
      constructor
      · exact_mod_cast h.1
      · have hh : (q:ℝ) ≤ (2:ℝ)^j*2 := by linarith [h.2]
        exact_mod_cast hh
    · intro h
      constructor
      · exact_mod_cast h.1
      · have hh : (q:ℝ) ≤ (2:ℝ)^j*2 := by exact_mod_cast h.2
        linarith
  rw [hcast]
  tauto

/-- The logarithm of q-1 assigns powers of two to the preceding shell,
matching the strict lower and weak upper endpoint convention. -/
theorem exists_index (Q J q : ℕ) (hQ : Q ≤ 2^J) (hq : q ∈ Finset.Icc 2 Q) :
    ∃ j ∈ Finset.range J, q ∈ block Q j := by
  have hq2 := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  let j := Nat.log 2 (q-1)
  have hprev : q-1 ≠ 0 := by omega
  have hlo : 2^j < q := lt_of_le_of_lt (Nat.pow_log_le_self 2 hprev) (by omega)
  have hhi : q ≤ 2^(j+1) := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) (q-1)
    change q-1 < 2^(j+1) at h
    omega
  have hj : j < J := Nat.log_lt_of_lt_pow hprev (by omega : q-1 < 2^J)
  exact ⟨j,Finset.mem_range.mpr hj,(mem_block Q j q).mpr ⟨hlo,hhi,hqQ⟩⟩

theorem blocks_disjoint (Q : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (block Q i) (block Q j) := by
  apply Finset.disjoint_left.mpr
  intro q hi hj
  have hi' := (mem_block Q i q).mp hi
  have hj' := (mem_block Q j q).mp hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2^(i+1) ≤ 2^j := Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hij)
    omega
  · have hpow : 2^(j+1) ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hji)
    omega

/-- No modulus is omitted or counted twice. -/
theorem biUnion_eq_Icc (Q J : ℕ) (hQ : Q ≤ 2^J) :
    (Finset.range J).biUnion (block Q) = Finset.Icc 2 Q := by
  ext q
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j,hj,hq⟩
    have h := (mem_block Q j q).mp hq
    have hpow : 1 ≤ 2^j := Nat.one_le_pow j 2 (by decide)
    exact Finset.mem_Icc.mpr ⟨by omega,h.2.2⟩
  · exact exists_index Q J q hQ

/-- Literal finite sum identity, with the dyadic cutoff left as an if-test
inside the already-defined actual modulus set. -/
theorem sum_Icc_two_eq_dyadic {E : Type*} [AddCommMonoid E]
    (Q J : ℕ) (hQ : Q ≤ 2^J) (f : ℕ → E) :
    (∑ q ∈ Finset.Icc 2 Q, f q) =
      ∑ j ∈ Finset.range J, ∑ q ∈ moduli ((2:ℝ)^j), if q ≤ Q then f q else 0 := by
  classical
  rw [← biUnion_eq_Icc Q J hQ,Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_filter _ _
  · intro i _ j _ hij
    exact blocks_disjoint Q hij

/-- The modulus-one term remains separate from all strict dyadic blocks. -/
theorem sum_Icc_eq_one_add_dyadic {E : Type*} [AddCommMonoid E]
    (Q J : ℕ) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2^J) (f : ℕ → E) :
    (∑ q ∈ Finset.Icc 1 Q, f q) = f 1 +
      ∑ j ∈ Finset.range J, ∑ q ∈ moduli ((2:ℝ)^j), if q ≤ Q then f q else 0 := by
  rw [← sum_Icc_two_eq_dyadic Q J hQ f]
  have hsets : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext q
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [hsets,Finset.sum_insert]
  simp

/-- A canonical logarithmic block count. -/
def count (Q : ℕ) : ℕ := Nat.log 2 Q+1

theorem le_two_pow_count (Q : ℕ) : Q ≤ 2^(count Q) :=
  (Nat.lt_pow_succ_log_self (by decide : 1<2) Q).le

theorem sum_Icc_eq_one_add_blocks {E : Type*} [AddCommMonoid E]
    (Q : ℕ) (hQ : 1 ≤ Q) (f : ℕ → E) :
    (∑ q ∈ Finset.Icc 1 Q, f q) = f 1 +
      ∑ j ∈ Finset.range (count Q), ∑ q ∈ moduli ((2:ℝ)^j), if q ≤ Q then f q else 0 :=
  sum_Icc_eq_one_add_dyadic Q (count Q) hQ (le_two_pow_count Q) f

end CubicTenVariables.FiniteDyadicModuli
