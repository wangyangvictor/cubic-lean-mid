import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Absolute convergence of a multiplicative series follows from the sum
of its nonconstant prime-power norms. The finite Euler-factor identity is
used before global convergence is known; no infinite Euler-product identity
or arithmetic estimate is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PrimePowerMultiplicativeSummability
open scoped BigOperators

/-- Summability over every prime and every positive exponent implies
absolute convergence of the entire multiplicative series. The coefficient
at zero is zero and the constant Euler-factor coefficient is exactly one. -/
theorem summable_norm (A : ℕ → ℂ) (hA0 : A 0 = 0) (hA1 : A 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → A (m*n) = A m*A n)
    (hprime : Summable (fun pk : Nat.Primes × ℕ =>
      ‖A (pk.1.val ^ (pk.2+1))‖)) :
    Summable (fun n : ℕ => ‖A n‖) := by
  classical
  let a : ℕ → ℝ := fun n => ‖A n‖
  have ha0 : a 0 = 0 := by simp [a,hA0]
  have ha1 : a 1 = 1 := by simp [a,hA1]
  have ha : ∀ n, 0 ≤ a n := fun n => norm_nonneg _
  have hamul : ∀ {m n : ℕ}, m.Coprime n → a (m*n) = a m*a n := by
    intro m n hmn
    simp only [a,hmul hmn,norm_mul]
  have hsplit := (summable_prod_of_nonneg (fun pk : Nat.Primes × ℕ =>
    norm_nonneg (A (pk.1.val ^ (pk.2+1))))).mp hprime
  have hlocal (p : ℕ) (hp : p.Prime) : Summable (fun k => a (p^k)) :=
    (summable_nat_add_iff 1).mp (hsplit.1 ⟨p,hp⟩)
  let b : ℕ → ℝ := Set.indicator {p : ℕ | p.Prime}
    (fun p => ∑' k : ℕ, a (p^(k+1)))
  have hb : Summable b := summable_subtype_iff_indicator.mp hsplit.2
  have hbnonneg : ∀ p, 0 ≤ b p := by
    intro p
    by_cases hp : p.Prime
    · simp only [b,Set.indicator,Set.mem_setOf_eq,if_pos hp]
      exact tsum_nonneg fun k => ha _
    · simp [b,hp]
  have hfactor (p : ℕ) (hp : p.Prime) :
      (∑' k : ℕ, a (p^k)) = 1+b p := by
    rw [(hlocal p hp).tsum_eq_zero_add]
    simp only [pow_zero,ha1,b,Set.indicator,Set.mem_setOf_eq,if_pos hp]
  apply summable_of_sum_range_le ha
  intro N
  obtain ⟨hsmooth,heuler⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum ha1
      (fun hmn => hamul hmn)
      (fun {p} hp => by simpa only [Real.norm_eq_abs,abs_of_nonneg (ha _)] using hlocal p hp) N
  have hsmooth' : Summable (fun m : Nat.smoothNumbers N => a m) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (ha _)] using hsmooth
  have hind : Summable (Set.indicator (Nat.smoothNumbers N) a) :=
    summable_subtype_iff_indicator.mp hsmooth'
  have hrange : (∑ m ∈ Finset.range N, a m) =
      ∑ m ∈ Finset.range N, Set.indicator (Nat.smoothNumbers N) a m := by
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hm0 : m=0
    · simp [hm0,ha0,Set.indicator]
    · have hmem : m ∈ Nat.smoothNumbers N :=
        Nat.mem_smoothNumbers_iff_forall_le.mpr
          ⟨hm0,fun p hpm _ _ => hpm.trans_lt (Finset.mem_range.mp hm)⟩
      exact (Set.indicator_of_mem hmem a).symm
  calc
    ∑ m ∈ Finset.range N, a m =
        ∑ m ∈ Finset.range N, Set.indicator (Nat.smoothNumbers N) a m := hrange
    _ ≤ ∑' m, Set.indicator (Nat.smoothNumbers N) a m := by
      apply Summable.sum_le_tsum _ _ hind
      intro m _
      by_cases hm : m ∈ Nat.smoothNumbers N
      · simpa only [Set.indicator_of_mem hm] using ha m
      · simp only [Set.indicator_of_notMem hm,le_refl]
    _ = ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, a (p^k) := by
      rw [←tsum_subtype]
      exact heuler.tsum_eq
    _ = ∏ p ∈ Nat.primesBelow N, (1+b p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hfactor p (Nat.mem_primesBelow.mp hp).2
    _ ≤ ∏ p ∈ Nat.primesBelow N, Real.exp (b p) := by
      apply Finset.prod_le_prod
      · intro p _
        linarith [hbnonneg p]
      · intro p _
        simpa only [add_comm] using Real.add_one_le_exp (b p)
    _ = Real.exp (∑ p ∈ Nat.primesBelow N, b p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' p, b p) := Real.exp_le_exp.mpr
      (Summable.sum_le_tsum _ (fun p _ => hbnonneg p) hb)

end CubicTenVariables.PrimePowerMultiplicativeSummability
