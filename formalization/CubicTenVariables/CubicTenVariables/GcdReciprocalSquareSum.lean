import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Divisors

/-! A cutoff-free reciprocal-square sum with an actual gcd weight. Expanding
over common divisors and reindexing b=s*k cancels the divisor's square.
The convergent ordinary p-series supplies one absolute constant, before the
exceptional integer and every finite positive subfamily. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GcdReciprocalSquareSum
open scoped BigOperators Classical

def constant : ℝ := max 1 (∑' k : ℕ, 1/(k : ℝ)^2)

theorem constant_ge_one : 1 ≤ constant := le_max_left _ _

private theorem divisible_sum_le (s : ℕ) (hs : 1 ≤ s) (Q : Finset ℕ)
    (hQ : ∀ b ∈ Q, 1 ≤ b) :
    (∑ b ∈ Q, if s ∣ b then (s : ℝ)^2/(b : ℝ)^2 else 0) ≤ constant := by
  let R := Q.filter (fun b => s ∣ b)
  have hinj : Set.InjOn (fun b : ℕ => b/s) R := by
    intro a ha b hb hab
    calc
      a = s*(a/s) := (Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2).symm
      _ = s*(b/s) := congrArg (fun k => s*k) hab
      _ = b := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have heq (b : ℕ) (hb : b ∈ R) :
      (s : ℝ)^2/(b : ℝ)^2 = 1/((b/s : ℕ) : ℝ)^2 := by
    have hdiv := (Finset.mem_filter.mp hb).2
    have hmul : s*(b/s) = b := Nat.mul_div_cancel' hdiv
    have hk : b/s ≠ 0 := by
      intro hz
      have hb1 := hQ b (Finset.mem_filter.mp hb).1
      rw [hz,mul_zero] at hmul
      omega
    have hk0 : ((b/s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hk
    have hbr : (b : ℝ) = (s : ℝ)*((b/s : ℕ) : ℝ) := by exact_mod_cast hmul.symm
    rw [hbr,mul_pow]
    field_simp
  have hseries : Summable (fun k : ℕ => 1/(k : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  calc
    _ = ∑ b ∈ R, (s : ℝ)^2/(b : ℝ)^2 := by rw [Finset.sum_filter]
    _ = ∑ b ∈ R, 1/((b/s : ℕ) : ℝ)^2 := Finset.sum_congr rfl heq
    _ = ∑ k ∈ R.image (fun b => b/s), 1/(k : ℝ)^2 :=
      (Finset.sum_image (f := fun k : ℕ => 1/(k : ℝ)^2) hinj).symm
    _ ≤ ∑' k : ℕ, 1/(k : ℝ)^2 :=
      hseries.sum_le_tsum _ (fun k _ => by positivity)
    _ ≤ constant := le_max_right _ _

/-- There is no interval or upper-cutoff hypothesis, and the exceptional
integer contributes only its actual number of positive divisors. -/
theorem sum_le (Θ : ℕ) (hΘ : 1 ≤ Θ) (Q : Finset ℕ)
    (hQ : ∀ b ∈ Q, 1 ≤ b) :
    (∑ b ∈ Q, (Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2) ≤
      constant*(Θ.divisors.card : ℝ) := by
  have hΘ0 : Θ ≠ 0 := by omega
  have hexpand (b : ℕ) (_hb : b ∈ Q) :
      (Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2 ≤
        ∑ s ∈ Θ.divisors, if s ∣ b then (s : ℝ)^2/(b : ℝ)^2 else 0 := by
    have hg : Nat.gcd b Θ ∈ Θ.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right b Θ,hΘ0⟩
    have hb := Finset.single_le_sum
      (fun s _ => show 0 ≤ if s ∣ b then (s : ℝ)^2/(b : ℝ)^2 else 0 by
        split_ifs <;> positivity) hg
    simpa only [if_pos (Nat.gcd_dvd_left b Θ)] using hb
  calc
    _ ≤ ∑ b ∈ Q, ∑ s ∈ Θ.divisors,
        if s ∣ b then (s : ℝ)^2/(b : ℝ)^2 else 0 := Finset.sum_le_sum hexpand
    _ = ∑ s ∈ Θ.divisors, ∑ b ∈ Q,
        if s ∣ b then (s : ℝ)^2/(b : ℝ)^2 else 0 := Finset.sum_comm
    _ ≤ ∑ _s ∈ Θ.divisors, constant :=
      Finset.sum_le_sum (fun s hs => divisible_sum_le s (Nat.pos_of_mem_divisors hs) Q hQ)
    _ = constant*(Θ.divisors.card : ℝ) := by simp [mul_comm]

theorem exists_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ Θ : ℕ, 1 ≤ Θ →
    ∀ Q : Finset ℕ, (∀ b ∈ Q, 1 ≤ b) →
      (∑ b ∈ Q, (Nat.gcd b Θ : ℝ)^2/(b : ℝ)^2) ≤ C*(Θ.divisors.card : ℝ) :=
  ⟨constant,constant_ge_one,sum_le⟩

end CubicTenVariables.GcdReciprocalSquareSum
