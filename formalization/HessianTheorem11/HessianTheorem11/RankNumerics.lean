import Mathlib.Tactic

/-!
Exact arithmetic consequences of Proposition 11.1's first-normal-rank sieve.

The source-specific geometric sieve is not assumed to be a textbook theorem:
its individual numerical inequalities are hypotheses of these reductions.
Here `m` is generic Hessian corank, `h` determinant divisor multiplicity, and
`rho` the first normal rank. These lemmas contain no geometric input.
-/

namespace HessianTheorem11.RankNumerics

/-- In twelve variables, the first-normal-rank sieve already gives corank
at most two, so the ten-variable classification is unnecessary for this entry. -/
theorem corank_le_two_in_twelve
    (m h rho : ℕ) (hrho : rho ≤ m) (hmh : m ≤ h) (hh : 3 * h ≤ 12)
    (hnormal : 2 * m ≤ h + rho)
    (heven : 2 ≤ rho → 2 ∣ 12 - m - 2)
    (hfour : 3 ≤ rho → 4 ∣ 12 - m - 2) : m ≤ 2 := by
  by_contra hlarge
  have hm_cases : m = 3 ∨ m = 4 := by omega
  rcases hm_cases with rfl | rfl
  · have hr : 2 ≤ rho := by omega
    have hmod := Nat.mod_eq_zero_of_dvd (heven hr)
    norm_num at hmod
  · have hr : 3 ≤ rho := by omega
    have hmod := Nat.mod_eq_zero_of_dvd (hfour hr)
    norm_num at hmod

/-- In thirteen variables, divisor degree and the parity obstruction give
corank at most three. -/
theorem corank_le_three_in_thirteen
    (m h rho : ℕ) (hrho : rho ≤ m) (hmh : m ≤ h) (hh : 3 * h ≤ 13)
    (hnormal : 2 * m ≤ h + rho)
    (heven : 2 ≤ rho → 2 ∣ 13 - m - 2) : m ≤ 3 := by
  by_contra hlarge
  have hm : m = 4 := by omega
  have hr : 2 ≤ rho := by omega
  have hmod := Nat.mod_eq_zero_of_dvd (heven hr)
  norm_num [hm] at hmod

/-- Eleven variables have exactly one low-rank case left by this sieve:
corank two, first normal rank one, and divisor multiplicity three. -/
theorem eleven_remaining_alternative
    (m h rho : ℕ) (hrho : rho ≤ m) (hmh : m ≤ h) (hh : 3 * h ≤ 11)
    (hnormal : 2 * m ≤ h + rho)
    (heven : 2 ≤ rho → 2 ∣ 11 - m - 2)
    (hfour : 3 ≤ rho → 4 ∣ 11 - m - 2) :
    m ≤ 1 ∨ (m = 2 ∧ rho = 1 ∧ h = 3) := by
  by_cases hm : m ≤ 1
  · exact Or.inl hm
  right
  have hm_cases : m = 2 ∨ m = 3 := by omega
  rcases hm_cases with hm | hm
  · have hr : rho < 2 := by
      by_contra hhigher
      have hmod := Nat.mod_eq_zero_of_dvd (heven (by omega))
      norm_num [hm] at hmod
    exact ⟨hm, by omega, by omega⟩
  · have hr : 3 ≤ rho := by omega
    have hmod := Nat.mod_eq_zero_of_dvd (hfour hr)
    norm_num [hm] at hmod

/-- The source's parity/divisibility sieve is insufficient on its own to
prove the eleven-variable rank-ten entry. -/
theorem eleven_exception_satisfies_sieve :
    (1 : ℕ) ≤ 2 ∧ 2 ≤ 3 ∧ 3 * 3 ≤ 11 ∧ 2 * 2 ≤ 3 + 1 ∧
      (2 ≤ 1 → 2 ∣ 11 - 2 - 2) ∧ (3 ≤ 1 → 4 ∣ 11 - 2 - 2) := by
  norm_num

/-- The radical-line incidence estimates in the remaining eleven-variable
case force the classified singular rank-four equality case. -/
theorem radical_incidence_forces_rank_four_dimension_five
    (r t : ℕ) (hr : r ≤ 4) (hfibre : r + 1 ≤ t)
    (hradial : t + 3 ≤ 2 * r) : r = 4 ∧ t = 5 := by
  omega

end HessianTheorem11.RankNumerics
