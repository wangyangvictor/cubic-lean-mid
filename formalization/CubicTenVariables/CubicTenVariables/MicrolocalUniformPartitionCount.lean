import CubicTenVariables.MicrolocalPartitionCounts

/-! One counting constant for all six levels of the same actual partition.
The profile is exactly 10,8,7,5,4,1. Ordinary bounds acquire the harmless
height factor, which is at least one; the two high-level bounds already
contain it. No geometric, counting or literature assumption is added. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.MicrolocalUniformPartitionCount

open MicrolocalPromotedPartition ConeComponentProgressionCount
open scoped BigOperators

/-- The selected, proved counting exponents; no fractional refinement at
levels one or two is included. -/
def profile : Fin 6 → ℕ := ![10,8,7,5,4,1]

theorem profile_values : profile 0 = 10 ∧ profile 1 = 8 ∧ profile 2 = 7 ∧
    profile 3 = 5 ∧ profile 4 = 4 ∧ profile 5 = 1 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem ordinary_with_height (P : Set (Fin 10 → ℚ)) (r : ℕ)
    (ε : ℝ) (hε : 0 < ε)
    (hcount : ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points P u L m b).card : ℝ) ≤ C*(1+L/(m : ℝ))^r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points P u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^r := by
  obtain ⟨C,hC,hbound⟩ := hcount
  refine ⟨C,hC,?_⟩
  intro u L hL m hm b
  have hheight : 1 ≤ (2+‖u‖+L+(m : ℝ))^ε :=
    Real.one_le_rpow (by linarith [norm_nonneg u,Nat.cast_nonneg (α := ℝ) m]) hε.le
  apply (hbound u L hL m hm b).trans
  calc
    C*(1+L/(m : ℝ))^r = (C*1)*(1+L/(m : ℝ))^r := by ring
    _ ≤ (C*(2+‖u‖+L+(m : ℝ))^ε)*(1+L/(m : ℝ))^r :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (by linarith)) (by positivity)

private theorem per_level_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {U : ℕ → Set (Fin 10 → ℚ)} (hc : MicrolocalPartitionCounts.Counts f U)
    (ε : ℝ) (hε : 0 < ε) (j : Fin 6) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(profile j) := by
  fin_cases j
  · simpa [profile] using ordinary_with_height _ 10 ε hε hc.ambient
  · simpa [profile] using ordinary_with_height _ 8 ε hε (hc.low 1 (Or.inl rfl))
  · simpa [profile] using ordinary_with_height _ 7 ε hε (hc.low 2 (Or.inr rfl))
  · simpa [profile] using hc.high 3 (Or.inl rfl) ε hε
  · simpa [profile] using hc.high 4 (Or.inr rfl) ε hε
  · simpa [profile] using ordinary_with_height _ 1 ε hε
      (by simpa only [pow_one] using hc.terminal)

/-- A common constant is chosen before the level and every box,
progression, and residue. All six bounds concern the same literal part. -/
theorem exists_uniform_bound {t : ℕ}
    {f : Fin t → BihomogeneousIncidenceFamily.Polynomial 10 10}
    {U : ℕ → Set (Fin 10 → ℚ)} (hc : MicrolocalPartitionCounts.Counts f U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (j : Fin 6) (u : Fin 10 → ℝ) (L : ℝ), 0 ≤ L →
      ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
        ((points (part f U j) u L m b).card : ℝ) ≤
          C*(2+‖u‖+L+(m : ℝ))^ε*(1+L/(m : ℝ))^(profile j) := by
  classical
  choose C hC hbound using per_level_bound hc ε hε
  let A : ℝ := 1+∑ j : Fin 6, C j
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => (by linarith [hC j]))
  have hCA (j : Fin 6) : C j ≤ A := by
    have hs : C j ≤ ∑ k : Fin 6, C k :=
      Finset.single_le_sum (fun k _ => (by linarith [hC k])) (Finset.mem_univ j)
    dsimp [A]
    linarith
  refine ⟨A,hA,?_⟩
  intro j u L hL m hm b
  exact (hbound j u L hL m hm b).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCA j) (Real.rpow_nonneg (by positivity) _))
      (by positivity))

end CubicTenVariables.MicrolocalUniformPartitionCount
