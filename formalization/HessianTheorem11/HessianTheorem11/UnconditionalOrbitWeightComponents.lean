import HessianTheorem11.ReducedWeightCurve
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Weight components of a finite Laurent curve lying in a linear subspace
also lie in that subspace. This is polynomial coefficient extraction over
an infinite field, proved without a representation-theory input. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitWeights
open Module
variable {K V ι : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem powers_coefficients_mem (W : Submodule K V) (s : Finset ι) (k : ι → ℕ)
    (hk : Set.InjOn k (s : Set ι)) (v : ι → V)
    (hcurve : ∀ t : K, t ≠ 0 → (∑ i ∈ s, t ^ k i • v i) ∈ W)
    (i : ι) (hi : i ∈ s) : v i ∈ W := by
  classical
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W (v i)).mp
  intro l hl
  let P : Polynomial K := ∑ j ∈ s, Polynomial.monomial (k j) (l (v j))
  have hP : P = 0 := ReducedWeightCurve.polynomial_zero_of_nonzero_values P (by
    intro t ht
    have h := (Submodule.mem_dualAnnihilator l).mp hl _ (hcurve t ht)
    simpa [P,Polynomial.eval_finset_sum,map_sum,map_smul,mul_comm] using h)
  have he : P.coeff (k i) = l (v i) := by
    change (∑ j ∈ s, Polynomial.monomial (k j) (l (v j))).coeff (k i) = l (v i)
    rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hki : k j ≠ k i := fun h => hji (hk hj hi h)
      simp [Polynomial.coeff_monomial,hki]
    · exact fun h => (h hi).elim
  rw [hP,Polynomial.coeff_zero] at he
  exact he.symm

/-- Negative powers cause no difficulty: subtract the least occurring
integer weight, then extract ordinary polynomial coefficients. -/
theorem laurent_coefficients_mem (W : Submodule K V) (s : Finset ℤ) (v : ℤ → V)
    (hcurve : ∀ t : K, t ≠ 0 → (∑ j ∈ s, t ^ j • v j) ∈ W)
    (i : ℤ) (hi : i ∈ s) : v i ∈ W := by
  classical
  have hs : s.Nonempty := ⟨i,hi⟩
  let m : ℤ := s.inf' hs id
  have hm (j : ℤ) (hj : j ∈ s) : m ≤ j := Finset.inf'_le id hj
  let k : ℤ → ℕ := fun j => (j-m).toNat
  have hk : Set.InjOn k (s : Set ℤ) := by
    intro a ha b hb hab
    have ha' := hm a ha
    have hb' := hm b hb
    dsimp [k] at hab
    omega
  apply powers_coefficients_mem W s k hk v _ i hi
  intro t ht
  have h := W.smul_mem (t ^ (-m)) (hcurve t ht)
  have he : t ^ (-m) • (∑ j ∈ s, t ^ j • v j) = ∑ j ∈ s, t ^ k j • v j := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul,← zpow_add₀ ht]
    congr 1
    rw [← zpow_natCast,Int.toNat_of_nonneg (sub_nonneg.mpr (hm j hj))]
    congr 1
    omega
  rwa [he] at h

end HessianTheorem11.UnconditionalOrbitWeights
