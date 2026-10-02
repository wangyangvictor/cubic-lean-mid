import CubicTenVariables.CubefullSmithWeightLocal
import CubicTenVariables.FinitePrimeWeightSum
import CubicTenVariables.SquarefullModulusAverage

/-! The manuscript's actual weighted cube-full averages. The local factors,
finite Euler products, and Rankin argument are all proved internally. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubefullSmithWeightAverage
open CubefullSmithWeightLocal CubeFullSmithParameters
open scoped BigOperators

/-- Uniform finite Rankin series of the literal Smith weight. -/
theorem exists_series_bound (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r) →
      (∑ r ∈ Q, weight α r*(r : ℝ)^(-(threshold α+ε))) ≤ C := by
  obtain ⟨K,hK,hlocal⟩ := exists_local_bound α ε hα hα10 hε
  obtain ⟨C,hC,hbound⟩ := FinitePrimeWeightSum.exists_uniform_bound
    (localWeight α (threshold α+ε)) (localWeight_nonneg α (threshold α+ε)) (localWeight_zero α (threshold α+ε))
    ε K hε hK (fun p hp E => hlocal p hp.two_le E)
  refine ⟨C,hC,?_⟩
  intro Q hQ
  calc
    _ = ∑ r ∈ Q, ∏ p ∈ r.primeFactors, localWeight α (threshold α+ε) p (r.factorization p) :=
      Finset.sum_congr rfl (fun r hr => weighted_rankin_product α _ r (hQ r hr).1 (hQ r hr).2)
    _ ≤ C := hbound Q (fun r hr => (hQ r hr).1)

/-- Cumulative bound for every finite family of positive cube-full moduli.
The constant is fixed before the real cutoff and the family. -/
theorem exists_uniform_bound (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ X) →
      (∑ r ∈ Q, weight α r) ≤ C*X^(threshold α+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_series_bound α ε hα hα10 hε
  refine ⟨C,hC,?_⟩
  intro X hX Q hQ
  have hs : 0 ≤ threshold α+ε := by linarith [threshold_nonneg α]
  calc
    _ ≤ ∑ r ∈ Q, X^(threshold α+ε)*(weight α r*(r : ℝ)^(-(threshold α+ε))) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr0 : 0 < (r : ℝ) := by exact_mod_cast (hQ r hr).1
      have heq : weight α r = (r : ℝ)^(threshold α+ε)*
          (weight α r*(r : ℝ)^(-(threshold α+ε))) := by
        rw [mul_left_comm, ← Real.rpow_add hr0, add_neg_cancel, Real.rpow_zero, mul_one]
      calc
        _ = (r : ℝ)^(threshold α+ε)*(weight α r*(r : ℝ)^(-(threshold α+ε))) := heq
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hr0.le (hQ r hr).2.2 hs)
          (mul_nonneg (weight_nonneg α r) (Real.rpow_nonneg hr0.le _))
    _ = X^(threshold α+ε)*(∑ r ∈ Q, weight α r*(r : ℝ)^(-(threshold α+ε))) :=
      (Finset.mul_sum ..).symm
    _ ≤ X^(threshold α+ε)*C := mul_le_mul_of_nonneg_left
      (hbound Q (fun r hr => ⟨(hQ r hr).1,(hQ r hr).2.1⟩)) (by positivity)
    _ = _ := mul_comm _ _

/-- Dyadic upper-cutoff form, allowing arbitrary subfamilies. -/
theorem exists_dyadic_bound (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      (∑ r ∈ Q, weight α r) ≤ C*X^(threshold α+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound α ε hα hα10 hε
  have hs : 0 ≤ threshold α+ε := by linarith [threshold_nonneg α]
  refine ⟨C*2^(threshold α+ε),
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow (by norm_num) hs), ?_⟩
  intro X hX Q hQ
  have hb := hbound (2*X) (by linarith) Q hQ
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (zero_le_one.trans hX)] at hb
  simpa only [mul_assoc] using hb

/-- The source's actual dyadic set and literal omega/u weights. -/
theorem exists_literal_cubefull_bound (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X, omega r*u r^α) ≤
        C*X^(max 0 ((α-9)/12)+ε) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_dyadic_bound α ε hα hα10 hε
  refine ⟨C,hC,?_⟩
  intro X hX
  apply hbound X hX
  intro r hr
  obtain ⟨hrange,_,hcube⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrpos,hrcut⟩ := Finset.mem_Icc.mp hrange
  refine ⟨hrpos,hcube,?_⟩
  exact (by exact_mod_cast hrcut : (r : ℝ) ≤ (⌊2*X⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ 2*X))

/-- Alpha zero: no power loss beyond epsilon. -/
theorem exists_alpha_zero_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X, omega r) ≤ C*X^ε := by
  have h := exists_literal_cubefull_bound 0 ε (by norm_num) (by norm_num) hε
  norm_num at h ⊢
  exact h

/-- Alpha one: no power loss beyond epsilon. -/
theorem exists_alpha_one_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X, omega r*u r) ≤ C*X^ε := by
  have h := exists_literal_cubefull_bound 1 ε (by norm_num) (by norm_num) hε
  norm_num at h ⊢
  exact h

/-- Alpha nine: the critical case still has only epsilon loss. -/
theorem exists_alpha_nine_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X, omega r*u r^9) ≤ C*X^ε := by
  have h := exists_literal_cubefull_bound 9 ε (by norm_num) (by norm_num) hε
  norm_num at h ⊢
  exact h

/-- Alpha ten: the sharp Rankin threshold is one twelfth. -/
theorem exists_alpha_ten_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X, omega r*u r^10) ≤
        C*X^((1:ℝ)/12+ε) := by
  have h := exists_literal_cubefull_bound 10 ε (by norm_num) (by norm_num) hε
  norm_num at h ⊢
  exact h

end CubicTenVariables.CubefullSmithWeightAverage
