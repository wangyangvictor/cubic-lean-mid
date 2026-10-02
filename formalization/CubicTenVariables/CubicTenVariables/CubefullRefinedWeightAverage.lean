import CubicTenVariables.CubefullRefinedParameterSum
import CubicTenVariables.SquarefullModulusAverage

/-! The sharper cube-full average of the manuscript's literal d2 weight.
All arithmetic decompositions, injections and power-series estimates are
proved internally. One constant precedes every cutoff and finite family. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubefullRefinedWeightAverage
open CubefullRefinedParameters SquarefullModulusDecomposition
open scoped BigOperators

theorem sum_eq_parameters (Q : Finset ℕ)
    (hQ : ∀ r ∈ Q, 0 < r ∧ CubeFullSmithParameters.CubeFull r) :
    (∑ r ∈ Q, (weight r : ℝ)) =
      ∑ t ∈ Q.image parameters, (t 2 : ℝ)*(t 4 : ℝ) := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [weight_eq r (hQ r hr).2, Nat.cast_mul]
  · intro r hr s hs hrs
    exact CubefullRefinedParameters.parameters_injOn (hQ r hr) (hQ s hs) hrs

/-- Cumulative bound for any finite set of positive cube-full moduli. -/
theorem exists_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFullSmithParameters.CubeFull r ∧ (r : ℝ) ≤ X) →
      (∑ r ∈ Q, (SquarefreeResidueFactors.d2 (c r) (d r) : ℝ)) ≤
        C*X^((2:ℝ)/5+ε) := by
  classical
  obtain ⟨C,hC,hbound⟩ := CubefullRefinedParameterSum.exists_uniform_bound ε hε
  refine ⟨C,hC,?_⟩
  intro X hX Q hQ
  change (∑ r ∈ Q, (weight r : ℝ)) ≤ _
  rw [sum_eq_parameters Q (fun r hr => ⟨(hQ r hr).1,(hQ r hr).2.1⟩)]
  apply hbound X hX
  · intro t ht i
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    exact parameters_pos r i
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    rw [reconstruction r (hQ r hr).1 (hQ r hr).2.1]
    exact (hQ r hr).2.2

/-- Dyadic normalization, uniformly for every finite family under 2X. -/
theorem exists_dyadic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFullSmithParameters.CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      (∑ r ∈ Q, (SquarefreeResidueFactors.d2 (c r) (d r) : ℝ)) ≤
        C*X^((2:ℝ)/5+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_bound ε hε
  refine ⟨C*2^((2:ℝ)/5+ε),
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow (by norm_num) (by positivity)), ?_⟩
  intro X hX Q hQ
  have hb := hbound (2*X) (by linarith) Q hQ
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (zero_le_one.trans hX)] at hb
  simpa only [mul_assoc] using hb

/-- The actual source dyadic cube-full set, with no counting premise. -/
theorem exists_literal_cubefull_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ r ∈ SquarefullModulusAverage.cubeFullDyadic X,
        (SquarefreeResidueFactors.d2 (c r) (d r) : ℝ)) ≤ C*X^((2:ℝ)/5+ε) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_dyadic_bound ε hε
  refine ⟨C,hC,?_⟩
  intro X hX
  apply hbound X hX
  intro r hr
  obtain ⟨hrange,_,hcube⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrpos,hrcut⟩ := Finset.mem_Icc.mp hrange
  refine ⟨hrpos,hcube,?_⟩
  exact (by exact_mod_cast hrcut : (r : ℝ) ≤ (⌊2*X⌋₊ : ℝ)).trans
    (Nat.floor_le (by linarith : 0 ≤ 2*X))

end CubicTenVariables.CubefullRefinedWeightAverage
