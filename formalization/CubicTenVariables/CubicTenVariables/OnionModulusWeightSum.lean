import CubicTenVariables.OnionModulusParameters
import CubicTenVariables.PositiveReciprocalSum
import CubicTenVariables.OnionParameterSum
import CubicTenVariables.SquarefullModulusDecomposition

/-! Source-defined squarefull modulus weights and their parameter sums. -/

noncomputable section
namespace CubicTenVariables.OnionModulusWeightSum
open OnionModulusParameters SquarefreeResidueFactors
open scoped BigOperators

/-- The actual source weight is exactly the weight of the first two
positive parameters. -/
theorem weight_eq (c d : ℕ) (hc : 0 < c) (hd : Squarefree d) (hdc : d ∣ c) :
    (d : ℝ)^((1:ℝ)/2)*(d2 c d : ℝ)^((1:ℝ)/2) =
      (d1 c d : ℝ)^((1:ℝ)/2)*(d2 c d : ℝ) := by
  have hd20 : 0 < (d2 c d : ℝ) := by exact_mod_cast d2_pos c d hc hd hdc
  conv_lhs =>
    lhs
    rw [d_eq c d hc hd hdc, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [mul_assoc, ← Real.rpow_add hd20]
  norm_num

/-- Reindexing by the actual injective parameter map preserves the sum. -/
theorem sum_weight_eq_parameters (S : Finset (ℕ × ℕ))
    (hS : ∀ cd ∈ S, 0 < cd.1 ∧ Squarefree cd.2 ∧ cd.2 ∣ cd.1) :
    (∑ cd ∈ S, (cd.2 : ℝ)^((1:ℝ)/2)*(d2 cd.1 cd.2 : ℝ)^((1:ℝ)/2)) =
      ∑ t ∈ S.image (fun cd => parameters cd.1 cd.2),
        (t.1 : ℝ)^((1:ℝ)/2)*(t.2.1 : ℝ) := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro cd hcd
    exact weight_eq cd.1 cd.2 (hS cd hcd).1 (hS cd hcd).2.1 (hS cd hcd).2.2
  · intro x hx y hy hxy
    exact parameters_injOn (hS x hx) (hS y hy) hxy

/-- The weighted sum over any finite family of eligible source modulus
pairs has one uniform square-root-power bound. -/
theorem exists_pair_weight_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset (ℕ × ℕ),
      (∀ cd ∈ S, 0 < cd.1 ∧ Squarefree cd.2 ∧ cd.2 ∣ cd.1 ∧
        ((cd.1^2*cd.2 : ℕ) : ℝ) ≤ X) →
      (∑ cd ∈ S, (cd.2 : ℝ)^((1:ℝ)/2)*(d2 cd.1 cd.2 : ℝ)^((1:ℝ)/2)) ≤
        C*X^((1:ℝ)/2+δ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := OnionParameterSum.exists_uniform_bound δ hδ
  refine ⟨C,hC,?_⟩
  intro X hX S hS
  rw [sum_weight_eq_parameters S (fun cd hcd =>
    ⟨(hS cd hcd).1,(hS cd hcd).2.1,(hS cd hcd).2.2.1⟩)]
  apply hbound X hX
  · intro t ht
    obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp ht
    exact parameters_pos cd.1 cd.2 (hS cd hcd).1
      (hS cd hcd).2.1 (hS cd hcd).2.2.1
  · intro t ht
    obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp ht
    change (((d1 cd.1 cd.2)^3*(d2 cd.1 cd.2)^5*(e cd.1 cd.2)^2 : ℕ) : ℝ) ≤ X
    rw [← modulus_eq cd.1 cd.2 (hS cd hcd).1
      (hS cd hcd).2.1 (hS cd hcd).2.2.1]
    exact (hS cd hcd).2.2.2

/-- Canonical decomposition of positive moduli also preserves the sum. -/
theorem sum_weight_eq_canonical_pairs (Q : Finset ℕ)
    (hQ : ∀ r ∈ Q, 0 < r) :
    (∑ r ∈ Q, (SquarefullModulusDecomposition.d r : ℝ)^((1:ℝ)/2)*
      (d2 (SquarefullModulusDecomposition.c r) (SquarefullModulusDecomposition.d r) : ℝ)^((1:ℝ)/2)) =
      ∑ cd ∈ Q.image (fun r => (SquarefullModulusDecomposition.c r,
        SquarefullModulusDecomposition.d r)),
        (cd.2 : ℝ)^((1:ℝ)/2)*(d2 cd.1 cd.2 : ℝ)^((1:ℝ)/2) := by
  classical
  rw [Finset.sum_image]
  intro r hr s hs hrs
  exact SquarefullModulusDecomposition.parameters_injOn (hQ r hr) (hQ s hs) hrs

/-- The actual r-indexed weight bound for every finite family of positive
squarefull moduli. The constant precedes the cutoff and the family. -/
theorem exists_uniform_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ SquarefullModulusDecomposition.SquareFull r ∧ (r : ℝ) ≤ X) →
      (∑ r ∈ Q, (SquarefullModulusDecomposition.d r : ℝ)^((1:ℝ)/2)*
        (d2 (SquarefullModulusDecomposition.c r) (SquarefullModulusDecomposition.d r) : ℝ)^((1:ℝ)/2)) ≤
        C*X^((1:ℝ)/2+δ) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_pair_weight_bound δ hδ
  refine ⟨C,hC,?_⟩
  intro X hX Q hQ
  rw [sum_weight_eq_canonical_pairs Q (fun r hr => (hQ r hr).1)]
  apply hbound X hX
  intro cd hcd
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hcd
  refine ⟨SquarefullModulusDecomposition.c_pos r,
    SquarefullModulusDecomposition.d_squarefree r,
    SquarefullModulusDecomposition.d_dvd_c r (hQ r hr).2.1, ?_⟩
  rw [← SquarefullModulusDecomposition.eq_c_sq_mul_d r (hQ r hr).1]
  exact (hQ r hr).2.2

end CubicTenVariables.OnionModulusWeightSum
