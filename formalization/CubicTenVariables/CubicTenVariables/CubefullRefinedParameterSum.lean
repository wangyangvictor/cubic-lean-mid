import CubicTenVariables.CubefullRefinedParameters
import CubicTenVariables.PositiveReciprocalSum

/-! Rankin's bound for the five positive cubefull parameters. The refined
weight has abscissa at most 2/5, by five ordinary convergent power series. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubefullRefinedParameterSum
open CubefullRefinedParameters
open scoped BigOperators

def exponents (s : ℝ) : Fin 5 → ℝ := ![-4*s,-3*s,1-5*s,-6*s,1-7*s]

theorem exponent_lt (s : ℝ) (hs : 2/5 < s) (i : Fin 5) : exponents s i < -1 := by
  fin_cases i <;> norm_num [exponents] <;> linarith

/-- Arbitrary finite parameter sets are bounded by the product of five
convergent ordinary power series. -/
theorem exists_uniform_series_bound (s : ℝ) (hs : 2/5 < s) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Finset (Fin 5 → ℕ),
      (∑ t ∈ T, ∏ i : Fin 5, (t i : ℝ)^(exponents s i)) ≤ C := by
  classical
  have hex (i : Fin 5) := PositiveReciprocalSum.exists_uniform_rpow_bound
    (exponents s i) (exponent_lt s hs i)
  choose C hC hbound using hex
  have hCprod : 1 ≤ ∏ i, C i := by
    calc
      1 = ∏ _i : Fin 5, (1:ℝ) := by simp
      _ ≤ ∏ i, C i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hC i)
  refine ⟨∏ i, C i, hCprod, ?_⟩
  intro T
  let A (i : Fin 5) : Finset ℕ := T.image (fun t => t i)
  have hsub : T ⊆ Fintype.piFinset A := by
    intro t ht
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image_of_mem (fun t => t i) ht)
  calc
    _ ≤ ∑ t ∈ Fintype.piFinset A, ∏ i : Fin 5, (t i : ℝ)^(exponents s i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun t _ _ => Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = ∏ i : Fin 5, ∑ a ∈ A i, (a : ℝ)^(exponents s i) := (Finset.prod_univ_sum A (fun (i : Fin 5) (a : ℕ) => (a : ℝ)^(exponents s i))).symm
    _ ≤ ∏ i, C i := by
      exact Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun i _ => hbound i (A i))

/-- Exact monomial cancellation, before applying the real cutoff. -/
theorem rankin_identity (s : ℝ) (t : Fin 5 → ℕ) (ht : ∀ i, 0 < t i) :
    (t 2 : ℝ)*(t 4 : ℝ) =
      (modulus t : ℝ)^s * (∏ i : Fin 5, (t i : ℝ)^(exponents s i)) := by
  have hreal (i : Fin 5) : 0 < (t i : ℝ) := by exact_mod_cast ht i
  have hmod : 0 < (modulus t : ℝ) := by exact_mod_cast modulus_pos t ht
  apply Real.log_injOn_pos (mul_pos (hreal 2) (hreal 4))
    (mul_pos (Real.rpow_pos_of_pos hmod _) (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hreal i) _)))
  have hlogmod : Real.log (modulus t : ℝ) =
      ∑ i : Fin 5, (powers i : ℝ)*Real.log (t i : ℝ) := by
    rw [modulus, Nat.cast_prod, Real.log_prod (fun i _ => by
      simpa only [Nat.cast_pow] using (pow_ne_zero (powers i) (hreal i).ne'))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_pow, Real.log_pow]
  have hlogseries : Real.log (∏ i : Fin 5, (t i : ℝ)^(exponents s i)) =
      ∑ i : Fin 5, exponents s i * Real.log (t i : ℝ) := by
    rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hreal i) _).ne')]
    apply Finset.sum_congr rfl
    intro i _
    exact Real.log_rpow (hreal i) _
  rw [Real.log_mul (hreal 2).ne' (hreal 4).ne',
    Real.log_mul (Real.rpow_pos_of_pos hmod _).ne'
      (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hreal i) _)).ne',
    Real.log_rpow hmod, hlogmod, hlogseries]
  norm_num [powers, exponents, Fin.sum_univ_succ]
  simp only [show ((2 : Fin 3).succ.succ : Fin 5) = 4 by decide]
  ring

/-- Uniform refined weight average for all positive parameter families. -/
theorem exists_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ T : Finset (Fin 5 → ℕ),
      (∀ t ∈ T, ∀ i, 0 < t i) →
      (∀ t ∈ T, (modulus t : ℝ) ≤ X) →
      (∑ t ∈ T, (t 2 : ℝ)*(t 4 : ℝ)) ≤ C*X^((2:ℝ)/5+ε) := by
  obtain ⟨C,hC,hseries⟩ := exists_uniform_series_bound (2/5+ε) (by linarith)
  refine ⟨C,hC,?_⟩
  intro X hX T hpos hcut
  calc
    _ ≤ ∑ t ∈ T, X^((2:ℝ)/5+ε)*(∏ i : Fin 5, (t i : ℝ)^(exponents (2/5+ε) i)) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [rankin_identity _ t (hpos t ht)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcut t ht) (by linarith))
        (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = X^((2:ℝ)/5+ε)*(∑ t ∈ T, ∏ i : Fin 5, (t i : ℝ)^(exponents (2/5+ε) i)) :=
      (Finset.mul_sum ..).symm
    _ ≤ X^((2:ℝ)/5+ε)*C := mul_le_mul_of_nonneg_left (hseries T) (by positivity)
    _ = _ := mul_comm _ _

end CubicTenVariables.CubefullRefinedParameterSum
