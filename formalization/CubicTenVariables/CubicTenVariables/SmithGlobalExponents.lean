import CubicTenVariables.SmithProfileMassBound

/-! Finite-product real-exponent algebra for the global Smith estimate. -/

noncomputable section
namespace CubicTenVariables.SmithGlobalExponents
open SmithProfileNumerics
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem prod_power_rpow (p a : ι → ℕ) (u : ℝ) :
    (∏ i, (p i : ℝ)^((a i : ℝ)*u)) = ((∏ i, p i^a i : ℕ) : ℝ)^u := by
  calc
    _ = ∏ i, ((p i : ℝ)^(a i))^u := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.rpow_natCast_mul (Nat.cast_nonneg _)]
    _ = (∏ i, (p i : ℝ)^(a i))^u :=
      Real.finset_prod_rpow _ _ (fun i _ => pow_nonneg (Nat.cast_nonneg _) _) u
    _ = _ := by simp only [Nat.cast_prod, Nat.cast_pow]

theorem prod_rpow_add (p : ι → ℕ) (hp : ∀ i, 0 < p i) (x y : ι → ℝ) :
    (∏ i, (p i : ℝ)^(x i+y i)) = (∏ i, (p i : ℝ)^x i)*(∏ i, (p i : ℝ)^y i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.rpow_add (by exact_mod_cast hp i) _ _

/-- All local exponents are signed real exponents. -/
theorem combined_exponents (p a t : ι → ℕ) (hp : ∀ i, 0 < p i)
    (b : ι → ℝ) (ε : ℝ) :
    ((∏ i, p i^a i : ℕ) : ℝ)^10 *
        (((∏ i, p i^a i)^2*(∏ i, p i^t i) : ℕ) : ℝ) *
        (∏ i, (p i : ℝ)^(10*(t i : ℝ)+b i+ε*(a i : ℝ))) =
      ((∏ i, p i^a i : ℕ) : ℝ)^ε *
        ∏ i, (p i : ℝ)^(12*(a i : ℝ)+11*(t i : ℝ)+b i) := by
  have h₁ : (∏ i, (p i : ℝ)^(10*(t i : ℝ)+b i+ε*(a i : ℝ))) =
      ((∏ i, p i^t i : ℕ) : ℝ)^10 * (∏ i, (p i : ℝ)^b i) *
        ((∏ i, p i^a i : ℕ) : ℝ)^ε := by
    rw [prod_rpow_add p hp, prod_rpow_add p hp]
    have ht := prod_power_rpow p t 10
    have ha := prod_power_rpow p a ε
    simp_rw [mul_comm (10 : ℝ), mul_comm ε]
    rw [ht, ha]
    norm_num
  have h₂ : (∏ i, (p i : ℝ)^(12*(a i : ℝ)+11*(t i : ℝ)+b i)) =
      ((∏ i, p i^a i : ℕ) : ℝ)^12 * ((∏ i, p i^t i : ℕ) : ℝ)^11 *
        ∏ i, (p i : ℝ)^b i := by
    rw [prod_rpow_add p hp, prod_rpow_add p hp]
    have ha := prod_power_rpow p a 12
    have ht := prod_power_rpow p t 11
    simp_rw [mul_comm (12 : ℝ), mul_comm (11 : ℝ)]
    rw [ha, ht]
    norm_num
  rw [h₁, h₂, Nat.cast_mul, Nat.cast_pow]
  ring

theorem combined_localD (p a t : ι → ℕ) (hp : ∀ i, 0 < p i) (ε : ℝ) :
    ((∏ i, p i^a i : ℕ) : ℝ)^10 *
        (((∏ i, p i^a i)^2*(∏ i, p i^t i) : ℕ) : ℝ) *
        (∏ i, (p i : ℝ)^(((10*t i : ℕ) : ℝ)+(phi (a i) (t i) : ℝ)+ε*(a i : ℝ))) =
      ((∏ i, p i^a i : ℕ) : ℝ)^ε *
        ∏ i, (p i : ℝ)^(localD (a i) (t i) : ℝ) := by
  simpa only [localD, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    combined_exponents p a t hp (fun i => (phi (a i) (t i) : ℝ)) ε

theorem parameter_rpow_le (A T : ℕ) (hA : 0 < A) (hT : 0 < T)
    (ε : ℝ) (hε : 0 ≤ ε) : (A : ℝ)^ε ≤ ((A^2*T : ℕ) : ℝ)^ε := by
  apply Real.rpow_le_rpow (Nat.cast_nonneg A) _ hε
  exact_mod_cast (show A ≤ A^2*T by
    have h : A ≤ A^2 := Nat.le_self_pow (by omega) A
    exact h.trans (Nat.le_mul_of_pos_right _ hT))

end CubicTenVariables.SmithGlobalExponents
