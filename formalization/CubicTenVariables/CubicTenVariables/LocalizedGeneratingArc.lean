import CubicTenVariables.LocalizedGeneratingNumerators

/-! Integrability and exact finite-numerator interchange for the actual
localized generating function. The arc is contained in a compact interval;
continuity of the kernel therefore supplies every integrability premise.
No literature input or arithmetic estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.LocalizedGeneratingArc
open MvPolynomial MeasureTheory DeltaMethod
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- The finite physical generating function is continuous in its phase. -/
theorem continuous_generatingSum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    Continuous (localizedGeneratingSum G w A P W Ω) := by
  unfold localizedGeneratingSum finiteExponentialSum realExponential
  fun_prop

/-- Continuity after summing the actual coprime canonical numerators. -/
theorem continuous_numerator_sum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P q W : ℕ) (Ω : Set (Fin n → ZMod W)) :
    Continuous (fun θ : ℝ => ∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ) else 0) := by
  apply continuous_finset_sum
  intro a _
  by_cases ha : Nat.Coprime a.val q
  · simp only [if_pos ha]
    exact (continuous_generatingSum G w A P W Ω).comp (continuous_const.add continuous_id)
  · simp only [if_neg ha]
    exact continuous_const

/-- Each actual numerator summand is integrable against a continuous kernel
on the bounded delta-method arc. -/
theorem integrableOn_weighted_generatingSum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P Q q W a : ℕ)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : Continuous (p Q q)) :
    IntegrableOn (fun θ => p Q q θ * localizedGeneratingSum G w A P W Ω
      ((a : ℝ)/(q : ℝ)+θ)) (arc Q q η) := by
  have hc : Continuous (fun θ => p Q q θ * localizedGeneratingSum G w A P W Ω
      ((a : ℝ)/(q : ℝ)+θ)) :=
    hp.mul ((continuous_generatingSum G w A P W Ω).comp (continuous_const.add continuous_id))
  rw [arc_eq_Ioo]
  exact hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

/-- The complete coprime numerator sum, with the same kernel, is genuinely
integrable on the arc. -/
theorem integrableOn_weighted_sum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P Q q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : Continuous (p Q q)) :
    IntegrableOn (fun θ => p Q q θ * ∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ) else 0)
      (arc Q q η) := by
  have hc := hp.mul (continuous_numerator_sum G w A P q W Ω)
  rw [arc_eq_Ioo]
  exact hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self

/-- The actual numerator sum can be moved inside the phase integral.
Every required integrability statement is derived above from continuity. -/
theorem sum_integrals_eq_integral_sum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P Q q W : ℕ)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : Continuous (p Q q)) :
    (∑ a : Fin q, if Nat.Coprime a.val q then
      ∫ θ in arc Q q η, p Q q θ * localizedGeneratingSum G w A P W Ω
        ((a.val : ℝ)/(q : ℝ)+θ) else 0) =
    ∫ θ in arc Q q η, p Q q θ * ∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ) else 0 := by
  have hi (a : Fin q) : IntegrableOn (fun θ => if Nat.Coprime a.val q then
      p Q q θ * localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ)
      else 0) (arc Q q η) := by
    by_cases ha : Nat.Coprime a.val q
    · simp only [if_pos ha]
      exact integrableOn_weighted_generatingSum G w A P Q q W a.val Ω η p hp
    · simp only [if_neg ha]
      exact integrable_zero _ _ _
  simp_rw [Finset.mul_sum,mul_ite,mul_zero]
  rw [integral_finset_sum _ (fun a _ => hi a)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : Nat.Coprime a.val q
  · simp only [if_pos ha]
  · simp only [if_neg ha, integral_zero]

/-- Combined source-interval conversion and integral interchange. -/
theorem sum_Icc_integrals_eq_integral_sum (G : MvPolynomial (Fin n) ℤ)
    (w : (Fin n → ℝ) → ℝ) (A P Q q W : ℕ) (hq : 0 < q)
    (Ω : Set (Fin n → ZMod W)) (η : ℝ) (p : ℕ → ℕ → ℝ → ℂ)
    (hp : Continuous (p Q q)) :
    (∑ a ∈ Finset.Icc 1 q, if Nat.Coprime a q then
      ∫ θ in arc Q q η, p Q q θ * localizedGeneratingSum G w A P W Ω
        ((a : ℝ)/(q : ℝ)+θ) else 0) =
    ∫ θ in arc Q q η, p Q q θ * ∑ a : Fin q, if Nat.Coprime a.val q then
      localizedGeneratingSum G w A P W Ω ((a.val : ℝ)/(q : ℝ)+θ) else 0 := by
  rw [LocalizedGeneratingNumerators.sum_Icc_integrals_eq_sum_fin G w A P q W hq Ω
    (arc Q q η) (p Q q)]
  exact sum_integrals_eq_integral_sum G w A P Q q W Ω η p hp

end CubicTenVariables.LocalizedGeneratingArc
