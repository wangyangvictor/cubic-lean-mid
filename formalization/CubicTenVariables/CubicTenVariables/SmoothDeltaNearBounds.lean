import CubicTenVariables.SmoothDeltaAmplitudeDerivatives
import CubicTenVariables.SmoothDeltaFarDerivative
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform derivative bounds on the inner region of the actual smooth delta
amplitude. Only four positive summands can contribute to the varying part. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaNearBounds
open Finset SmoothDeltaCutoffs SmoothDeltaKernel SmoothDeltaAmplitudeDerivatives
open ReciprocalSmoothProfile
open scoped ContDiff Topology BigOperators

/-- The even cutoff and all its derivatives vanish in the central gap. -/
theorem Omega_deriv_eq_zero (j : ℕ) {v : ℝ} (hv : |v| < 1/4) :
    iteratedDeriv j Omega v = 0 := by
  have he : Set.EqOn Omega (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (-(1/4) : ℝ) (1/4)) := by
    intro z hz
    have h1 := omega_deriv_eq_zero 0 (v := z) (by
      intro hi
      linarith [hz.2,hi.1])
    have h2 := omega_deriv_eq_zero 0 (v := -z) (by
      intro hi
      linarith [hz.1,hi.1])
    simp only [iteratedDeriv_zero] at h1 h2
    simp [Omega,h1,h2]
  have hm : v ∈ Set.Ioo (-(1/4) : ℝ) (1/4) := abs_lt.mp hv
  have h := he.iteratedDeriv_of_isOpen isOpen_Ioo j hm
  simpa [iteratedDeriv_const] using h

/-- One bound for each fixed derivative of the fixed even cutoff. -/
theorem Omega_deriv_bound (j : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v : ℝ, |iteratedDeriv j Omega v| ≤ B := by
  have hs : HasCompactSupport Omega :=
    omega_hasCompactSupport.add (omega_hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))
  have hs' : HasCompactSupport (iteratedDeriv j Omega) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (hs.iteratedFDeriv j).comp_left (map_zero _)
  have hc : Continuous (iteratedDeriv j Omega) :=
    Omega_contDiff.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  obtain ⟨B,hB⟩ := hs'.exists_bound_of_continuous hc
  refine ⟨max 1 B,le_max_left _ _,fun v => ?_⟩
  have hv : |iteratedDeriv j Omega v| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB v
  exact hv.trans (le_max_right _ _)

/-- The varying part has at most four nonzero summands whenever `|y|≤q/Q`.
This statement includes order zero; it does not discard the constant first sum. -/
theorem varying_sum_bound (j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ v : ℝ, |iteratedDeriv j Omega v| ≤ B)
    {Q q : ℕ} (hQ : 0 < Q) (hq : 1 ≤ q) {y : ℝ}
    (hy : |y| ≤ (q : ℝ)/(Q : ℝ)) :
    |∑ k ∈ Icc 1 Q, ((Q : ℝ)/((q : ℝ)*(k : ℝ)))^(j+1) *
      iteratedDeriv j Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ)))| ≤
        4*B / ((q : ℝ)/(Q : ℝ))^(j+1) := by
  classical
  let x : ℝ := (q : ℝ)/(Q : ℝ)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hx : 0 < x := div_pos hqR hQR
  let f : ℕ → ℝ := fun k => ((Q : ℝ)/((q : ℝ)*(k : ℝ)))^(j+1) *
    iteratedDeriv j Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ)))
  let s := (Icc 1 Q).filter (fun k => k ≤ 4)
  have hzero (k : ℕ) (hk : k ∈ Icc 1 Q) (hks : k ∉ s) : f k = 0 := by
    have hk4 : 4 < k := by
      have hn : ¬ k ≤ 4 := fun hh => hks (mem_filter.mpr ⟨hk,hh⟩)
      omega
    have hkR : (4 : ℝ) < k := by exact_mod_cast hk4
    have hkpos : 0 < (k : ℝ) := by linarith
    have he : |y*(Q : ℝ)/((q : ℝ)*(k : ℝ))| = |y|/(x*(k : ℝ)) := by
      rw [abs_div,abs_mul,abs_of_pos hQR,abs_of_pos (mul_pos hqR hkpos)]
      dsimp [x]
      field_simp
    have hsmall : |y*(Q : ℝ)/((q : ℝ)*(k : ℝ))| < 1/4 := by
      rw [he]
      apply (div_lt_iff₀ (mul_pos hx hkpos)).mpr
      have hy' : |y| ≤ x := hy
      nlinarith
    simp only [f,Omega_deriv_eq_zero j hsmall,mul_zero]
  have he : (∑ k ∈ Icc 1 Q, f k) = ∑ k ∈ s, f k := by
    symm
    apply sum_subset (filter_subset _ _)
    exact hzero
  have hterm (k : ℕ) (hk : k ∈ s) : |f k| ≤ B/x^(j+1) := by
    have hk1 : 1 ≤ k := (mem_Icc.mp (mem_filter.mp hk).1).1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkpos : 0 < (k : ℝ) := zero_lt_one.trans_le hkR
    have ha : (Q : ℝ)/((q : ℝ)*(k : ℝ)) ≤ x⁻¹ := by
      have he : (Q : ℝ)/((q : ℝ)*(k : ℝ)) = (x*(k : ℝ))⁻¹ := by
        dsimp [x]
        field_simp
      rw [he]
      exact inv_anti₀ hx (by nlinarith)
    have han : 0 ≤ (Q : ℝ)/((q : ℝ)*(k : ℝ)) := by positivity
    calc
      |f k| = (((Q : ℝ)/((q : ℝ)*(k : ℝ)))^(j+1)) *
          |iteratedDeriv j Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ)))| := by
        dsimp only [f]
        rw [abs_mul,abs_of_nonneg (pow_nonneg han _)]
      _ ≤ (x⁻¹)^(j+1)*B :=
        mul_le_mul (pow_le_pow_left₀ han ha _) (hb _) (abs_nonneg _) (by positivity)
      _ = B/x^(j+1) := by rw [inv_pow]; ring
  have hcard : s.card ≤ 4 := by
    have hs : s ⊆ Icc 1 4 := by
      intro k hk
      exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩
    have hh := card_le_card hs
    norm_num at hh ⊢
    exact hh
  change |∑ k ∈ Icc 1 Q, f k| ≤ _
  rw [he]
  calc
    |∑ k ∈ s, f k| ≤ ∑ k ∈ s, |f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, B/x^(j+1) := sum_le_sum hterm
    _ = (s.card : ℝ)*(B/x^(j+1)) := by simp
    _ ≤ 4*(B/x^(j+1)) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 4*B / ((q : ℝ)/(Q : ℝ))^(j+1) := by dsimp [x]; ring

/-- The positive-order inner-region estimate has a constant depending only on
its derivative order, before every modulus and real parameter. -/
theorem exists_positive_order_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      ∀ y : ℝ, |y| ≤ (q : ℝ)/(Q : ℝ) →
        |iteratedDeriv j (h Q q) y| ≤ C / ((q : ℝ)/(Q : ℝ))^(j+1) := by
  obtain ⟨B,hB,hb⟩ := Omega_deriv_bound j
  refine ⟨4*B,by linarith,?_⟩
  intro Q hQ q hq _hqQ y hy
  rw [iteratedDeriv_h Q q j hj y,abs_neg]
  exact varying_sum_bound j B (by linarith) hb (by omega) hq hy

/-- The actual amplitude itself has the same inner-region estimate. The
constant first sum is bounded independently of both moduli. -/
theorem exists_zero_order_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      ∀ y : ℝ, |y| ≤ (q : ℝ)/(Q : ℝ) →
        |h Q q y| ≤ C / ((q : ℝ)/(Q : ℝ)) := by
  obtain ⟨A,hA,ha⟩ := SmoothDeltaFarDerivative.exists_first_sum_bound
  obtain ⟨B,hB,hb⟩ := Omega_deriv_bound 0
  refine ⟨A+4*B,by linarith,?_⟩
  intro Q hQ q hq hqQ y hy
  have he : h Q q y =
      (∑ k ∈ Icc 1 Q, (Q : ℝ)/((q : ℝ)*(k : ℝ)) *
        omega (((q : ℝ)*(k : ℝ))/(Q : ℝ))) -
      ∑ k ∈ Icc 1 Q, (Q : ℝ)/((q : ℝ)*(k : ℝ)) *
        Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ))) := by
    unfold h
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
  have hv := varying_sum_bound 0 B (by linarith) hb (by omega : 0 < Q) hq hy
  simp only [zero_add,pow_one,iteratedDeriv_zero] at hv
  rw [he]
  exact (abs_sub _ _).trans (by
    calc
      _ ≤ A/((q : ℝ)/(Q : ℝ)) + 4*B/((q : ℝ)/(Q : ℝ)) :=
        add_le_add (ha Q q (by omega) hq hqQ) hv
      _ = _ := by ring)

/-- Every fixed derivative of the literal finite amplitude has one uniform
inner-region bound, with the constant preceding `Q`, `q`, and `y`. -/
theorem exists_bound (j : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ q : ℕ, 1 ≤ q → q ≤ Q →
      ∀ y : ℝ, |y| ≤ (q : ℝ)/(Q : ℝ) →
        |iteratedDeriv j (h Q q) y| ≤ C / ((q : ℝ)/(Q : ℝ))^(j+1) := by
  by_cases hj : j = 0
  · subst j
    simpa only [zero_add,pow_one,iteratedDeriv_zero] using exists_zero_order_bound
  · exact exists_positive_order_bound j (by omega)

end CubicTenVariables.SmoothDeltaNearBounds
