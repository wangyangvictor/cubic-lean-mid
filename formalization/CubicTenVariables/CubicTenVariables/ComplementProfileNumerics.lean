import CubicTenVariables.DyadicPowerSum

/-! The final numerical comparison for the six-term complementary bound.
This proves only the comparison of right-hand sides; the actual arithmetic
mean still requires the separate allocation and sieve estimates. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementProfileNumerics

theorem power_le_two_terms (x a : ℝ) (hx : 0 < x) (ha : 1 ≤ a) (ha9 : a ≤ 9) :
    x^a ≤ x+x^9 := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 ha
    rw [Real.rpow_one] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) ha9
    rw [Real.rpow_ofNat] at h
    exact h.trans (le_add_of_nonneg_left hx.le)

/-- The two endpoint powers of x=T/D^(1/3) dominate every term with
spatial exponent between one and nine and total D-exponent at most59/6. -/
theorem term_le (D T a b : ℝ) (hD : 1 ≤ D) (hT : 0 < T)
    (ha : 1 ≤ a) (ha9 : a ≤ 9) (hexp : a/3+b ≤ 59/6) :
    T^a*D^b ≤ D^((59 : ℝ)/6)*
      (T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  let x : ℝ := T/D^((1 : ℝ)/3)
  have hx : 0 < x := by dsimp [x]; positivity
  have hTD : T = x*D^((1 : ℝ)/3) := by
    dsimp [x]
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hD0 _))]
  have he : T^a*D^b = x^a*D^(a/3+b) := by
    conv_lhs => rw [hTD]
    rw [Real.mul_rpow hx.le (Real.rpow_nonneg hD0.le _),← Real.rpow_mul hD0.le,
      mul_assoc,← Real.rpow_add hD0]
    congr 2
    ring
  calc
    _ = x^a*D^(a/3+b) := he
    _ ≤ (x+x^9)*D^((59 : ℝ)/6) :=
      mul_le_mul (power_le_two_terms x a hx ha ha9)
        (Real.rpow_le_rpow_of_exponent_le hD hexp)
        (Real.rpow_nonneg hD0.le _) (by positivity)
    _ = _ := by dsimp [x]; ring

/-- Literal comparison of all six entries of the manuscript's conductor
table. The factor six is a fixed absolute constant. -/
theorem table_le (D T : ℝ) (hD : 1 ≤ D) (hT : 1 ≤ T) :
    T*D^9+T^9*D^((13 : ℝ)/2)+T^8*D^7+T^7*D^((15 : ℝ)/2)+
      T^5*D^8+T^4*D^((17 : ℝ)/2) ≤
        6*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have h1 := term_le D T 1 9 hD hT0 (by norm_num) (by norm_num) (by norm_num)
  have h2 := term_le D T 9 (13/2) hD hT0 (by norm_num) (by norm_num) (by norm_num)
  have h3 := term_le D T 8 7 hD hT0 (by norm_num) (by norm_num) (by norm_num)
  have h4 := term_le D T 7 (15/2) hD hT0 (by norm_num) (by norm_num) (by norm_num)
  have h5 := term_le D T 5 8 hD hT0 (by norm_num) (by norm_num) (by norm_num)
  have h6 := term_le D T 4 (17/2) hD hT0 (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one,Real.rpow_ofNat] at h1 h2 h3 h4 h5 h6
  linarith

end CubicTenVariables.ComplementProfileNumerics
