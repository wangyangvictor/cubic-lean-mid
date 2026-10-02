import CubicTenVariables.CubefullSmithWeightLocal

/-! Exact identities for the actual Smith modulus and weight ratio, and
the progression-width comparison needed in Plan Alpha (4.7). The scale
comparison is an inequality and does not assume an exact dyadic product. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaParameterRatios
open CubeFullSmithParameters
open CubefullSmithWeightLocal (u)

theorem A_dvd (r : ℕ) (hr : 0 < r) : A r ∣ r := by
  have h : A r ∣ (A r)^2 := by rw [pow_two]; exact dvd_mul_right _ _
  exact h.trans (A_sq_dvd_r r hr)

theorem A_le (r : ℕ) (hr : 0 < r) : A r ≤ r := Nat.le_of_dvd hr (A_dvd r hr)

/-- The exact cubic identity for the selected Smith modulus. It holds
for every positive modulus, even without cube-fullness. -/
theorem A_cube (r : ℕ) (hr : 0 < r) :
    (A r : ℝ)^3 = (r : ℝ)*(z r 2 : ℝ)/(z r 1 : ℝ) := by
  have hz1 : (z r 1 : ℝ) ≠ 0 := by exact_mod_cast (z_pos r 1).ne'
  have he : (r : ℝ) = (b r : ℝ)^3*(z r 1 : ℝ)*(z r 2 : ℝ)^2 := by
    exact_mod_cast eq_b_cube_z r hr
  rw [he]
  unfold A
  push_cast
  field_simp

/-- The literal weight ratio is the cube root of r divided by A(r). -/
theorem cube_root_div_A (r : ℕ) (hr : 0 < r) :
    (r : ℝ)^((1 : ℝ)/3)/(A r : ℝ) = u r := by
  have hA : 0 < (A r : ℝ) := by exact_mod_cast A_pos r
  have hz1 : 0 < (z r 1 : ℝ) := by exact_mod_cast z_pos r 1
  have hz2 : 0 < (z r 2 : ℝ) := by exact_mod_cast z_pos r 2
  have he : (r : ℝ) = (A r : ℝ)^3*((z r 1 : ℝ)/(z r 2 : ℝ)) := by
    rw [A_cube r hr]
    field_simp
  rw [he,Real.mul_rpow (pow_nonneg hA.le _) (div_nonneg hz1.le hz2.le),
    ← Real.rpow_natCast_mul hA.le]
  norm_num
  unfold u
  field_simp

/-- A literal scale comparison gives the required progression-width
bound. The natural condition g ≤ a³ applies to the ceiling-third local
residue modulus. K, D and Q may be any nonnegative real numbers. -/
theorem progression_width_le (r g a : ℕ) (Q D K : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hga : g ≤ a^3) (hsize : Q ≤ K^3*(g : ℝ)*D*(r : ℝ)) :
    1+Q^((1 : ℝ)/3)/((a : ℝ)*(A r : ℝ)) ≤
      1+K*D^((1 : ℝ)/3)*u r := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hA0 : 0 < (A r : ℝ) := by exact_mod_cast A_pos r
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hgaR : (g : ℝ) ≤ (a : ℝ)^3 := by exact_mod_cast hga
  have hsize' : Q ≤ K^3*(a : ℝ)^3*D*(r : ℝ) := by
    apply hsize.trans
    gcongr
  have hroot := Real.rpow_le_rpow hQ hsize' (by norm_num : (0 : ℝ) ≤ 1/3)
  have he : (K^3*(a : ℝ)^3*D*(r : ℝ))^((1 : ℝ)/3) =
      K*(a : ℝ)*D^((1 : ℝ)/3)*(r : ℝ)^((1 : ℝ)/3) := by
    rw [Real.mul_rpow (by positivity) hr0.le,
      Real.mul_rpow (by positivity) hD,
      Real.mul_rpow (pow_nonneg hK _) (pow_nonneg ha0.le _),
      ← Real.rpow_natCast_mul hK,← Real.rpow_natCast_mul ha0.le]
    norm_num
  rw [he] at hroot
  calc
    _ ≤ 1+(K*(a : ℝ)*D^((1 : ℝ)/3)*(r : ℝ)^((1 : ℝ)/3))/
        ((a : ℝ)*(A r : ℝ)) :=
      add_le_add (le_refl 1) (div_le_div_of_nonneg_right hroot (mul_pos ha0 hA0).le)
    _ = 1+K*D^((1 : ℝ)/3)*((r : ℝ)^((1 : ℝ)/3)/(A r : ℝ)) := by
      field_simp
      <;> ring
    _ = _ := by rw [cube_root_div_A r hr]

/-- A factor-eight dyadic upper bound contributes only the explicit
factor two in the progression-width estimate. -/
theorem progression_width_le_two (r g a : ℕ) (Q D : ℝ)
    (hr : 0 < r) (ha : 0 < a) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hga : g ≤ a^3) (hsize : Q ≤ 8*(g : ℝ)*D*(r : ℝ)) :
    1+Q^((1 : ℝ)/3)/((a : ℝ)*(A r : ℝ)) ≤
      1+2*D^((1 : ℝ)/3)*u r := by
  apply progression_width_le r g a Q D 2 hr ha hQ hD (by norm_num) hga
  norm_num
  exact hsize

end CubicTenVariables.PlanAlphaParameterRatios
