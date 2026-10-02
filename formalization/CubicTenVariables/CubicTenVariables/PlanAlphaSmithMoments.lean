import CubicTenVariables.CubefullSmithWeightAverage

/-! The two actual Smith-weight moments used by the mixed-modulus mass
estimates. These bounds hold on arbitrary eligible cube-full subfamilies. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaSmithMoments
open CubeFullSmithParameters CubefullSmithWeightLocal
open scoped BigOperators

/-- The complementary term requires only the zero, first and ninth
moments; its entire shape has no power loss beyond epsilon. -/
theorem exists_complement_shape_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      (∑ r ∈ Q, omega r*(1+u r+(u r)^9)) ≤ K*X^ε := by
  obtain ⟨C₀,hC₀,h₀⟩ := CubefullSmithWeightAverage.exists_dyadic_bound
    0 ε (by norm_num) (by norm_num) hε
  obtain ⟨C₁,hC₁,h₁⟩ := CubefullSmithWeightAverage.exists_dyadic_bound
    1 ε (by norm_num) (by norm_num) hε
  obtain ⟨C₉,hC₉,h₉⟩ := CubefullSmithWeightAverage.exists_dyadic_bound
    9 ε (by norm_num) (by norm_num) hε
  refine ⟨C₀+C₁+C₉,by linarith,?_⟩
  intro X hX Q hQ
  have h0 := h₀ X hX Q hQ
  have h1 := h₁ X hX Q hQ
  have h9 := h₉ X hX Q hQ
  norm_num [weight,threshold,Real.rpow_natCast] at h0 h1 h9
  calc
    _ = (∑ r ∈ Q, omega r)+(∑ r ∈ Q, omega r*u r)+
        (∑ r ∈ Q, omega r*(u r)^9) := by
      simp only [mul_add,mul_one,Finset.sum_add_distrib]
    _ ≤ C₀*X^ε+C₁*X^ε+C₉*X^ε := add_le_add (add_le_add h0 h1) h9
    _ = _ := by ring

/-- The tenth moment pays exactly the existing one-twelfth loss. The
constant is independent of the extra scale t and the cube-full subfamily. -/
theorem exists_tenth_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ t : ℝ, 1 ≤ t →
      (∑ r ∈ Q, omega r*(1+t*u r)^10) ≤ K*X^((1 : ℝ)/12+ε)*t^10 := by
  obtain ⟨C₀,hC₀,h₀⟩ := CubefullSmithWeightAverage.exists_dyadic_bound
    0 ε (by norm_num) (by norm_num) hε
  obtain ⟨C₁₀,hC₁₀,h₁₀⟩ := CubefullSmithWeightAverage.exists_dyadic_bound
    10 ε (by norm_num) (by norm_num) hε
  refine ⟨512*(C₀+C₁₀),by nlinarith,?_⟩
  intro X hX Q hQ t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have h0 := h₀ X hX Q hQ
  have h10 := h₁₀ X hX Q hQ
  norm_num [weight,threshold,Real.rpow_natCast] at h0 h10
  have hx : X^ε ≤ X^((1 : ℝ)/12+ε) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have h0' := h0.trans (mul_le_mul_of_nonneg_left hx (zero_le_one.trans hC₀))
  have hpoint (r : ℕ) :
      omega r*(1+t*u r)^10 ≤ 512*t^10*(omega r+omega r*(u r)^10) := by
    have hu : 0 ≤ u r := by unfold u; positivity
    have hw : 0 ≤ omega r := by unfold omega; positivity
    have hp : (1+t*u r)^10 ≤ t^10*(1+u r)^10 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have ha := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hu 10
    norm_num at ha
    calc
      _ ≤ omega r*(t^10*(1+u r)^10) := mul_le_mul_of_nonneg_left hp hw
      _ ≤ omega r*(t^10*(512*(1+(u r)^10))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ha (pow_nonneg ht0 _)) hw
      _ = _ := by ring
  calc
    _ ≤ ∑ r ∈ Q, 512*t^10*(omega r+omega r*(u r)^10) :=
      Finset.sum_le_sum fun r _ => hpoint r
    _ = 512*t^10*((∑ r ∈ Q, omega r)+(∑ r ∈ Q, omega r*(u r)^10)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ 512*t^10*(C₀*X^((1 : ℝ)/12+ε)+C₁₀*X^((1 : ℝ)/12+ε)) :=
      mul_le_mul_of_nonneg_left (add_le_add h0' h10) (by positivity)
    _ = _ := by ring

end CubicTenVariables.PlanAlphaSmithMoments
