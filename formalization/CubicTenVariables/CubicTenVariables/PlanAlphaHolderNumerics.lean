import CubicTenVariables.ConductorMomentHolder

/-! The numerical Hölder step in Plan Alpha. Zero masses are included;
no division by a weight sum is used. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaHolderNumerics
open scoped BigOperators

theorem factor (X T P W : ℝ) (hX : 0 ≤ X) (hT : 0 ≤ T)
    (hP : 0 ≤ P) (hW : 0 ≤ W) :
    (X*T^10*P)^((2 : ℝ)/3)*(X*W)^((1 : ℝ)/3) =
      X*T^((20 : ℝ)/3)*P^((2 : ℝ)/3)*W^((1 : ℝ)/3) := by
  have hx : X^((2 : ℝ)/3)*X^((1 : ℝ)/3)=X := by
    rw [← Real.rpow_add_of_nonneg hX (by norm_num) (by norm_num)]
    norm_num
  have ht : (T^10)^((2 : ℝ)/3)=T^((20 : ℝ)/3) := by
    rw [← Real.rpow_natCast_mul hT]
    norm_num
  rw [Real.mul_rpow (mul_nonneg hX (pow_nonneg hT _)) hP,
    Real.mul_rpow hX (pow_nonneg hT _), Real.mul_rpow hX hW,ht]
  calc
    _ = (X^((2 : ℝ)/3)*X^((1 : ℝ)/3))*T^((20 : ℝ)/3)*
        P^((2 : ℝ)/3)*W^((1 : ℝ)/3) := by ring
    _ = _ := by rw [hx]

/-- Positive and inverse moment bounds with one common coefficient imply
the literal weighted Hölder term in Proposition1.1. -/
theorem sum_le {ι : Type*} (E : Finset ι) (a k : ι → ℝ)
    (ha : ∀ i ∈ E, 0 ≤ a i) (hk : ∀ i ∈ E, 1 ≤ k i)
    (X T P W : ℝ) (hX : 0 ≤ X) (hT : 0 ≤ T) (hP : 0 ≤ P) (hW : 0 ≤ W)
    (hpos : (∑ i ∈ E, a i*(k i)^((1 : ℝ)/2)) ≤ X*T^10*P)
    (hinv : (∑ i ∈ E, a i/k i) ≤ X*W) :
    (∑ i ∈ E, a i) ≤ X*T^((20 : ℝ)/3)*P^((2 : ℝ)/3)*W^((1 : ℝ)/3) := by
  have hp0 : 0 ≤ ∑ i ∈ E, a i*(k i)^((1 : ℝ)/2) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (Real.rpow_nonneg (by linarith [hk i hi]) _)
  have hi0 : 0 ≤ ∑ i ∈ E, a i/k i :=
    Finset.sum_nonneg fun i hi => div_nonneg (ha i hi) (by linarith [hk i hi])
  calc
    _ ≤ (∑ i ∈ E, a i*(k i)^((1 : ℝ)/2))^((2 : ℝ)/3)*
        (∑ i ∈ E, a i/k i)^((1 : ℝ)/3) :=
      ConductorMomentHolder.sum_le_moments E a k ha hk
    _ ≤ (X*T^10*P)^((2 : ℝ)/3)*(X*W)^((1 : ℝ)/3) :=
      mul_le_mul (Real.rpow_le_rpow hp0 hpos (by norm_num))
        (Real.rpow_le_rpow hi0 hinv (by norm_num)) (Real.rpow_nonneg hi0 _)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := factor X T P W hX hT hP hW

theorem add_le_min_add (z y U C R G : ℝ) (hU : 0 ≤ U)
    (hc : z ≤ U*C) (hr : z ≤ U*R) (hg : y ≤ U*G) :
    z+y ≤ U*(min C R+G) := by
  have hz : z ≤ U*min C R := by
    rw [mul_min_of_nonneg C R hU]
    exact le_min hc hr
  calc
    _ ≤ U*min C R+U*G := add_le_add hz hg
    _ = _ := by ring

end CubicTenVariables.PlanAlphaHolderNumerics
