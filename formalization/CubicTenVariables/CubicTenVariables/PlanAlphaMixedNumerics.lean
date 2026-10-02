import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! Exact real monomial identities and comparisons from Plan Alpha §4.2.
The first identity assumes Q = G*D*C exactly. These are numerical lemmas
only: no claim about dyadic comparability constants or arithmetic sums is made. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaMixedNumerics
open scoped BigOperators

/-- The actual finite outer Hölder sum from §4.2. All three functions
need only be nonnegative on E, and zero masses and empty sets are allowed. -/
theorem outer_holder {ι : Type*} (E : Finset ι) (T P W : ι → ℝ)
    (hT : ∀ r ∈ E, 0 ≤ T r) (hP : ∀ r ∈ E, 0 ≤ P r) (hW : ∀ r ∈ E, 0 ≤ W r) :
    (∑ r ∈ E, (T r)^((20 : ℝ)/3)*(P r)^((2 : ℝ)/3)*(W r)^((1 : ℝ)/3)) ≤
      (∑ r ∈ E, (T r)^10*P r)^((2 : ℝ)/3)*(∑ r ∈ E, W r)^((1 : ℝ)/3) := by
  have hconj : Real.HolderConjugate ((3 : ℝ)/2) 3 := ⟨by norm_num,by norm_num,by norm_num⟩
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg E
    (f := fun r => ((T r)^10*P r)^((2 : ℝ)/3)) (g := fun r => (W r)^((1 : ℝ)/3))
    hconj (fun r hr => Real.rpow_nonneg (mul_nonneg (pow_nonneg (hT r hr) _) (hP r hr)) _)
    (fun r hr => Real.rpow_nonneg (hW r hr) _)
  have hleft : (∑ r ∈ E, ((T r)^10*P r)^((2 : ℝ)/3)*(W r)^((1 : ℝ)/3)) =
      ∑ r ∈ E, (T r)^((20 : ℝ)/3)*(P r)^((2 : ℝ)/3)*(W r)^((1 : ℝ)/3) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Real.mul_rpow (pow_nonneg (hT r hr) _) (hP r hr),← Real.rpow_natCast_mul (hT r hr)]
    norm_num
  have hfirst : (∑ r ∈ E, (((T r)^10*P r)^((2 : ℝ)/3))^((3 : ℝ)/2)) =
      ∑ r ∈ E, (T r)^10*P r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Real.rpow_mul (mul_nonneg (pow_nonneg (hT r hr) _) (hP r hr))]
    norm_num
  have hsecond : (∑ r ∈ E, ((W r)^((1 : ℝ)/3))^(3 : ℝ)) = ∑ r ∈ E, W r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Real.rpow_mul (hW r hr)]
    norm_num
  rw [hleft,hfirst,hsecond] at hh
  norm_num at hh
  exact hh

/-- The exact monomial furnished by the two mixed-modulus mass estimates
and Hölder, retaining both negative powers before the final comparison. -/
theorem holder_identity (Q G D C : ℝ) (hG : 1 ≤ G) (hD : 1 ≤ D)
    (hC : 1 ≤ C) (hQ : Q = G*D*C) :
    D^((13 : ℝ)/2)*
      (G^((28 : ℝ)/3)*C^((121 : ℝ)/12)*D^((10 : ℝ)/3))^((2 : ℝ)/3)*
      (G^7*C^((32 : ℝ)/5)*Q^((10 : ℝ)/3))^((1 : ℝ)/3) =
      Q^((10 : ℝ)-1/30)*G^(-(3 : ℝ)/10)*D^(-(2 : ℝ)/15) := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  subst Q
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (discharger := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow]
  ring

/-- With all three factors at least one, the Hölder monomial is bounded
by the common 1/96-saving power. No error term or comparison constant is hidden. -/
theorem holder_le (Q G D C : ℝ) (hG : 1 ≤ G) (hD : 1 ≤ D)
    (hC : 1 ≤ C) (hQ : Q = G*D*C) :
    D^((13 : ℝ)/2)*
      (G^((28 : ℝ)/3)*C^((121 : ℝ)/12)*D^((10 : ℝ)/3))^((2 : ℝ)/3)*
      (G^7*C^((32 : ℝ)/5)*Q^((10 : ℝ)/3))^((1 : ℝ)/3) ≤
      Q^((10 : ℝ)-1/96) := by
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hG hD) hC
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1
  have hGp := Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num : -(3 : ℝ)/10 ≤ 0)
  have hDp := Real.rpow_le_one_of_one_le_of_nonpos hD (by norm_num : -(2 : ℝ)/15 ≤ 0)
  rw [holder_identity Q G D C hG hD hC hQ]
  calc
    _ ≤ Q^((10 : ℝ)-1/30)*1*1 := mul_le_mul
      (mul_le_mul_of_nonneg_left hGp (Real.rpow_nonneg hQ0 _)) hDp
      (Real.rpow_nonneg (zero_le_one.trans hD) _) (by positivity)
    _ = Q^((10 : ℝ)-1/30) := by ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)

/-- The original 15/16,1/16 interpolation cancels the D exponent exactly.
This identity does not need a factorisation of Q. -/
theorem complement_interpolation_identity (Q G D : ℝ)
    (hQ : 1 ≤ Q) (hG : 1 ≤ G) (hD : 1 ≤ D) :
    (Q^10*G^(-(2 : ℝ)/3)*D^(-(1 : ℝ)/6))^((15 : ℝ)/16)*
      (Q^((10 : ℝ)-1/6)*G^((1 : ℝ)/2)*D^((5 : ℝ)/2))^((1 : ℝ)/16) =
      Q^((10 : ℝ)-1/96)*G^(-(19 : ℝ)/32) := by
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
  simp (discharger := positivity) only [Real.log_mul,Real.log_rpow,Real.log_pow]
  ring

/-- The interpolated complementary monomial has the same 1/96 saving. -/
theorem complement_interpolation_le (Q G D : ℝ)
    (hQ : 1 ≤ Q) (hG : 1 ≤ G) (hD : 1 ≤ D) :
    (Q^10*G^(-(2 : ℝ)/3)*D^(-(1 : ℝ)/6))^((15 : ℝ)/16)*
      (Q^((10 : ℝ)-1/6)*G^((1 : ℝ)/2)*D^((5 : ℝ)/2))^((1 : ℝ)/16) ≤
      Q^((10 : ℝ)-1/96) := by
  rw [complement_interpolation_identity Q G D hQ hG hD]
  calc
    _ ≤ Q^((10 : ℝ)-1/96)*1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))
      (Real.rpow_nonneg (zero_le_one.trans hQ) _)
    _ = _ := mul_one _

end CubicTenVariables.PlanAlphaMixedNumerics
