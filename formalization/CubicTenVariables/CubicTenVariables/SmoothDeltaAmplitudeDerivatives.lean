import CubicTenVariables.SmoothDeltaKernel
import CubicTenVariables.ReciprocalSmoothProfile

/-! Finite derivative identities for the actual smooth delta amplitude.
The integer profile sums are proved to have finite support. No derivative of
an infinite series and no uniform derivative bound is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaAmplitudeDerivatives
open Finset SmoothDeltaCutoffs SmoothDeltaKernel ReciprocalSmoothProfile
open scoped BigOperators ContDiff Topology

private theorem iteratedDeriv_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (j : ℕ) (hf : ∀ i ∈ s, ContDiff ℝ j (f i)) (y : ℝ) :
    iteratedDeriv j (fun z => ∑ i ∈ s, f i z) y = ∑ i ∈ s, iteratedDeriv j (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iteratedDeriv_const]
  | @insert a s ha ih =>
      simp only [mem_insert,forall_eq_or_imp] at hf
      simp only [sum_insert ha]
      rw [show (fun z => f a z + ∑ i ∈ s, f i z) = f a + (fun z => ∑ i ∈ s, f i z) by rfl,
        iteratedDeriv_add hf.1.contDiffAt (ContDiff.sum hf.2).contDiffAt,ih hf.2]

/-- Derivatives of positive order kill the constant first part of each
summand, leaving a literal finite chain-rule expression. -/
theorem iteratedDeriv_h (Q q j : ℕ) (hj : 1 ≤ j) (y : ℝ) :
    iteratedDeriv j (h Q q) y =
      -(∑ k ∈ Icc 1 Q, ((Q : ℝ)/((q : ℝ)*(k : ℝ)))^(j+1) *
        iteratedDeriv j Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ)))) := by
  have hform : h Q q = fun z => ∑ k ∈ Icc 1 Q,
      ((Q : ℝ)/((q : ℝ)*(k : ℝ))) *
        (omega (((q : ℝ)*(k : ℝ))/(Q : ℝ)) -
          Omega (((Q : ℝ)/((q : ℝ)*(k : ℝ)))*z)) := by
    funext z
    unfold h
    apply sum_congr rfl
    intro k hk
    congr 2
    congr 1
    ring
  rw [hform,iteratedDeriv_finset_sum]
  · rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    let a : ℝ := (Q : ℝ)/((q : ℝ)*(k : ℝ))
    have hc : ContDiff ℝ j (fun z =>
        omega (((q : ℝ)*(k : ℝ))/(Q : ℝ))-Omega (a*z)) :=
      contDiff_const.sub ((Omega_contDiff.of_le (by exact_mod_cast le_top)).comp
        (contDiff_const.mul contDiff_id))
    rw [iteratedDeriv_const_mul hc.contDiffAt,
      iteratedDeriv_const_sub (show 0 < j by omega),iteratedDeriv_neg,
      iteratedDeriv_comp_const_mul (Omega_contDiff.of_le (by exact_mod_cast le_top))]
    have he : a*y = y*(Q : ℝ)/((q : ℝ)*(k : ℝ)) := by dsimp [a]; ring
    change a * -(a^j * iteratedDeriv j Omega (a*y)) = _
    rw [he]
    change a * -(a^j * _) = -(a^(j+1) * _)
    rw [pow_succ]
    ring
  · intro k hk
    exact contDiff_const.mul (contDiff_const.sub
      ((Omega_contDiff.of_le (by exact_mod_cast le_top)).comp
        (contDiff_const.mul contDiff_id)))

/-- On the positive half-line the even extension and the original positive
bump have exactly the same derivatives, including order zero. -/
theorem iteratedDeriv_Omega_of_pos (j : ℕ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv j Omega y = iteratedDeriv j omega y := by
  have he : Set.EqOn Omega omega (Set.Ioi (0 : ℝ)) := by
    intro z hz
    have hzero := omega_deriv_eq_zero 0 (v := -z) (by
      intro hmem
      have := hmem.1
      have hz0 : 0 < z := hz
      linarith)
    simp only [iteratedDeriv_zero] at hzero
    simp only [Omega,hzero,add_zero]
  exact he.iteratedDeriv_of_isOpen isOpen_Ioi j hy

private theorem scaled_profile (Q q k j : ℕ) (hQ : 0 < Q) (hq : 0 < q)
    (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    ((Q : ℝ)/((q : ℝ)*(k : ℝ)))^(j+1) *
      iteratedDeriv j Omega (y*(Q : ℝ)/((q : ℝ)*(k : ℝ))) =
        (y⁻¹)^(j+1) * profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y) := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hp : 0 < y*(Q : ℝ)/((q : ℝ)*(k : ℝ)) := by positivity
  rw [iteratedDeriv_Omega_of_pos j hp]
  have he : (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y)⁻¹ =
      y*(Q : ℝ)/((q : ℝ)*(k : ℝ)) := by field_simp
  unfold profile
  rw [he,← mul_assoc,← mul_pow]
  congr 2
  field_simp

/-- All nonzero terms of the integer reciprocal-profile sum occur among
`k=1,...,Q` in the small positive amplitude window. -/
theorem profile_tsum_eq_finite {Q q : ℕ} (hQ : 0 < Q) (hq : 1 ≤ q)
    (j : ℕ) {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1/4) :
    (∑' k : ℤ, profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y)) =
      ∑ k ∈ Icc 1 Q, profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y) := by
  classical
  let s : Finset ℤ := (Icc 1 Q).image (fun k : ℕ => (k : ℤ))
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqR : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hx : 0 < (q : ℝ)/(Q : ℝ) := div_pos (lt_of_lt_of_le zero_lt_one hqR) hQR
  have hz (k : ℤ) (hk : k ∉ s) :
      profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y) = 0 := by
    apply profile_eq_zero
    by_cases hk0 : k ≤ 0
    · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
      have hv : ((q : ℝ)/(Q : ℝ))*(k : ℝ)/y ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hx.le hkR) hy.le
      intro hi
      linarith [hi.1]
    · have hk1 : 1 ≤ k := by omega
      have hkQ : (Q : ℤ) < k := by
        by_contra hh
        apply hk
        refine mem_image.mpr ⟨k.toNat,mem_Icc.mpr ⟨?_,?_⟩,?_⟩
        · omega
        · omega
        · exact Int.toNat_of_nonneg (by omega)
      have hkR : (Q : ℝ) < (k : ℝ) := by exact_mod_cast hkQ
      have hkp : 0 < (k : ℝ) := hQR.trans hkR
      have hmult : (Q : ℝ) < (q : ℝ)*(k : ℝ) := by nlinarith
      have hbig : 1 < ((q : ℝ)/(Q : ℝ))*(k : ℝ) := by
        rw [div_mul_eq_mul_div]
        exact (lt_div_iff₀ hQR).mpr (by simpa using hmult)
      have hfour : 4 < ((q : ℝ)/(Q : ℝ))*(k : ℝ)/y :=
        (lt_div_iff₀ hy).mpr (by linarith)
      intro hi
      linarith [hi.2]
  rw [tsum_eq_sum hz]
  dsimp [s]
  rw [sum_image]
  · simp only [Int.cast_natCast]
  · intro a ha b hb hab
    exact Int.natCast_inj.mp hab

/-- The actual derivative is a scaled sum of the fixed reciprocal profile.
The scale is `q/Q`, and the integer sum is finite by the preceding theorem. -/
theorem iteratedDeriv_h_eq_profile_tsum {Q q : ℕ} (hQ : 0 < Q) (hq : 1 ≤ q)
    (j : ℕ) (hj : 1 ≤ j) {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1/4) :
    iteratedDeriv j (h Q q) y = -(y⁻¹)^(j+1) *
      ∑' k : ℤ, profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y) := by
  rw [iteratedDeriv_h Q q j hj y,profile_tsum_eq_finite hQ hq j hy hy4,neg_mul,
    mul_sum]
  congr 1
  apply sum_congr rfl
  intro k hk
  exact scaled_profile Q q k j hQ (by omega) (mem_Icc.mp hk).1 hy

/-- Order zero retains the first finite sum rather than dropping its constant
contribution. This is the exact original amplitude on the positive window. -/
theorem h_eq_profile_tsum {Q q : ℕ} (hQ : 0 < Q) (hq : 1 ≤ q)
    {y : ℝ} (hy : 0 < y) (hy4 : y ≤ 1/4) :
    h Q q y = (∑ k ∈ Icc 1 Q, (Q : ℝ)/((q : ℝ)*(k : ℝ)) *
        omega (((q : ℝ)*(k : ℝ))/(Q : ℝ))) -
      y⁻¹ * ∑' k : ℤ, profile 0 (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y) := by
  rw [profile_tsum_eq_finite hQ hq 0 hy hy4,mul_sum,← sum_sub_distrib]
  unfold h
  apply sum_congr rfl
  intro k hk
  have he := scaled_profile Q q k 0 hQ (by omega) (mem_Icc.mp hk).1 hy
  simp only [zero_add,pow_one,iteratedDeriv_zero] at he
  rw [← he]
  ring

end CubicTenVariables.SmoothDeltaAmplitudeDerivatives
