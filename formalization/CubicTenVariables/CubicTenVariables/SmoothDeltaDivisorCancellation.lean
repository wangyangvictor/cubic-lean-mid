import CubicTenVariables.SmoothDeltaKernel
import CubicTenVariables.FiniteDeltaDivisorIdentity

/-! Exact finite arithmetic cancellation for the concrete smooth delta kernel.
The compact cutoff controls the finite truncation; complementary divisors cancel
all nonzero integer phases. No analytic estimate or literature input is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaDivisorCancellation
open Finset SmoothDeltaCutoffs SmoothDeltaKernel RamanujanDivisorSwitch
open scoped BigOperators

private theorem omega_zero_low {x : ℝ} (hx : x ≤ 1/4) : omega x = 0 := by
  by_contra hn
  have hs : x ∈ Function.support omega := hn
  rw [omega_support] at hs
  exact (not_lt_of_ge hx) hs.1

private theorem omega_zero_high {x : ℝ} (hx : 1 ≤ x) : omega x = 0 := by
  by_contra hn
  have hs : x ∈ Function.support omega := hn
  rw [omega_support] at hs
  exact (not_lt_of_ge hx) hs.2

private def weight (Q : ℕ) (m : ℤ) (r : ℕ) : ℝ :=
  omega ((r : ℝ)/(Q : ℝ)) -
    omega ((m.natAbs : ℝ)/((r : ℝ)*(Q : ℝ)))

private theorem weight_zero {Q : ℕ} (hQ : 0 < Q) (m : ℤ)
    (hm : |(m : ℝ)| ≤ (Q : ℝ)^2/4) {r : ℕ} (hr : Q < r) :
    weight Q m r = 0 := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hrR : (Q : ℝ) < r := by exact_mod_cast hr
  have hr0 : 0 < (r : ℝ) := hQR.trans hrR
  have ha : (m.natAbs : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hfirst : 1 ≤ (r : ℝ)/(Q : ℝ) := (le_div_iff₀ hQR).mpr (by linarith)
  have hsecond : (m.natAbs : ℝ)/((r : ℝ)*(Q : ℝ)) ≤ 1/4 := by
    apply (div_le_iff₀ (mul_pos hr0 hQR)).mpr
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_right hrR.le hQR.le]
  simp only [weight,omega_zero_high hfirst,omega_zero_low hsecond,sub_self]

private theorem finite_inner_truncation {Q q : ℕ} (hq : 0 < q)
    (f : ℕ → ℂ) (hf : ∀ r, Q < r → f r = 0) :
    (∑ j ∈ Icc 1 Q, f (q*j)/(q*j : ℕ)) =
      ∑ j ∈ Icc 1 (Q/q), f (q*j)/(q*j : ℕ) := by
  classical
  symm
  apply sum_subset (Icc_subset_Icc le_rfl (Nat.div_le_self Q q))
  intro j hj hnot
  have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
  have hjlarge : Q/q < j := by
    by_contra hh
    exact hnot (mem_Icc.mpr ⟨hj1,le_of_not_gt hh⟩)
  have hprod : Q < q*j := by
    by_contra hh
    have : j ≤ Q/q := (Nat.le_div_iff_mul_le hq).mpr (by
      simpa only [Nat.mul_comm] using (le_of_not_gt hh))
    exact (not_le_of_gt hjlarge) this
  rw [hf _ hprod,zero_div]

private theorem h_eq_weight_sum {Q q : ℕ} (hQ : 0 < Q) (hq : 0 < q) (m : ℤ) :
    (h Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) =
      (Q : ℂ) * ∑ j ∈ Icc 1 Q, (weight Q m (q*j) : ℂ)/(q*j : ℕ) := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  unfold h
  rw [Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
  have he : ((m : ℝ)/(Q : ℝ)^2)*(Q : ℝ)/((q : ℝ)*(j : ℝ)) =
      (m : ℝ)/(((q*j : ℕ) : ℝ)*(Q : ℝ)) := by
    push_cast
    field_simp
  have ha : |(m : ℝ)/(((q*j : ℕ) : ℝ)*(Q : ℝ))| =
      (m.natAbs : ℝ)/(((q*j : ℕ) : ℝ)*(Q : ℝ)) := by
    have hqj : 0 < ((q*j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos hq (mem_Icc.mp hj).1)
    rw [abs_div,abs_of_pos (mul_pos hqj hQR),Nat.cast_natAbs,Int.cast_abs]
  rw [he,Omega_eq_abs,ha]
  unfold weight
  push_cast
  ring

private theorem sum_h_eq_weight_sum {Q : ℕ} (hQ : 0 < Q) (m : ℤ)
    (hm : |(m : ℝ)| ≤ (Q : ℝ)^2/4) :
    (∑ q ∈ Icc 1 Q, ramanujan q m * (h Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ)) =
      (Q : ℂ) * ∑ r ∈ Icc 1 Q,
        if (r : ℤ) ∣ m then (weight Q m r : ℂ) else 0 := by
  classical
  have ht (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (h Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) =
        (Q : ℂ) * ∑ j ∈ Icc 1 (Q/q), (weight Q m (q*j) : ℂ)/(q*j : ℕ) := by
    rw [h_eq_weight_sum hQ (mem_Icc.mp hq).1 m]
    congr 1
    apply finite_inner_truncation (mem_Icc.mp hq).1 (fun r => (weight Q m r : ℂ))
    intro r hr
    rw [weight_zero hQ m hm hr,Complex.ofReal_zero]
  calc
    _ = (Q : ℂ) * ∑ q ∈ Icc 1 Q, ramanujan q m *
        ∑ j ∈ Icc 1 (Q/q), (weight Q m (q*j) : ℂ)/(q*j : ℕ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      rw [ht q hq]
      ring
    _ = _ := by rw [FiniteDeltaDivisorIdentity.weighted_switch Q m
      (fun r => (weight Q m r : ℂ))]

private theorem weight_divisor_sum_zero (Q : ℕ) (m : ℤ) :
    (∑ r ∈ m.natAbs.divisors, (weight Q m r : ℂ)) = 0 := by
  have he := FiniteDeltaDivisorIdentity.complementary_divisors_natAbs m (Q : ℝ)
    (fun x => (omega x : ℂ))
  simpa only [weight,Complex.ofReal_sub,sum_sub_distrib,sub_eq_zero] using he

private theorem sum_weight_zero {Q : ℕ} (hQ : 0 < Q) (m : ℤ) (hm0 : m ≠ 0)
    (hm : |(m : ℝ)| ≤ (Q : ℝ)^2/4) :
    (∑ r ∈ Icc 1 Q, if (r : ℤ) ∣ m then (weight Q m r : ℂ) else 0) = 0 := by
  classical
  have hmn : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
  rw [← sum_filter]
  have he : (Icc 1 Q).filter (fun r : ℕ => (r : ℤ) ∣ m) =
      m.natAbs.divisors.filter (fun r => r ≤ Q) := by
    ext r
    simp only [mem_filter,mem_Icc,Nat.mem_divisors,Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hr,hRQ⟩,hd⟩
      exact ⟨⟨hd,hmn⟩,hRQ⟩
    · rintro ⟨⟨hd,_⟩,hRQ⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hmn),hRQ⟩,hd⟩
  rw [he,← weight_divisor_sum_zero Q m]
  apply sum_subset (filter_subset _ _)
  intro r hr hnot
  have hQr : Q < r := by
    simpa only [mem_filter,hr,true_and,not_le] using hnot
  rw [weight_zero hQ m hm hQr,Complex.ofReal_zero]

/-- Exact finite cancellation before Fourier inversion, valid for every integer
phase, including zero and negative phases, and for the endpoint `Q=2`. -/
theorem sum_g {Q : ℕ} (hQ : 2 ≤ Q) (m : ℤ) :
    (∑ q ∈ Icc 1 Q, ramanujan q m *
      (g Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ)) =
        if m = 0 then (Q : ℂ)^2/(c Q : ℂ) else 0 := by
  classical
  have hQ0 : 0 < Q := by omega
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ0
  by_cases hm0 : m = 0
  · subst m
    rw [if_pos rfl]
    have hs := sum_h_eq_weight_sum hQ0 0 (by simp; positivity)
    have hw (r : ℕ) : weight Q 0 r = omega ((r : ℝ)/(Q : ℝ)) := by
      simp [weight,omega_zero_low (by norm_num : (0 : ℝ) ≤ 1/4)]
    simp only [Int.cast_zero,zero_div,g,U_zero,one_mul] at hs ⊢
    rw [hs]
    simp only [dvd_zero,ite_true,hw]
    unfold c normalizer
    push_cast
    field_simp
  · rw [if_neg hm0]
    by_cases hu : U ((m : ℝ)/(Q : ℝ)^2) = 0
    · simp [g,hu]
    · have hs : (m : ℝ)/(Q : ℝ)^2 ∈ Function.support U := hu
      rw [U_support] at hs
      have habs : |(m : ℝ)| ≤ (Q : ℝ)^2/4 := by
        have hpow : 0 < (Q : ℝ)^2 := sq_pos_of_pos hQR
        have hlo := (lt_div_iff₀ hpow).mp hs.1
        have hhi := (div_lt_iff₀ hpow).mp hs.2
        rw [abs_le]
        constructor <;> nlinarith
      have hh := sum_h_eq_weight_sum hQ0 m habs
      rw [sum_weight_zero hQ0 m hm0 habs,mul_zero] at hh
      calc
        _ = (U ((m : ℝ)/(Q : ℝ)^2) : ℂ) *
            ∑ q ∈ Icc 1 Q, ramanujan q m * (h Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q hq
          simp only [g,Complex.ofReal_mul]
          ring
        _ = 0 := by rw [hh,mul_zero]

/-- The normalized delta identity with the same coefficient used by the actual
Fourier kernel. -/
theorem normalized_sum_g {Q : ℕ} (hQ : 2 ≤ Q) (m : ℤ) :
    ((c Q : ℂ)/(Q : ℂ)^2) *
      (∑ q ∈ Icc 1 Q, ramanujan q m *
        (g Q q ((m : ℝ)/(Q : ℝ)^2) : ℂ)) = if m = 0 then 1 else 0 := by
  rw [sum_g hQ m]
  have hc : (c Q : ℂ) ≠ 0 := by exact_mod_cast (c_pos hQ).ne'
  have hq : (Q : ℂ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  split_ifs
  · field_simp
  · simp

end CubicTenVariables.SmoothDeltaDivisorCancellation
