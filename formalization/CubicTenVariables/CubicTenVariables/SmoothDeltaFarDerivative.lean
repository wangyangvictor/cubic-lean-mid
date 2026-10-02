import CubicTenVariables.SmoothDeltaNormalization
import CubicTenVariables.SmoothDeltaAmplitudeDerivatives

/-! Uniform far-window derivative estimates for the concrete delta amplitude.
The zeroth order retains the cancellation between the two equal profile means. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaFarDerivative
open MeasureTheory Set Finset SmoothDeltaCutoffs SmoothDeltaKernel
  SmoothDeltaNormalization ReciprocalSmoothProfile SmoothDeltaAmplitudeDerivatives
open scoped BigOperators ContDiff SchwartzMap Topology

/-- Real smooth compact profiles satisfy the same quantitative Riemann rule. -/
theorem exists_riemann_error_real (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      |a * (∑' k : ℤ, f (a*(k : ℝ))) - ∫ x : ℝ, f x| ≤ C * a^N := by
  let fc : ℝ → ℂ := fun x => (f x : ℂ)
  have hcc : HasCompactSupport fc := hc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hfc : ContDiff ℝ ∞ fc := Complex.ofRealCLM.contDiff.comp hf
  let F : 𝓢(ℝ,ℂ) := hcc.toSchwartzMap hfc
  obtain ⟨C,hC,hb⟩ := exists_riemann_error F N
  refine ⟨C,hC,?_⟩
  intro a ha ha1
  have hh := hb a ha ha1
  change ‖(a : ℂ) * (∑' k : ℤ, (f (a*(k : ℝ)) : ℂ)) -
    ∫ x : ℝ, (f x : ℂ)‖ ≤ C*a^N at hh
  rw [← Complex.ofReal_tsum,integral_complex_ofReal,← Complex.ofReal_mul,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

/-- The first, non-reciprocal profile in the zeroth-order cancellation. -/
def firstProfile (v : ℝ) : ℝ := omega v / v

theorem firstProfile_contDiff : ContDiff ℝ ∞ firstProfile := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ)<1/4)] with x hx
    have hz : omega x=0 := by
      apply Function.notMem_support.mp
      rw [omega_support]
      exact fun h => (not_lt_of_ge (le_of_lt hx)) h.1
    simp [firstProfile,hz]
  · exact omega_contDiff.contDiffAt.div contDiffAt_id hv

theorem firstProfile_hasCompactSupport : HasCompactSupport firstProfile := by
  simpa only [firstProfile,div_eq_mul_inv] using
    (omega_hasCompactSupport.mul_right (f' := fun x : ℝ => x⁻¹))

theorem firstProfile_integrable : Integrable firstProfile :=
  firstProfile_contDiff.continuous.integrable_of_hasCompactSupport firstProfile_hasCompactSupport

/-- The first finite sum is literally a whole-lattice sample of one fixed
smooth compact profile; terms outside `1,…,Q` vanish. -/
theorem firstProfile_tsum_eq_finite {Q q : ℕ} (hQ : 0<Q) (hq : 1≤q) :
    (∑' k : ℤ, firstProfile (((q : ℝ)/(Q : ℝ))*(k : ℝ))) =
      ∑ k ∈ Icc 1 Q, (Q : ℝ)/((q : ℝ)*(k : ℝ)) *
        omega (((q : ℝ)*(k : ℝ))/(Q : ℝ)) := by
  classical
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : 0 < (q : ℝ) := zero_lt_one.trans_le hqr
  let S := (Finset.Icc 1 Q).image (fun k : ℕ => (k : ℤ))
  have hz (k : ℤ) (hk : k∉S) : firstProfile (((q : ℝ)/(Q : ℝ))*(k : ℝ))=0 := by
    have hw : omega (((q : ℝ)/(Q : ℝ))*(k : ℝ))=0 := by
      by_contra hw
      have hs : ((q : ℝ)/(Q : ℝ))*(k : ℝ) ∈ Function.support omega := hw
      rw [omega_support] at hs
      have hkpos : (0 : ℝ)<k := (mul_pos_iff.mp (lt_trans (by norm_num) hs.1)).resolve_right
        (by intro h; exact (not_lt_of_ge (div_pos hqp hQr).le) h.1) |>.2
      have hkle : (k : ℝ) ≤ Q := by
        have hh : (q : ℝ)*(k : ℝ)<Q := by
          have ht : ((q : ℝ)*(k : ℝ))/(Q : ℝ)<1 := by
            simpa only [div_mul_eq_mul_div] using hs.2
          simpa only [one_mul] using (div_lt_iff₀ hQr).mp ht
        nlinarith
      have hkpos' : (0 : ℤ)<k := by exact_mod_cast hkpos
      have hkle' : k≤(Q : ℤ) := by exact_mod_cast hkle
      apply hk
      apply mem_image.mpr
      refine ⟨k.toNat,mem_Icc.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg (by omega)⟩ <;> omega
    simp [firstProfile,hw]
  rw [tsum_eq_sum hz,sum_image]
  · apply sum_congr rfl
    intro k hk
    simp only [Int.cast_natCast,firstProfile]
    have hk0 : (k : ℝ)≠0 := by exact_mod_cast (show k≠0 by have := (mem_Icc.mp hk).1; omega)
    field_simp
  · intro a ha b hb he
    change (a : ℤ)=(b : ℤ) at he
    exact_mod_cast he

theorem h_neg (Q q : ℕ) (y : ℝ) : h Q q (-y)=h Q q y := by
  simp only [h,Omega,neg_mul,neg_div,neg_neg]
  congr 1
  funext k
  congr 1
  ring

/-- Reflection preserves every derivative's absolute value. -/
theorem abs_iteratedDeriv_h_neg (Q q j : ℕ) (y : ℝ) :
    |iteratedDeriv j (h Q q) (-y)|=|iteratedDeriv j (h Q q) y| := by
  have he : (fun x => h Q q (-x))=h Q q := funext (h_neg Q q)
  have hh := iteratedDeriv_comp_neg j (h Q q) y
  rw [he] at hh
  have ha := congrArg abs hh
  simpa only [smul_eq_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using ha.symm



private theorem exists_sum_error (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      |(∑' k : ℤ, f (a*(k : ℝ))) - (∫ x : ℝ, f x)/a| ≤ C*a := by
  obtain ⟨C,hC,hb⟩ := exists_riemann_error_real f hf hc 2
  refine ⟨C,hC,?_⟩
  intro a ha ha1
  have hh := hb a ha ha1
  have he : (∑' k : ℤ, f (a*(k : ℝ))) - (∫ x : ℝ, f x)/a =
      (a*(∑' k : ℤ, f (a*(k : ℝ))) - ∫ x : ℝ, f x)/a := by field_simp
  rw [he,abs_div,abs_of_pos ha]
  exact (div_le_iff₀ ha).mpr (by nlinarith)

/-- A uniform bound for the first finite sum, including the near window. -/
theorem exists_first_sum_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q q : ℕ,
    0<Q → 1≤q → q≤Q →
    |∑ k ∈ Icc 1 Q, (Q : ℝ)/((q : ℝ)*(k : ℝ)) *
      omega (((q : ℝ)*(k : ℝ))/(Q : ℝ))| ≤ C/((q : ℝ)/(Q : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := exists_sum_error firstProfile firstProfile_contDiff
    firstProfile_hasCompactSupport
  let M := ∫ x : ℝ, firstProfile x
  refine ⟨C+|M|,(by linarith [abs_nonneg M]),?_⟩
  intro Q q hQ hq hqQ
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hqr : 0 < (q : ℝ) := by exact_mod_cast (show 0<q by omega)
  have hx : 0 < (q : ℝ)/(Q : ℝ) := div_pos hqr hQr
  have hx1 : (q : ℝ)/(Q : ℝ) ≤ 1 := (div_le_one hQr).mpr (by exact_mod_cast hqQ)
  rw [← firstProfile_tsum_eq_finite hQ hq]
  have hh := hb ((q : ℝ)/(Q : ℝ)) hx hx1
  have he : |∑' k : ℤ, firstProfile (((q : ℝ)/(Q : ℝ))*(k : ℝ))| ≤
      C*((q : ℝ)/(Q : ℝ)) + |M|/((q : ℝ)/(Q : ℝ)) := by
    have ht := abs_add_le ((∑' k : ℤ, firstProfile (((q : ℝ)/(Q : ℝ))*(k : ℝ))) -
      M/((q : ℝ)/(Q : ℝ))) (M/((q : ℝ)/(Q : ℝ)))
    rw [sub_add_cancel,abs_div,abs_of_pos hx] at ht
    exact ht.trans (add_le_add hh le_rfl)
  apply he.trans
  apply (le_div_iff₀ hx).mpr
  have hhx : ((q : ℝ)/(Q : ℝ))^2 ≤ 1 := pow_le_one₀ hx.le hx1
  have hhC := mul_le_mul_of_nonneg_left hhx (zero_le_one.trans hC)
  field_simp at *
  nlinarith

private theorem positive_order_bound (j : ℕ) (hj : 1≤j) :
    ∃ C : ℝ, 1≤C ∧ ∀ Q q : ℕ, 0<Q → 1≤q → ∀ y : ℝ,
    0<y → (q : ℝ)/(Q : ℝ)≤y → y≤1/4 →
    |iteratedDeriv j (h Q q) y| ≤ C*((q : ℝ)/(Q : ℝ))/y^(j+2) := by
  obtain ⟨C,hC,hb⟩ := exists_sum_error (profile j) (profile_contDiff j)
    (profile_hasCompactSupport j)
  refine ⟨C,hC,?_⟩
  intro Q q hQ hq y hy hxy hy4
  have hx : 0 < (q : ℝ)/(Q : ℝ) := div_pos (by exact_mod_cast (show 0<q by omega))
    (by exact_mod_cast hQ)
  have ha : 0 < ((q : ℝ)/(Q : ℝ))/y := div_pos hx hy
  have ha1 : ((q : ℝ)/(Q : ℝ))/y ≤ 1 := (div_le_one hy).mpr hxy
  have hh := hb (((q : ℝ)/(Q : ℝ))/y) ha ha1
  rw [integral_profile_eq_zero j hj,zero_div,sub_zero] at hh
  have hh' : |∑' k : ℤ, profile j (((q : ℝ)/(Q : ℝ))*(k : ℝ)/y)| ≤
      C*(((q : ℝ)/(Q : ℝ))/y) := by
    simpa only [div_mul_eq_mul_div] using hh
  rw [iteratedDeriv_h_eq_profile_tsum hQ hq j hj hy hy4,abs_mul,abs_neg,
    abs_pow,abs_inv,abs_of_pos hy]
  calc
    _ ≤ (y⁻¹)^(j+1)*(C*(((q : ℝ)/(Q : ℝ))/y)) :=
      mul_le_mul_of_nonneg_left hh' (by positivity)
    _ = _ := by rw [show j+2=(j+1)+1 by omega,pow_succ,inv_pow]; field_simp [hy.ne']; ring

private theorem zero_order_bound :
    ∃ C : ℝ, 1≤C ∧ ∀ Q q : ℕ, 0<Q → 1≤q → ∀ y : ℝ,
    0<y → (q : ℝ)/(Q : ℝ)≤y → y≤1/4 →
    |h Q q y| ≤ C*((q : ℝ)/(Q : ℝ))/y^2 := by
  obtain ⟨C₀,hC₀,hb₀⟩ := exists_sum_error firstProfile firstProfile_contDiff
    firstProfile_hasCompactSupport
  obtain ⟨C₁,hC₁,hb₁⟩ := exists_sum_error (profile 0) (profile_contDiff 0)
    (profile_hasCompactSupport 0)
  refine ⟨C₀+C₁,(by linarith),?_⟩
  intro Q q hQ hq y hy hxy hy4
  let x := (q : ℝ)/(Q : ℝ)
  have hx : 0<x := div_pos (by exact_mod_cast (show 0<q by omega)) (by exact_mod_cast hQ)
  have hx1 : x≤1 := by dsimp [x]; linarith
  have ha : 0<x/y := div_pos hx hy
  have ha1 : x/y≤1 := (div_le_one hy).mpr hxy
  let M := ∫ v : ℝ, firstProfile v
  let A := ∑' k : ℤ, firstProfile (x*(k : ℝ))
  let B := ∑' k : ℤ, profile 0 (x*(k : ℝ)/y)
  have hA : |A-M/x|≤C₀*x := hb₀ x hx hx1
  have hB : |B-M/(x/y)|≤C₁*(x/y) := by
    have hh := hb₁ (x/y) ha ha1
    rw [integral_profile_zero] at hh
    simpa only [B,M,firstProfile,div_mul_eq_mul_div] using hh
  have hh : h Q q y=A-y⁻¹*B := by
    rw [h_eq_profile_tsum hQ hq hy hy4,← firstProfile_tsum_eq_finite hQ hq]
  have hb : |y⁻¹*B-M/x|≤C₁*x/y^2 := by
    have he : y⁻¹*B-M/x=y⁻¹*(B-M/(x/y)) := by field_simp
    rw [he,abs_mul,abs_inv,abs_of_pos hy]
    calc
      _ ≤ y⁻¹*(C₁*(x/y)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by field_simp
  rw [hh]
  calc
    |A-y⁻¹*B| = |(A-M/x)-(y⁻¹*B-M/x)| := by congr 1; ring
    _ ≤ |A-M/x|+|y⁻¹*B-M/x| := abs_sub _ _
    _ ≤ C₀*x+C₁*x/y^2 := add_le_add hA hb
    _ ≤ (C₀+C₁)*x/y^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
      have hys : y^2≤1 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hys (mul_nonneg (zero_le_one.trans hC₀) hx.le)
      field_simp at *
      nlinarith

/-- All orders, both signs, and one constant before the modulus and location. -/
theorem exists_bound (j : ℕ) : ∃ C : ℝ, 1≤C ∧ ∀ Q q : ℕ,
    0<Q → 1≤q → ∀ y : ℝ, (q : ℝ)/(Q : ℝ)≤|y| → |y|≤1/4 →
    |iteratedDeriv j (h Q q) y| ≤ C*((q : ℝ)/(Q : ℝ))/|y|^(j+2) := by
  have hpos : ∃ C : ℝ, 1≤C ∧ ∀ Q q : ℕ, 0<Q → 1≤q → ∀ y : ℝ,
      0<y → (q : ℝ)/(Q : ℝ)≤y → y≤1/4 →
      |iteratedDeriv j (h Q q) y| ≤ C*((q : ℝ)/(Q : ℝ))/y^(j+2) := by
    by_cases hj : j=0
    · subst j
      simpa only [iteratedDeriv_zero,zero_add] using zero_order_bound
    · exact positive_order_bound j (by omega)
  obtain ⟨C,hC,hb⟩ := hpos
  refine ⟨C,hC,?_⟩
  intro Q q hQ hq y hxy hy4
  have hx : 0 < (q : ℝ)/(Q : ℝ) := div_pos (by exact_mod_cast (show 0<q by omega))
    (by exact_mod_cast hQ)
  have hy : 0 < |y| := hx.trans_le hxy
  have hh := hb Q q hQ hq |y| hy hxy hy4
  by_cases hy0 : 0≤y
  · simpa only [abs_of_nonneg hy0] using hh
  · simpa only [abs_of_neg (lt_of_not_ge hy0),abs_iteratedDeriv_h_neg] using hh

theorem exists_rpow_bound (j : ℕ) : ∃ C : ℝ, 1≤C ∧ ∀ Q q : ℕ,
    0<Q → 1≤q → ∀ y : ℝ, (q : ℝ)/(Q : ℝ)≤|y| → |y|≤1/4 →
    |iteratedDeriv j (h Q q) y| ≤
      C*((q : ℝ)/(Q : ℝ))*|y|^(-((j+2 : ℕ) : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound j
  refine ⟨C,hC,?_⟩
  intro Q q hQ hq y hxy hy4
  simpa only [Real.rpow_neg (abs_nonneg y),Real.rpow_natCast,div_eq_mul_inv] using
    hb Q q hQ hq y hxy hy4

end CubicTenVariables.SmoothDeltaFarDerivative
