import CubicTenVariables.SmoothDeltaKernel
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries

/-! Quantitative normalization of the actual fixed smooth delta cutoff.
The finite Riemann sum is evaluated by one-dimensional Poisson summation;
all estimates are proved from Schwartz decay. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.SmoothDeltaNormalization
open MeasureTheory SmoothDeltaCutoffs SmoothDeltaKernel
open scoped BigOperators FourierTransform SchwartzMap ContDiff

private def dilate (f : 𝓢(ℝ,ℂ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ a ha).toContinuousLinearEquiv f

private theorem dilate_apply (f : 𝓢(ℝ,ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    dilate f a ha x = f (a*x) := rfl

theorem fourier_dilate (f : ℝ → ℂ) (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x => f (a*x)) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ/a) := by
  let J : ℝ → ℂ := fun y => Complex.exp
    ((↑(-2 * Real.pi * inner ℝ y (ξ/a)) : ℂ) * Complex.I) * f y
  have he (x : ℝ) :
      Complex.exp ((↑(-2 * Real.pi * inner ℝ x ξ) : ℂ) * Complex.I) * f (a*x) =
        J (a*x) := by
    unfold J
    congr 2
    change ((↑(-2 * Real.pi * (ξ*x)) : ℂ) * Complex.I) =
      ((↑(-2 * Real.pi * ((ξ/a)*(a*x))) : ℂ) * Complex.I)
    congr 2
    field_simp
  rw [Real.fourier_eq',Real.fourier_eq']
  simp only [smul_eq_mul]
  simp_rw [he]
  rw [Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr ha),Complex.real_smul,
    Complex.ofReal_inv]

theorem scaled_poisson (f : 𝓢(ℝ,ℂ)) (a : ℝ) (ha : 0 < a) :
    (∑' k : ℤ, f (a*(k : ℝ))) =
      (a : ℂ)⁻¹ * ∑' k : ℤ, (𝓕 f) ((k : ℝ)/a) := by
  let F := dilate f a ha.ne'
  have hp := F.tsum_eq_tsum_fourier (0 : ℝ)
  simp only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one] at hp
  have hscale (k : ℤ) : (𝓕 F) (k : ℝ) = (a : ℂ)⁻¹ * (𝓕 f) ((k : ℝ)/a) :=
    fourier_dilate f a ha k
  simp_rw [hscale] at hp
  rw [tsum_mul_left] at hp
  simpa only [F,dilate_apply] using hp

private def weight (k : ℤ) : ℝ := ((k : ℝ)^2)⁻¹

private theorem weight_summable : Summable weight := by
  simpa [weight,one_div] using (Real.summable_one_div_int_pow.mpr (by omega : 1 < 2))

private theorem weight_nonneg (k : ℤ) : 0 ≤ weight k := inv_nonneg.mpr (sq_nonneg _)

/-- All nonzero lattice samples have a summable majorant, uniformly in the
spacing `a≥1`, with any requested polynomial saving. -/
theorem exists_lattice_tail_bound (f : 𝓢(ℝ,ℂ)) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 1 ≤ a →
      Summable (fun k : ℤ => if k=0 then (0 : ℂ) else f ((k : ℝ)*a)) ∧
      ‖∑' k : ℤ, if k=0 then (0 : ℂ) else f ((k : ℝ)*a)‖ ≤ C / a^N := by
  obtain ⟨B,hB,hbound⟩ := f.decay (N+2) 0
  let W := ∑' k : ℤ, weight k
  have hW : 0 ≤ W := tsum_nonneg weight_nonneg
  refine ⟨max 1 (B*W),le_max_left _ _,?_⟩
  intro a ha
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hterm (k : ℤ) :
      ‖if k=0 then (0 : ℂ) else f ((k : ℝ)*a)‖ ≤ (B/a^N)*weight k := by
    by_cases hk : k=0
    · simp [hk,weight]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : 1 ≤ |(k : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |k| from Int.one_le_abs hk)
    have hka : 0 < |(k : ℝ)| * a := mul_pos (abs_pos.mpr hk0) ha0
    have hb := hbound ((k : ℝ)*a)
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,abs_mul,abs_of_pos ha0] at hb
    have hc : |(k : ℝ)|^2 * a^N ≤ (|(k : ℝ)| * a)^(N+2) := by
      rw [mul_pow]
      exact mul_le_mul
        (pow_le_pow_right₀ hk1 (by omega))
        (pow_le_pow_right₀ ha (by omega)) (by positivity) (by positivity)
    have hm : (|(k : ℝ)|^2 * a^N) * ‖f ((k : ℝ)*a)‖ ≤ B :=
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans hb
    simp only [if_neg hk,weight]
    rw [← sq_abs]
    have he : (B/a^N) * (|(k : ℝ)|^2)⁻¹ = B / (|(k : ℝ)|^2 * a^N) := by ring
    rw [he]
    exact (le_div_iff₀ (mul_pos (pow_pos (abs_pos.mpr hk0) 2) (pow_pos ha0 N))).mpr
      (by simpa [mul_comm] using hm)
  have hs := weight_summable.mul_left (B/a^N)
  refine ⟨hs.of_norm_bounded hterm,?_⟩
  have hb := tsum_of_norm_bounded hs.hasSum hterm
  rw [tsum_mul_left] at hb
  calc
    _ ≤ (B/a^N)*W := hb
    _ = (B*W)/a^N := by ring
    _ ≤ max 1 (B*W)/a^N := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

theorem fourier_at_zero (f : 𝓢(ℝ,ℂ)) : (𝓕 f) 0 = ∫ x : ℝ, f x := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  simp

/-- Poisson summation and the nonzero Schwartz lattice tail give a rapid
Riemann-sum estimate, uniformly over every real mesh `0<a≤1`. -/
theorem exists_riemann_error (f : 𝓢(ℝ,ℂ)) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 →
      ‖(a : ℂ) * (∑' k : ℤ, f (a*(k : ℝ))) - ∫ x : ℝ, f x‖ ≤ C * a^N := by
  obtain ⟨C,hC,hbound⟩ := exists_lattice_tail_bound (𝓕 f) N
  refine ⟨C,hC,?_⟩
  intro a ha ha1
  have ha' : 1 ≤ a⁻¹ := (one_le_inv₀ ha).mpr ha1
  obtain ⟨hs,ht⟩ := hbound a⁻¹ ha'
  let F : ℤ → ℂ := fun k => (𝓕 f) ((k : ℝ)*a⁻¹)
  have hsf : Summable F := by
    have hz := (hasSum_ite_eq (0 : ℤ) ((𝓕 f) 0)).summable
    convert hz.add hs using 1
    funext k
    by_cases hk : k=0 <;> simp [F,hk]
  have he := hsf.tsum_eq_add_tsum_ite 0
  have hp := scaled_poisson f a ha
  have heq : (a : ℂ) * (∑' k : ℤ, f (a*(k : ℝ))) - ∫ x : ℝ, f x =
      ∑' k : ℤ, if k=0 then (0 : ℂ) else (𝓕 f) ((k : ℝ)*a⁻¹) := by
    rw [hp,mul_inv_cancel_left₀ (by exact_mod_cast ha.ne')]
    simp only [div_eq_mul_inv] at *
    have he' : (∑' k : ℤ, (𝓕 f) ((k : ℝ)*a⁻¹)) =
        (∫ x : ℝ, f x) + ∑' k : ℤ, if k=0 then (0 : ℂ) else (𝓕 f) ((k : ℝ)*a⁻¹) := by
      simpa only [F,Int.cast_zero,zero_mul,fourier_at_zero] using he
    rw [he']
    ring
  rw [heq]
  simpa only [inv_pow,div_inv_eq_mul] using ht

private def omegaComplex (x : ℝ) : ℂ := (omega x : ℂ)

private theorem omegaComplex_compact : HasCompactSupport omegaComplex :=
  omega_hasCompactSupport.comp_left (by simp)

private theorem omegaComplex_smooth : ContDiff ℝ ∞ omegaComplex :=
  Complex.ofRealCLM.contDiff.comp omega_contDiff

private def omegaSchwartz : 𝓢(ℝ,ℂ) :=
  omegaComplex_compact.toSchwartzMap omegaComplex_smooth

private theorem omegaSchwartz_integral : (∫ x : ℝ, omegaSchwartz x) = 1 := by
  change (∫ x : ℝ, (omega x : ℂ)) = 1
  rw [integral_complex_ofReal,omega_integral]
  norm_num

/-- The support makes the two-sided lattice sum exactly the finite positive
grid sum already used to define the normalizer. -/
theorem omega_grid_sum {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑' k : ℤ, (omega ((k : ℝ)/(Q : ℝ)) : ℂ)) =
      ∑ j ∈ Finset.Icc 1 Q, (omega ((j : ℝ)/(Q : ℝ)) : ℂ) := by
  classical
  let S := (Finset.Icc 1 Q).image (fun j : ℕ => (j : ℤ))
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hz (k : ℤ) (hk : k ∉ S) : (omega ((k : ℝ)/(Q : ℝ)) : ℂ) = 0 := by
    have hw : omega ((k : ℝ)/(Q : ℝ)) = 0 := by
      by_contra hw
      have hs : (k : ℝ)/(Q : ℝ) ∈ Function.support omega := hw
      rw [omega_support] at hs
      have hkpos : (0 : ℝ) < k := by
        have hh := (lt_div_iff₀ hQ0).mp hs.1
        nlinarith
      have hkle : (k : ℝ) ≤ Q := le_of_lt (by
        simpa using (div_lt_iff₀ hQ0).mp hs.2)
      have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
      have hkle' : k ≤ (Q : ℤ) := by exact_mod_cast hkle
      have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
      apply hk
      apply Finset.mem_image.mpr
      refine ⟨k.toNat,Finset.mem_Icc.mpr ⟨?_,?_⟩,hcast⟩ <;> omega
    simp [hw]
  rw [tsum_eq_sum hz]
  rw [Finset.sum_image]
  · simp
  · intro a ha b hb he
    change (a : ℤ) = (b : ℤ) at he
    exact_mod_cast he

theorem normalizer_error (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q →
    |normalizer Q - 1| ≤ C / (Q : ℝ)^N := by
  obtain ⟨C,hC,hb⟩ := exists_riemann_error omegaSchwartz N
  refine ⟨C,hC,?_⟩
  intro Q hQ
  have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hh := hb (Q : ℝ)⁻¹ (inv_pos.mpr hQ0) ((inv_le_one₀ hQ0).mpr hQ1)
  have he : (∑' k : ℤ, omegaSchwartz ((Q : ℝ)⁻¹*(k : ℝ))) =
      ∑ j ∈ Finset.Icc 1 Q, (omega ((j : ℝ)/(Q : ℝ)) : ℂ) := by
    change (∑' k : ℤ, (omega ((Q : ℝ)⁻¹*(k : ℝ)) : ℂ)) = _
    simpa only [div_eq_mul_inv,mul_comm] using omega_grid_sum hQ
  rw [he,omegaSchwartz_integral] at hh
  simp only [Complex.ofReal_inv] at hh
  have hn : ((Q : ℝ)⁻¹ : ℂ) * (∑ j ∈ Finset.Icc 1 Q, (omega ((j : ℝ)/(Q : ℝ)) : ℂ)) =
      (normalizer Q : ℂ) := by simp [normalizer]
  rw [hn,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  simpa only [inv_pow,div_eq_mul_inv] using hh

/-- The inverse normalizer is uniformly bounded over every natural `Q≥2`. -/
theorem c_bounded : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q → c Q ≤ C := by
  obtain ⟨B,hB,herror⟩ := normalizer_error 1
  obtain ⟨M,hM⟩ := exists_nat_gt (2*B)
  let C := max 2 (∑ i ∈ Finset.Icc 2 M, c i)
  refine ⟨C,(by dsimp [C]; linarith [le_max_left (2 : ℝ) (∑ i ∈ Finset.Icc 2 M, c i)]),?_⟩
  intro Q hQ
  by_cases hQM : Q ≤ M
  · apply (Finset.single_le_sum (fun i hi => (c_pos (Finset.mem_Icc.mp hi).1).le)
      (Finset.mem_Icc.mpr ⟨hQ,hQM⟩)).trans
    exact le_max_right _ _
  · have hMQ : (M : ℝ) ≤ Q := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hQM))
    have hQ0 : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
    have he := herror Q hQ
    simp only [pow_one] at he
    have hsmall : B/(Q : ℝ) ≤ 1/2 := (div_le_iff₀ hQ0).mpr (by linarith)
    have hn : (1/2 : ℝ) ≤ normalizer Q := by
      have hl := (abs_le.mp (he.trans hsmall)).1
      linarith
    have hc : c Q ≤ 2 := by
      apply (inv_le_iff_one_le_mul₀ (normalizer_pos hQ)).mpr
      linarith
    exact hc.trans (le_max_left _ _)

/-- Strict positivity has one lower constant independent of the integer mesh. -/
theorem normalizer_uniform_pos : ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℕ, 2 ≤ Q → δ ≤ normalizer Q := by
  obtain ⟨C,hC,hb⟩ := c_bounded
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  refine ⟨C⁻¹,inv_pos.mpr hC0,?_⟩
  intro Q hQ
  have hh := (inv_le_iff_one_le_mul₀ (normalizer_pos hQ)).mp (hb Q hQ)
  exact (inv_le_iff_one_le_mul₀ hC0).mpr (by nlinarith)

/-- The actual normalizing constant approaches one faster than every fixed
inverse power, without excluding any natural `Q≥2`. -/
theorem c_error (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ Q : ℕ, 2 ≤ Q →
    |c Q - 1| ≤ C / (Q : ℝ)^N := by
  obtain ⟨B,hB,hb⟩ := c_bounded
  obtain ⟨D,hD,hd⟩ := normalizer_error N
  refine ⟨B*D,one_le_mul_of_one_le_of_one_le hB hD,?_⟩
  intro Q hQ
  have hc0 := (c_pos hQ).le
  have he : c Q - 1 = -(c Q) * (normalizer Q - 1) := by
    unfold c
    field_simp [(normalizer_pos hQ).ne']
    ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg hc0]
  calc
    _ ≤ B * (D/(Q : ℝ)^N) :=
      mul_le_mul (hb Q hQ) (hd Q hQ) (abs_nonneg _) (zero_le_one.trans hB)
    _ = _ := by ring

end CubicTenVariables.SmoothDeltaNormalization
