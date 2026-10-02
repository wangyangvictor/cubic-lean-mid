import CubicTenVariables.OscillatoryLocalizationAsymptotic

/-! Rapid frequency decay follows from the same generic localization input.
The additional decay order absorbs both the physical Jacobian and the
conversion from normalized to physical frequency. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory
open scoped BigOperators Topology ContDiff
variable {n : ℕ}

theorem exists_gradient_bound (f : MvPolynomial (Fin n) ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x : Fin n → ℝ, ‖x‖ ≤ 2 →
      ‖(fun i => eval x (pderiv i f))‖ ≤ B := by
  have hg : Continuous (fun x : Fin n → ℝ => fun i => eval x (pderiv i f)) := by
    apply continuous_pi
    intro i
    exact (pderiv i f).continuous_eval
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro x hx
  exact (hB x (by simpa using hx)).trans (le_max_right _ _)

theorem max_sqrt_sq_le (H t : ℝ) (hH : 1 ≤ H) :
    (max 1 (Real.sqrt (|t| * H)))^2 ≤ H*max 1 |t| := by
  have hH0 : 0 ≤ H := by linarith
  rcases le_total 1 (Real.sqrt (|t| * H)) with h | h
  · rw [max_eq_right h,Real.sq_sqrt (mul_nonneg (abs_nonneg _) hH0)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (le_max_right 1 |t|) hH0
  · rw [max_eq_left h,one_pow]
    exact one_le_mul_of_one_le_of_one_le hH (le_max_left _ _)

/-- An explicit empty-window criterion. Only a compact-box bound for the
literal polynomial gradient occurs; it is proved above by continuity. -/
theorem window_empty_of_frequency (f : MvPolynomial (Fin n) ℝ)
    (B H t : ℝ) (u : Fin n → ℝ) (R : ℝ) (hH : 1 ≤ H)
    (hg : ∀ x : Fin n → ℝ, ‖x‖ ≤ 2 → ‖(fun i => eval x (pderiv i f))‖ ≤ B)
    (hu : 0 < ‖u‖) (huT : max 1 |t| ≤ ‖u‖)
    (huB : 4*B*|t| ≤ ‖u‖) (hRsq : 16*H*R^2=‖u‖) :
    PolynomialOscillatory.window f 1 H t u R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx2 : ‖x‖ ≤ 2 := by have hh := hx.1; norm_num at hh; exact hh
  have hgrad := hg x hx2
  let W : ℝ := max 1 (Real.sqrt (|t| * H))
  have hW : 0 ≤ W := le_trans (by norm_num) (le_max_left _ _)
  have hWsq : W^2 ≤ H*max 1 |t| := max_sqrt_sq_le H t hH
  have hs1 := mul_le_mul_of_nonneg_left hWsq (by positivity : 0 ≤ 16*R^2)
  have hs2 := mul_le_mul_of_nonneg_left huT hu.le
  have hRW : R*W ≤ ‖u‖/4 := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [hRsq]
  have hgT : ‖t • (fun i => eval x (pderiv i f))‖ ≤ |t| * B := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hgrad (abs_nonneg _)
  have hxu : ‖t • (fun i => eval x (pderiv i f))-u‖ ≤ R*W := hx.2
  have htri := norm_le_norm_sub_add u (t • (fun i => eval x (pderiv i f)))
  rw [norm_sub_rev] at htri
  nlinarith

/-- Arbitrarily strong simultaneous decay in a scale P and the normalized
frequency. Constants are fixed before t,u,P. -/
theorem exists_normalized_frequency_bound (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (f : MvPolynomial (Fin n) ℝ)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (A N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ (t : ℝ) (u : Fin n → ℝ),
      K*P^(2*ε)*max 1 |t| ≤ ‖u‖ →
      ‖PolynomialOscillatory.integral f w t u‖ ≤ C*P^(-(A : ℝ))*‖u‖^(-(N : ℝ)) := by
  obtain ⟨B,hB,hg⟩ := exists_gradient_bound f
  obtain ⟨H,hH,h⟩ := lit n hn f w hw hc hwn 1 (by norm_num) hs
  obtain ⟨L,hL,hLA⟩ := exists_decay_order ε hε 0 A
  obtain ⟨C,R₀,hC,hR₀,hb⟩ := h (L+2*N) (by omega)
  let D : ℝ := 16*H
  let K : ℝ := max D (4*B)
  refine ⟨C*D^N,K,max 1 (R₀^ε⁻¹),?_,?_,le_max_left _ _,?_⟩
  · exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by dsimp [D]; linarith))
  · exact le_trans (by dsimp [D]; linarith : (1 : ℝ) ≤ D) (le_max_left _ _)
  intro P hP t u hu
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hD : 0 < D := by dsimp [D]; linarith
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hK1 : 1 ≤ K := le_trans hD1 (le_max_left _ _)
  have hPe : 1 ≤ P^(2*ε) := Real.one_le_rpow hP1 (by positivity)
  have hT : 1 ≤ max 1 |t| := le_max_left _ _
  have hT0 : 0 ≤ max 1 |t| := by positivity
  have hu1 : 1 ≤ ‖u‖ := (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK1 hPe) hT).trans hu
  have hu0 : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu1
  have huT : max 1 |t| ≤ ‖u‖ :=
    (le_mul_of_one_le_left hT0 (one_le_mul_of_one_le_of_one_le hK1 hPe)).trans hu
  have huB : 4*B*|t| ≤ ‖u‖ := by
    calc
      _ ≤ K*|t| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      _ ≤ (K*P^(2*ε))*max 1 |t| := by
        apply mul_le_mul
        · exact le_mul_of_one_le_right (by linarith : 0 ≤ K) hPe
        · exact le_max_right _ _
        · exact abs_nonneg _
        · positivity
      _ ≤ _ := hu
  have huD : D*P^(2*ε) ≤ ‖u‖ := by
    calc
      _ ≤ K*P^(2*ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ (K*P^(2*ε))*max 1 |t| := le_mul_of_one_le_right (by positivity) hT
      _ ≤ _ := hu
  let R : ℝ := Real.sqrt (‖u‖/D)
  have hRpos : 0 < R := Real.sqrt_pos.mpr (div_pos hu0 hD)
  have hRsq : R^2=‖u‖/D := Real.sq_sqrt (div_nonneg hu0.le hD.le)
  have hRD : D*R^2=‖u‖ := by rw [hRsq]; field_simp
  have hPR : P^ε ≤ R := by
    apply le_of_sq_le_sq _ hRpos.le
    rw [hRsq,le_div_iff₀ hD]
    convert huD using 1
    rw [← Real.rpow_two,← Real.rpow_mul hP0.le]
    ring_nf
  have hRcut : R₀ ≤ R := le_trans
    ((Real.rpow_inv_le_iff_of_pos (by linarith : 0 ≤ R₀) hP0.le hε).mp
      ((le_max_right _ _).trans hP)) hPR
  have hempty := window_empty_of_frequency f B H t u R hH hg hu0 huT huB hRD
  have hib := hb t u R hRcut
  rw [hempty,measure_empty,ENNReal.toReal_zero,add_zero] at hib
  have hRL : R^(-(L : ℝ)) ≤ P^(-(A : ℝ)) := by
    calc
      _ ≤ (P^ε)^(-(L : ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) hPR (neg_nonpos.mpr (Nat.cast_nonneg L))
      _ ≤ P^(-(A : ℝ)) := by simpa using scale_decay P ε hP1 0 A L hLA
  have hRN : R^(-((2*N : ℕ) : ℝ)) = D^N*‖u‖^(-(N : ℝ)) := by
    rw [Real.rpow_neg hRpos.le,Real.rpow_natCast,pow_mul]
    rw [hRsq,div_pow,inv_div,Real.rpow_neg hu0.le,Real.rpow_natCast]
    rfl
  calc
    _ ≤ C*R^(-((L+2*N : ℕ) : ℝ)) := hib
    _ = C*(R^(-(L : ℝ))*R^(-((2*N : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hRpos]
      congr 2
      push_cast
      ring
    _ ≤ C*(P^(-(A : ℝ))*(D^N*‖u‖^(-(N : ℝ)))) := by
      rw [hRN]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hRL (by positivity)) (by linarith)
    _ = _ := by ring

/-- Required physical-frequency tail. The same fixed chart weight is used
as in localization. It holds for every θ; in particular it covers the source
range |θ|≤1/(qP). Only q>0 and q≤P² are needed. -/
theorem exists_frequency_bound (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ C K P₀ : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ q : ℝ, 0 < q → q ≤ P^2 →
      ∀ (θ : ℝ) (v : Fin n → ℝ),
      K*P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ (q⁻¹ • v)‖ ≤ C*‖v‖^(-(N : ℝ)) := by
  obtain ⟨C,K,P₀,hC,hK,hP₀,hb⟩ := exists_normalized_frequency_bound lit hn
    (chartPolynomial F x₀ ρ) w hw hc hwn hs ε hε (n+N) N
  refine ⟨max 1 (C*ρ^n*ρ^(-(N : ℝ))),max 1 (K/ρ),P₀,le_max_left _ _,
    le_max_left _ _,hP₀,?_⟩
  intro P hP q hq hqP θ v hv
  have hP1 : 1 ≤ P := hP₀.trans hP
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  let u : Fin n → ℝ := (P*ρ) • (q⁻¹ • v)
  have hunorm : ‖u‖=(P*ρ/q)*‖v‖ := by
    dsimp [u]
    rw [smul_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity)]
    rfl
  have ht : |θ*P^3|=|θ| * P^3 := by rw [abs_mul,abs_of_pos (pow_pos hPpos _)]
  have hcut : K*P^(2*ε)*max 1 |θ*P^3| ≤ ‖u‖ := by
    rw [hunorm,ht]
    have h1 : (K/ρ)*P^(2*ε)*(q/P)*max 1 (|θ| * P^3) ≤ ‖v‖ := by
      apply le_trans _ hv
      gcongr
      exact le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ P*ρ/q)
    convert h2 using 1
    field_simp
  have hnormu : 0 < ‖u‖ := lt_of_lt_of_le (by positivity) hcut
  have hnormv : 0 < ‖v‖ := by
    rw [hunorm] at hnormu
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < P*ρ/q)).mp hnormu
  have hI := hb P hP (θ*P^3) u hcut
  have hcancel : (P*ρ)^n*P^(-((n+N : ℕ) : ℝ)) = ρ^n*P^(-(N : ℝ)) := by
    rw [mul_pow,Real.rpow_neg hPpos.le,Real.rpow_natCast,
      Real.rpow_neg hPpos.le,Real.rpow_natCast,pow_add]
    field_simp
  have hPU : ρ*‖v‖ ≤ P*‖u‖ := by
    rw [hunorm]
    have hcoeff : ρ ≤ P*(P*ρ/q) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hq).mpr
      nlinarith [mul_le_mul_of_nonneg_right hqP hρ.le]
    exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg v) |>.trans_eq (by ring)
  have hdecay : P^(-(N : ℝ))*‖u‖^(-(N : ℝ)) ≤
      ρ^(-(N : ℝ))*‖v‖^(-(N : ℝ)) := by
    rw [← Real.mul_rpow hPpos.le hnormu.le,← Real.mul_rpow hρ.le hnormv.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hρ hnormv) hPU
      (neg_nonpos.mpr (Nat.cast_nonneg N))
  rw [norm_scaledIntegral_chart F hF w x₀ ρ P hρ hPpos θ (q⁻¹ • v)]
  calc
    _ ≤ (P*ρ)^n*(C*P^(-((n+N : ℕ) : ℝ))*‖u‖^(-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (C*ρ^n)*(P^(-(N : ℝ))*‖u‖^(-(N : ℝ))) := by
      calc
        _ = C*((P*ρ)^n*P^(-((n+N : ℕ) : ℝ)))*‖u‖^(-(N : ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring
    _ ≤ (C*ρ^n)*(ρ^(-(N : ℝ))*‖v‖^(-(N : ℝ))) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ ≤ max 1 (C*ρ^n*ρ^(-(N : ℝ)))*‖v‖^(-(N : ℝ)) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (le_max_right 1 (C*ρ^n*ρ^(-(N : ℝ))))
        (Real.rpow_nonneg (norm_nonneg v) (-(N : ℝ)))

end CubicTenVariables.OscillatoryLocalization
