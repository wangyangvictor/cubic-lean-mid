import CubicTenVariables.OscillatoryLocalization

/-! The cited normalized localization window becomes an actual physical
coordinate/gradient window, with the exact Lebesgue Jacobian. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.OscillatoryLocalization
open MvPolynomial MeasureTheory HessianTheorem11
open scoped BigOperators Topology ContDiff Pointwise

variable {n : ℕ}

def physicalWindow (F : MvPolynomial (Fin n) ℝ) (x₀ : Fin n → ℝ)
    (ρ P θ : ℝ) (β : Fin n → ℝ) (H R : ℝ) : Set (Fin n → ℝ) :=
  {x | ‖P⁻¹ • x-x₀‖ ≤ 2*ρ ∧
    ‖(fun i => θ*eval x (pderiv i F)-β i)‖ ≤
      (R/(P*ρ))*max 1 (Real.sqrt (|θ*P^3| * H))}

theorem gradient_phase_chart (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (x₀ : Fin n → ℝ) (ρ P θ : ℝ) (β y : Fin n → ℝ) :
    (fun i => (θ*P^3)*eval y (pderiv i (chartPolynomial F x₀ ρ)) - ((P*ρ) • β) i) =
      (P*ρ) • (fun i => θ*eval (P • chartPoint x₀ ρ y) (pderiv i F)-β i) := by
  funext i
  have hg := eval_homogeneous_smul (pderiv i F) hF.pderiv P (chartPoint x₀ ρ y)
  simp only [pderiv_chartPolynomial,eval_mul,eval_C,eval_chartPolynomial,
    Pi.smul_apply,smul_eq_mul,hg]
  norm_num
  ring

theorem chart_inverse (x₀ x : Fin n → ℝ) (ρ P : ℝ) (hρ : ρ ≠ 0) (hP : P ≠ 0) :
    P • chartPoint x₀ ρ (ρ⁻¹ • (P⁻¹ • x-x₀)) = x := by
  simp [chartPoint,hρ,hP]

theorem mem_physicalWindow_chart (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β y : Fin n → ℝ) (H R : ℝ) :
    P • chartPoint x₀ ρ y ∈ physicalWindow F x₀ ρ P θ β H R ↔
      y ∈ PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
        1 H (θ*P^3) ((P*ρ) • β) R := by
  simp only [physicalWindow,PolynomialOscillatory.window,Set.mem_setOf_eq]
  rw [inv_smul_smul₀ hP.ne',gradient_phase_chart F hF,norm_smul,Real.norm_eq_abs,
    abs_of_pos (mul_pos hP hρ)]
  have hc : chartPoint x₀ ρ y-x₀=ρ • y := by simp [chartPoint]
  rw [hc,norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
  have hr : (R/(P*ρ))*max 1 (Real.sqrt (|θ*P^3| * H)) =
      (R*max 1 (Real.sqrt (|θ*P^3| * H)))/(P*ρ) := by ring
  rw [hr,le_div_iff₀ (mul_pos hP hρ)]
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_⟩
    · have h := (mul_le_mul_iff_right₀ hρ).mp (by simpa [mul_comm] using h1)
      norm_num at ⊢; exact h
    · simpa [mul_comm] using h2
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_⟩
    · norm_num at h1
      simpa [mul_comm] using mul_le_mul_of_nonneg_left h1 hρ.le
    · simpa [mul_comm] using h2

theorem physicalWindow_eq_image (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β : Fin n → ℝ) (H R : ℝ) :
    physicalWindow F x₀ ρ P θ β H R =
      (fun y => P • chartPoint x₀ ρ y) ''
        PolynomialOscillatory.window (chartPolynomial F x₀ ρ) 1 H (θ*P^3) ((P*ρ) • β) R := by
  ext x
  constructor
  · intro hx
    let y := ρ⁻¹ • (P⁻¹ • x-x₀)
    have he : P • chartPoint x₀ ρ y=x := chart_inverse x₀ x ρ P hρ.ne' hP.ne'
    refine ⟨y,?_,he⟩
    apply (mem_physicalWindow_chart F hF x₀ ρ P hρ hP θ β y H R).mp
    rwa [he]
  · rintro ⟨y,hy,rfl⟩
    exact (mem_physicalWindow_chart F hF x₀ ρ P hρ hP θ β y H R).mpr hy

/-- Translation and scalar dilation of an arbitrary set, without a
measurability side condition or any convention about infinite real volume. -/
theorem volume_affine_image (a : Fin n → ℝ) (s : ℝ) (S : Set (Fin n → ℝ)) :
    volume ((fun y => a+s • y) '' S) = ENNReal.ofReal |s^n| * volume S := by
  have he : (fun y => a+s • y) '' S = (fun z => -a+z) ⁻¹' (s • S) := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,by simp⟩
    · rintro ⟨y,hy,h⟩
      refine ⟨y,hy,?_⟩
      change s • y = -a+z at h
      change a+s • y=z
      rw [h]
      simp
  rw [he,measure_preimage_add,Measure.addHaar_smul,Module.finrank_pi,Fintype.card_fin]

theorem physicalWindow_measure (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β : Fin n → ℝ) (H R : ℝ) :
    (volume (physicalWindow F x₀ ρ P θ β H R)).toReal =
      (P*ρ)^n * (volume (PolynomialOscillatory.window (chartPolynomial F x₀ ρ)
        1 H (θ*P^3) ((P*ρ) • β) R)).toReal := by
  rw [physicalWindow_eq_image F hF x₀ ρ P hρ hP]
  have he : (fun y => P • chartPoint x₀ ρ y) = fun y => P • x₀+(P*ρ) • y := by
    funext y
    simp [chartPoint,smul_add,smul_smul]
  rw [he,volume_affine_image,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (pow_pos (mul_pos hP hρ) n)]

/-- Every point of the enlarged physical window remains in the prescribed
fixed chart neighborhood after division by P. -/
theorem physicalWindow_subset_chart (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (x₀ : Fin n → ℝ) (ρ P : ℝ) (hρ : 0 < ρ) (hP : 0 < P)
    (θ : ℝ) (β : Fin n → ℝ) (H R : ℝ) (U : Set (Fin n → ℝ))
    (hU : ∀ y : Fin n → ℝ, ‖y‖ ≤ 2 → chartPoint x₀ ρ y ∈ U) :
    ∀ x ∈ physicalWindow F x₀ ρ P θ β H R, P⁻¹ • x ∈ U := by
  rw [physicalWindow_eq_image F hF x₀ ρ P hρ hP]
  rintro _ ⟨y,hy,rfl⟩
  rw [inv_smul_smul₀ hP.ne']
  exact hU y (by have hh : ‖y‖ ≤ 1+1 := hy.1; norm_num at hh; exact hh)

/-- The exact physical integral localization with a free decay parameter.
Only the generic literature lemma is an input; the physical gradient and
Lebesgue-volume normalization are derived here. -/
theorem localization_physical (lit : Literature.BrowningHeathBrown2009Lemma6)
    (hn : 1 ≤ n) (F : MvPolynomial (Fin n) ℝ) (hF : F.IsHomogeneous 3)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hs : ∀ x ∈ tsupport w, ‖x‖ ≤ 1)
    (x₀ : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∃ C R₀ : ℝ, 1 ≤ C ∧ 1 ≤ R₀ ∧
      ∀ P : ℝ, 0 < P → ∀ (θ : ℝ) (β : Fin n → ℝ) (R : ℝ), R₀ ≤ R →
      ‖scaledIntegral F (chartWeight w x₀ ρ) P θ β‖ ≤
        C * ((P*ρ)^n*R^(-(N : ℝ)) +
          (volume (physicalWindow F x₀ ρ P θ β H R)).toReal) := by
  obtain ⟨H,hH,h⟩ := localization_on_chart lit hn F hF w hw hc hwn hs x₀ ρ hρ
  refine ⟨H,hH,?_⟩
  intro N hN
  obtain ⟨C,R₀,hC,hR₀,hb⟩ := h N hN
  refine ⟨C,R₀,hC,hR₀,?_⟩
  intro P hP θ β R hR
  rw [physicalWindow_measure F hF x₀ ρ P hρ hP]
  convert hb P hP θ β R hR using 1; ring

end CubicTenVariables.OscillatoryLocalization
