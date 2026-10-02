import CubicTenVariables.RealRegularGradientChart
import CubicTenVariables.SelectedGradientSliceVolume
import Mathlib.Analysis.Calculus.MeanValue

/-! Full-gradient variation on the actual fixed regular chart box.
The bound is obtained from the continuous polynomial derivative on a compact
convex box and the proved selected-coordinate inverse-distance estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace CubicTenVariables.GradientChartLipschitz
open MvPolynomial HessianTheorem11 RealRegularGradientChart SelectedGradientCoordinates
open scoped BigOperators Topology ContDiff NNReal

/-- Every polynomial gradient has a fixed Lipschitz constant on a fixed
compact convex set. No polynomial degree or rank assumption is needed. -/
theorem exists_gradient_lipschitz {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ LipschitzOnWith L (gradient F) K := by
  have hs : ContDiff ℝ ∞ (gradient F) := by
    apply contDiff_pi.mpr
    intro i
    exact NormedPolynomialChart.contDiff_eval (pderiv i F)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (hs.continuous_fderiv (by simp)).continuousOn
  let L : ℝ≥0 := ⟨max 1 B,le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨L,?_,?_⟩
  · change (1 : ℝ) ≤ max 1 B
    exact le_max_left _ _
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hs.differentiable (by simp) x) _ hconv
    intro x hx
    change ‖fderiv ℝ (gradient F) x‖ ≤ max 1 B
    exact (hB x hx).trans (le_max_right _ _)

theorem box_convex (F : MvPolynomial (Fin 10) ℝ) (D : Data F) : Convex ℝ D.box := by
  change Convex ℝ {x : Fin 10 → ℝ | ‖x-D.point‖ ≤ 2*D.radius}
  simpa only [Metric.closedBall,dist_eq_norm] using convex_closedBall D.point (2*D.radius)

/-- One fixed NNReal constant controls the full actual gradient everywhere
on the enlarged localization box. -/
theorem exists_box_lipschitz (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ LipschitzOnWith L (gradient F) D.box :=
  exists_gradient_lipschitz F D.box D.box_compact (box_convex F D)

/-- On every fixed untouched-input fiber, the full gradient is controlled
by its seven selected coordinates. Rows and columns need not coincide. -/
theorem exists_complement_variation_bound (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ ∀ x ∈ D.box, ∀ y ∈ D.box,
      (∀ i : Complement D.cols, x i=y i) →
      ‖gradient F x-gradient F y‖ ≤ (L : ℝ)*
        ‖(fun i : Fin 7 => eval x (pderiv (D.rows i) F))-
          (fun i : Fin 7 => eval y (pderiv (D.rows i) F))‖ := by
  obtain ⟨B,hB,hLip⟩ := exists_box_lipschitz F D
  let L : ℝ≥0 := max 1 (B*D.antiConstant)
  refine ⟨L,le_max_left _ _,?_⟩
  intro x hx y hy heq
  have hinv := SelectedGradientSliceVolume.dist_le_selected_of_complement_eq F D.rows D.cols
    D.domain D.antiConstant D.antilipschitz x y
    (D.box_subset_domain hx) (D.box_subset_domain hy) heq
  have hg := hLip.dist_le_mul x hx y hy
  have hB0 : 0 ≤ (B : ℝ) := B.coe_nonneg
  have hle : (B : ℝ)*(D.antiConstant : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (le_max_right 1 (B*D.antiConstant))
  have hcomp := hg.trans (mul_le_mul_of_nonneg_left hinv hB0)
  have hd := mul_le_mul_of_nonneg_right hle
    (dist_nonneg : 0 ≤ dist (fun i : Fin 7 => eval x (pderiv (D.rows i) F))
      (fun i : Fin 7 => eval y (pderiv (D.rows i) F)))
  simpa only [dist_eq_norm,mul_assoc] using hcomp.trans (by simpa only [mul_assoc] using hd)

/-- The scalar phase can be arbitrary, including zero. A shared selected-
gradient window controls every component of the full scaled gradient. -/
theorem exists_scaled_window_variation_bound (F : MvPolynomial (Fin 10) ℝ) (D : Data F) :
    ∃ L : ℝ≥0, 1 ≤ L ∧ ∀ (α δ : ℝ) (b : Fin 7 → ℝ), 0 ≤ δ →
      ∀ x ∈ D.box, ∀ y ∈ D.box,
      (∀ i : Complement D.cols, x i=y i) →
      ‖α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))-b‖ ≤ δ →
      ‖α • (fun i : Fin 7 => eval y (pderiv (D.rows i) F))-b‖ ≤ δ →
      ‖α • gradient F x-α • gradient F y‖ ≤ 2*(L : ℝ)*δ := by
  obtain ⟨L,hL,h⟩ := exists_complement_variation_bound F D
  refine ⟨L,hL,?_⟩
  intro α δ b hδ x hx y hy heq hxb hyb
  have hb := h x hx y hy heq
  have hm := mul_le_mul_of_nonneg_left hb (abs_nonneg α)
  have htri : ‖α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))-
      α • (fun i : Fin 7 => eval y (pderiv (D.rows i) F))‖ ≤ 2*δ := by
    calc
      _ ≤ ‖α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))-b‖+
        ‖α • (fun i : Fin 7 => eval y (pderiv (D.rows i) F))-b‖ :=
          by simpa only [norm_sub_rev b] using
            norm_sub_le_norm_sub_add_norm_sub
              (α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))) b
              (α • (fun i : Fin 7 => eval y (pderiv (D.rows i) F)))
      _ ≤ _ := by linarith
  have hnorm : ‖α • gradient F x-α • gradient F y‖ ≤ (L : ℝ)*
      ‖α • (fun i : Fin 7 => eval x (pderiv (D.rows i) F))-
        α • (fun i : Fin 7 => eval y (pderiv (D.rows i) F))‖ := by
    simpa only [← smul_sub,norm_smul,Real.norm_eq_abs,mul_left_comm] using hm
  exact hnorm.trans ((mul_le_mul_of_nonneg_left htri L.coe_nonneg).trans_eq (by ring))

end CubicTenVariables.GradientChartLipschitz
