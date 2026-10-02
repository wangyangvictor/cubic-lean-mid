import CubicTenVariables.HighRankLocalPoint
import CubicTenVariables.SelectedGradientCoordinates
import CubicTenVariables.OscillatoryLocalizationApplication

/-! A fixed real rank-seven gradient chart and an actual counting weight.
The whole enlarged oscillatory localization box lies inside the chart.
No point-counting, measure-comparison, or literature input is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace CubicTenVariables.RealRegularGradientChart
open MvPolynomial HessianTheorem11
open SelectedGradientCoordinates OscillatoryLocalization
open scoped BigOperators Topology ContDiff NNReal

/-- Every rank lower bound yields a minor of the specified size, not merely
one of the full rank. Rows and columns are chosen independently. -/
theorem exists_minor_of_le_rank {K : Type*} [Field K] {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hr : r ≤ M.rank) :
    ∃ rows cols : Fin r → Fin n, (M.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨rs,cs,hd⟩ := MatrixRankMinors.exists_rank_minor M
  let A := M.submatrix rs cs
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
  have hli := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  let N := A.submatrix id (Fin.castLE hr)
  have hNli : LinearIndependent K N.col := hli.comp (Fin.castLE hr) (Fin.castLE_injective hr)
  have hNr : N.rank=r := by
    rw [Matrix.rank_eq_finrank_span_cols,finrank_span_eq_card hNli,Fintype.card_fin]
  obtain ⟨rows,cols,hdN⟩ := MatrixRankMinors.exists_rank_minor N
  let e : Fin r ≃ Fin N.rank := finCongr hNr.symm
  refine ⟨rs ∘ rows ∘ e,cs ∘ Fin.castLE hr ∘ cols ∘ e,?_⟩
  change ((N.submatrix rows cols).submatrix e e).det ≠ 0
  rw [Matrix.det_submatrix_equiv_self]
  exact hdN

/-- Real Hessian specialization with symbolic dimensions. -/
theorem exists_real_hessian_minor {n r : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hr : r ≤ (hessian F x).rank) :
    ∃ rows cols : Fin r → Fin n, ((hessian F x).submatrix rows cols).det ≠ 0 := by
  exact exists_minor_of_le_rank (hessian F x) hr

/-- Real-field specialization at symbolic dimensions, avoiding expansion of
finite determinant enumerators when the chart is later instantiated. -/
theorem exists_real_selectedGradient_antilipschitz {n r : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (rows cols : Fin r → Fin n)
    (hd : ((hessian F x).submatrix rows cols).det ≠ 0) :
    ∃ (U : Set (Fin n → ℝ)) (C : ℝ≥0), x ∈ U ∧ IsOpen U ∧
      AntilipschitzWith C (U.restrict (selectedGradientCoordinates F rows cols)) := by
  classical
  exact exists_selectedGradient_antilipschitz F rows cols x hd

/-- All chart and weight data are selected before analytic scales, phases,
or localization centers. The minor is literal and need not be principal. -/
structure Data (F : MvPolynomial (Fin 10) ℝ) where
  point : Fin 10 → ℝ
  point_ne_zero : point ≠ 0
  point_zero : eval point F = 0
  gradient_ne_zero : gradient F point ≠ 0
  rows : Fin 7 → Fin 10
  cols : Fin 7 → Fin 10
  minor_ne_zero : ((hessian F point).submatrix rows cols).det ≠ 0
  domain : Set (Fin 10 → ℝ)
  point_mem : point ∈ domain
  domain_open : IsOpen domain
  antiConstant : ℝ≥0
  antilipschitz : AntilipschitzWith antiConstant
    (domain.restrict (selectedGradientCoordinates F rows cols))
  radius : ℝ
  radius_pos : 0 < radius
  normalizedWeight : (Fin 10 → ℝ) → ℝ
  normalized_smooth : ContDiff ℝ ∞ normalizedWeight
  normalized_compact : HasCompactSupport normalizedWeight
  normalized_nonneg : ∀ x, 0 ≤ normalizedWeight x
  normalized_support : ∀ x ∈ tsupport normalizedWeight, ‖x‖ ≤ 1
  weight : SmoothCountingWeight point
  weight_eq : weight.weight=chartWeight normalizedWeight point radius
  chart_inside : ∀ y : Fin 10 → ℝ, ‖y‖ ≤ 2 → chartPoint point radius y ∈ domain
  partialIndex : Fin 10
  partialBound : ℝ
  partialBound_pos : 0 < partialBound
  partial_lowerBound : ∀ z : Fin 10 → ℝ, ‖z-point‖ ≤ 2*radius →
    partialBound ≤ |eval z (pderiv partialIndex F)|

def Data.box {F : MvPolynomial (Fin 10) ℝ} (D : Data F) : Set (Fin 10 → ℝ) :=
  {x | ‖x-D.point‖ ≤ 2*D.radius}

theorem Data.rows_injective {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    Function.Injective D.rows :=
  rows_injective_of_submatrix_det_ne_zero _ _ _ D.minor_ne_zero

theorem Data.cols_injective {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    Function.Injective D.cols :=
  cols_injective_of_submatrix_det_ne_zero _ _ _ D.minor_ne_zero

theorem Data.box_compact {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    IsCompact D.box := by
  change IsCompact {x : Fin 10 → ℝ | ‖x-D.point‖ ≤ 2*D.radius}
  simpa only [Metric.closedBall,dist_eq_norm] using isCompact_closedBall D.point (2*D.radius)

theorem Data.box_subset_domain {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    D.box ⊆ D.domain := by
  intro x hx
  let y := D.radius⁻¹ • (x-D.point)
  have hy : ‖y‖ ≤ 2 := by
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr D.radius_pos)]
    have hh := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr D.radius_pos.le)
    exact hh.trans_eq (by field_simp [D.radius_pos.ne'])
  have he : chartPoint D.point D.radius y=x := by simp [chartPoint,y,D.radius_pos.ne']
  rw [← he]
  exact D.chart_inside y hy

theorem Data.support_subset_box {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    tsupport D.weight.weight ⊆ D.box := by
  intro x hx
  rw [D.weight_eq] at hx
  have hh := chartWeight_support D.normalizedWeight D.normalized_support D.point D.radius x hx
  have hb := mul_le_mul_of_nonneg_left hh D.radius_pos.le
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr D.radius_pos)] at hb
  have hc : ‖x-D.point‖ ≤ D.radius := by
    simpa only [mul_one,← mul_assoc,mul_inv_cancel₀ D.radius_pos.ne',one_mul] using hb
  change ‖x-D.point‖ ≤ 2*D.radius
  linarith [D.radius_pos]

theorem Data.exists_box_bound {F : MvPolynomial (Fin 10) ℝ} (D : Data F) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ D.box, ∀ i : Fin 10, |x i| ≤ B := by
  refine ⟨max 1 (2*D.radius+‖D.point‖),le_max_left _ _,?_⟩
  intro x hx i
  have ht := norm_le_norm_sub_add x D.point
  have hb : ‖x‖ ≤ 2*D.radius+‖D.point‖ := by
    have hh : ‖x-D.point‖ ≤ 2*D.radius := hx
    linarith
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  exact hi.trans (hb.trans (le_max_right _ _))

/-- Rational anisotropy proves the nonzero smooth real zero and supplies
rank at least eight there; this theorem selects seven actual coordinates
and builds the regular chart and counting weight with no analytic input. -/
theorem exists_data (F : AnisotropicCubic 10) :
    Nonempty (Data (map (algebraMap ℚ ℝ) F.polynomial)) := by
  classical
  obtain ⟨x,hx,hFx,hgrad⟩ := RealPlace.exists_nonsingular_real_zero F (by norm_num)
  have hex : ∃ i : Fin 10, eval₂ (algebraMap ℚ ℝ) x (pderiv i F.polynomial) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hgrad
    ext i
    simpa [gradient,pderiv_map,eval_map] using h i
  obtain ⟨i,hi⟩ := hex
  obtain ⟨y,hy,_,hFy,hgy,hry⟩ := HighRankLocalPoint.exists_high_rank_zero_mem_open
    F x hx (by simpa only [eval_map] using hFx) i hi Set.univ isOpen_univ (Set.mem_univ _)
  have hgy' : gradient (map (algebraMap ℚ ℝ) F.polynomial) y ≠ 0 := by
    obtain ⟨j,hj⟩ := hgy
    intro h
    apply hj
    simpa [gradient,pderiv_map,eval_map] using congrFun h j
  obtain ⟨rows,cols,hd⟩ := exists_real_hessian_minor
    (map (algebraMap ℚ ℝ) F.polynomial) y (show 7 ≤ _ from by omega)
  obtain ⟨U,C,hyU,hU,hanti⟩ := exists_real_selectedGradient_antilipschitz
    (map (algebraMap ℚ ℝ) F.polynomial) y rows cols hd
  obtain ⟨j,hj⟩ := hgy
  let G := map (algebraMap ℚ ℝ) F.polynomial
  have hj' : eval y (pderiv j G) ≠ 0 := by
    simpa [G,pderiv_map,eval_map] using hj
  let c : ℝ := |eval y (pderiv j G)|/2
  have hcpos : 0 < c := half_pos (abs_pos.mpr hj')
  let V : Set (Fin 10 → ℝ) := {z | c < |eval z (pderiv j G)|}
  have hV : IsOpen V := isOpen_lt continuous_const (pderiv j G).continuous_eval.abs
  have hyV : y ∈ V := by
    change |eval y (pderiv j G)|/2 < |eval y (pderiv j G)|
    linarith [abs_pos.mpr hj']
  obtain ⟨ρ,w,W,hρ,hw,hc,hwn,hs,hW,_,hchart⟩ :=
    exists_counting_weight_chart y hy (U ∩ V)
      (Filter.inter_mem (hU.mem_nhds hyU) (hV.mem_nhds hyV))
  have hpartial : ∀ z : Fin 10 → ℝ, ‖z-y‖ ≤ 2*ρ →
      c ≤ |eval z (pderiv j G)| := by
    intro z hz
    let a := ρ⁻¹ • (z-y)
    have ha : ‖a‖ ≤ 2 := by
      dsimp [a]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
      exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hρ.le)).trans_eq
        (by field_simp [hρ.ne'])
    have he : chartPoint y ρ a=z := by simp [chartPoint,a,hρ.ne']
    have hv := (hchart a ha).2
    rw [he] at hv
    exact le_of_lt hv
  exact ⟨{
    point := y
    point_ne_zero := hy
    point_zero := by simpa [eval_map] using hFy
    gradient_ne_zero := hgy'
    rows := rows
    cols := cols
    minor_ne_zero := hd
    domain := U
    point_mem := hyU
    domain_open := hU
    antiConstant := C
    antilipschitz := hanti
    radius := ρ
    radius_pos := hρ
    normalizedWeight := w
    normalized_smooth := hw
    normalized_compact := hc
    normalized_nonneg := hwn
    normalized_support := hs
    weight := W
    weight_eq := hW
    chart_inside := fun a ha => (hchart a ha).1
    partialIndex := j
    partialBound := c
    partialBound_pos := hcpos
    partial_lowerBound := hpartial }⟩

end CubicTenVariables.RealRegularGradientChart
