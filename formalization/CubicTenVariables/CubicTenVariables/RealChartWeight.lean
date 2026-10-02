import CubicTenVariables.RealWeight
import Mathlib.Topology.Algebra.MvPolynomial

/-! Smooth counting weights localized to a prescribed neighbourhood.

The constructions retain every field of `SmoothCountingWeight` and additionally
place its closed support inside a supplied neighbourhood. At a nonsingular
polynomial point one chosen formal partial derivative is uniformly bounded
away from zero on that support. These are proved localizations; no inverse
function chart or singular-integral theorem is assumed or asserted here. -/

noncomputable section
namespace CubicTenVariables
open scoped Topology ContDiff
open Filter MvPolynomial HessianTheorem11

/-- The existing counting-weight properties can be obtained with the closed
support contained in any prescribed neighbourhood of a nonzero point. -/
theorem exists_smoothCountingWeight_tsupport_subset {n : ℕ}
    (x : Fin n → ℝ) (hx : x ≠ 0) (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 x) :
    ∃ w : SmoothCountingWeight x, tsupport w.weight ⊆ U := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨w, hsupport, hcompact, hsmooth, hbounds, hwx⟩ :=
    exists_smooth_tsupport_subset
      (inter_mem hU (Metric.ball_mem_nhds x (half_pos hxpos)))
  obtain ⟨A, hA⟩ := exists_nat_ge (‖x‖ + ‖x‖ / 2)
  have horigin : (0 : Fin n → ℝ) ∉ tsupport w := by
    intro hz
    have hb := Metric.mem_ball.mp (hsupport hz).2
    simp only [dist_zero_left] at hb
    linarith
  have hbox : WeightSupportedInBox w A := by
    intro y hy i
    have hyt : y ∈ tsupport w := subset_tsupport w hy
    have hyball := Metric.mem_ball.mp (hsupport hyt).2
    have htri := dist_triangle y x 0
    simp only [dist_zero_right] at htri
    have hnorm : ‖y‖ ≤ (A : ℝ) := by linarith
    have hi := norm_le_pi_norm y i
    simpa only [Real.norm_eq_abs] using hi.trans hnorm
  refine ⟨⟨w, A, hsmooth, hcompact, ?_, hwx, horigin, hbox⟩, ?_⟩
  · intro y
    exact hbounds (Set.mem_range_self y)
  · intro y hy
    exact (hsupport hy).1

/-- Open-neighbourhood form of the localized counting-weight construction. -/
theorem exists_smoothCountingWeight_tsupport_subset_of_isOpen {n : ℕ}
    (x : Fin n → ℝ) (hx : x ≠ 0) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ w : SmoothCountingWeight x, tsupport w.weight ⊆ U :=
  exists_smoothCountingWeight_tsupport_subset x hx U (hU.mem_nhds hxU)

/-- A selected nonzero formal partial derivative can be kept uniformly
away from zero on the weight's entire closed support, while also localizing
inside an independently prescribed neighbourhood. -/
theorem exists_smoothCountingWeight_tsupport_subset_partial_lowerBound {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ≠ 0)
    (i : Fin n) (hi : eval x (pderiv i F) ≠ 0)
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 x) :
    ∃ w : SmoothCountingWeight x, tsupport w.weight ⊆ U ∧
      ∃ c : ℝ, 0 < c ∧ ∀ y ∈ tsupport w.weight, c ≤ |eval y (pderiv i F)| := by
  let c : ℝ := |eval x (pderiv i F)| / 2
  have hc : 0 < c := half_pos (abs_pos.mpr hi)
  let V : Set (Fin n → ℝ) := {y | c < |eval y (pderiv i F)|}
  have hV : IsOpen V :=
    isOpen_lt continuous_const ((MvPolynomial.continuous_eval (pderiv i F)).abs)
  have hxV : x ∈ V := by
    change |eval x (pderiv i F)| / 2 < |eval x (pderiv i F)|
    have hp := abs_pos.mpr hi
    linarith
  obtain ⟨w, hw⟩ := exists_smoothCountingWeight_tsupport_subset x hx (U ∩ V)
    (inter_mem hU (hV.mem_nhds hxV))
  refine ⟨w, fun y hy => (hw hy).1, c, hc, ?_⟩
  intro y hy
  exact le_of_lt (hw hy).2

/-- At a nonsingular polynomial point, one coordinate partial remains
nonzero throughout the closed support of a localized counting weight. -/
theorem exists_smoothCountingWeight_tsupport_subset_partial_ne_zero {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hgrad : gradient F x ≠ 0)
    (U : Set (Fin n → ℝ)) (hU : U ∈ 𝓝 x) :
    ∃ i : Fin n, ∃ w : SmoothCountingWeight x,
      tsupport w.weight ⊆ U ∧
      ∀ y ∈ tsupport w.weight, eval y (pderiv i F) ≠ 0 := by
  classical
  have hex : ∃ i : Fin n, eval x (pderiv i F) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hgrad (funext h)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨w, hw, c, hc, hbound⟩ :=
    exists_smoothCountingWeight_tsupport_subset_partial_lowerBound F x hx i hi U hU
  refine ⟨i, w, hw, ?_⟩
  intro y hy hz
  have hb := hbound y hy
  rw [hz, abs_zero] at hb
  exact (not_le_of_gt hc) hb

/-- Rational anisotropy supplies both a nonzero smooth real zero and an
actual counting weight on whose support a selected partial never vanishes. -/
theorem exists_nonsingular_real_zero_with_localized_weight {n : ℕ}
    (F : AnisotropicCubic n) (hn : 2 ≤ n) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧
      eval x (map (algebraMap ℚ ℝ) F.polynomial) = 0 ∧
      ∃ i : Fin n, ∃ w : SmoothCountingWeight x,
        ∀ y ∈ tsupport w.weight,
          eval y (pderiv i (map (algebraMap ℚ ℝ) F.polynomial)) ≠ 0 := by
  obtain ⟨x, hx, hF, hgrad⟩ := RealPlace.exists_nonsingular_real_zero F hn
  obtain ⟨i, w, _, hpartial⟩ :=
    exists_smoothCountingWeight_tsupport_subset_partial_ne_zero
      (map (algebraMap ℚ ℝ) F.polynomial) x hx hgrad Set.univ (by simp)
  exact ⟨x, hx, hF, i, w, hpartial⟩

end CubicTenVariables
