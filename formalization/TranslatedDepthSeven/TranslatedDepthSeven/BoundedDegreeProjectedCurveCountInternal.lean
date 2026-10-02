import TranslatedDepthSeven.BoundedDegreePlaneCurveCountInternal
import TranslatedDepthSeven.Salberger2023ProjectedCurveCountInternal

/-! # Internal bounded-degree half-power count on a projected source curve -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Filter Published
open scoped Topology
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000

theorem eventually_boundedDegree_projectedCurve_count_internal
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
      2 ≤ δ → δ ≤ D → (M : ℝ) ≤ V →
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime),
        I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) →
        HasProjectiveDimensionDegree I 1 δ →
      ∀ (A : Matrix (Fin 3) (Fin (N + 1)) ℤ) (G : MvPolynomial (Fin 3) ℚ),
        A ∈ boundedIntegralAffineProjectionMatrices N 1 δ →
        StandardAG.IsAffineChartFiniteBirationalLinearProjection (degree := δ) I hI A G →
      ∀ X : Finset (IntVector N),
        (∀ z ∈ X, ∀ f ∈ I,
          eval (fun j => (integralAffineChartVector z j : ℚ)) f = 0) →
        (∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) →
        (X.card : ℝ) ≤ V ^ ((1 : ℝ) / 2 + ε) := by
  have hplane := eventually_boundedDegree_integralPlaneCurve_count_of_projectedBounds
    N D (ε / 2) (by linarith)
  have hfibre := eventually_count_le_rpow_of_projectedImage_count
    (D : ℝ) ((1 : ℝ) / 2 + ε / 2) ((1 : ℝ) / 2 + ε) (by positivity) (by linarith)
  have hsmall := eventually_degree_sq_le_rpow_of_log_degree
    (D : ℝ) (1 + 2 * ε) (by positivity) (by linarith)
  filter_upwards [hplane, hfibre, hsmall, eventually_ge_atTop (1 : ℝ)]
    with V hplaneV hfibreV hsmallV hV
  intro δ M hδtwo hδD hM I hI hIhom hIdim A G hA hprojection X hsource hbox
  have hδlog : (δ : ℝ) ≤ (D : ℝ) * (1 + Real.log V) := by
    have hlog : 1 ≤ 1 + Real.log V := by
      have := Real.log_nonneg hV
      linarith
    exact (show (δ : ℝ) ≤ D by exact_mod_cast hδD).trans
      (le_mul_of_one_le_right (by positivity) hlog)
  rcases projectedCurve_smallEquation_or_bounded_exceptional_set_of_mem_bounded
      rationalProjectiveCurveAuxiliaryFirstChartBezout_internal (by omega : 0 < δ)
      I hI hIhom hIdim A hA G hprojection X hsource hbox with
    hfew | ⟨P, _hPne, _hPprimitive, hPhom, hPzero, hPcoeff,
      hPirred, _himage, _hclosure, hsingular⟩
  · have hfew' : X.card ≤ δ ^ 2 := by simpa only [pow_two] using hfew
    have hbound := (show (X.card : ℝ) ≤ ((δ ^ 2 : ℕ) : ℝ) by
      exact_mod_cast hfew').trans (hsmallV δ hδlog)
    convert hbound using 1 <;> congr 1 <;> ring
  · let Y : Finset (IntVector 2) := projectedCurvePlaneImage A X
    have hPcoeff' : ∀ m, (P.coeff m).natAbs ≤
        projectedCurveSmallEquationCoefficientBound N δ M := by
      intro m
      simpa only [projectedCurveSmallEquationCoefficientBound,
        projectedCurveCertificateRadius] using hPcoeff m
    obtain ⟨hYzeroAffine, hYbox, hYDheight, hYexceptional⟩ :=
      projectedCurvePlaneImage_data A hA hprojection.1 X hbox P hPhom
        hPzero hPcoeff' hsingular
    have hYzero : ∀ y ∈ Y, eval (integralAffineChartVector y) P = 0 := by
      intro y hy
      simpa only [planeCurveFirstChartPoint, integralAffineChartVector] using
        (planeCurveFirstChart_eval y P).symm.trans (hYzeroAffine y hy)
    have hYbox' : ∀ y ∈ Y, ∀ i,
        (integralAffineChartVector y i).natAbs ≤
          salbergerProjectedCurveBoxRadius N δ M := by
      intro y hy i
      simpa only [salbergerProjectedCurveBoxRadius,
        projectedCurveCertificateRadius] using hYbox y hy i
    have hYexceptional' :
        (Y.filter (fun y => planeCurveDerivativeCertificate
          (planeCurveFirstChartDehomogenize P) y = 0)).card ≤ δ ^ 2 :=
      hYexceptional.trans (by
        calc
          δ * (δ - 1) ≤ δ * δ := Nat.mul_le_mul_left δ (Nat.sub_le δ 1)
          _ = δ ^ 2 := by ring)
    have hYcount : (Y.card : ℝ) ≤ V ^ ((1 : ℝ) / 2 + ε / 2) :=
      hplaneV δ M hδtwo hδD hM P hPhom hPirred Y
        hYzero hYbox' hYDheight hYexceptional'
    have hsourceCard : X.card ≤ δ * Y.card := by
      simpa only [Y, projectedCurvePlaneImage] using
        card_source_le_degree_mul_projectedAffineImage_card
          I hI A G hprojection X hsource
    exact hfibreV δ X.card Y.card hδlog hsourceCard hYcount

end
end TranslatedDepthSeven
