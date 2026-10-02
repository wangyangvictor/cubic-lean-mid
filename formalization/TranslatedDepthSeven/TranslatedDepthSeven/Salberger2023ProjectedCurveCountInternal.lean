import TranslatedDepthSeven.BoundedAffineProjectionMassInternal
import TranslatedDepthSeven.ProjectedCurveImageCard
import TranslatedDepthSeven.ProjectedCurvePlaneImageData
import TranslatedDepthSeven.RationalProjectiveCurveFirstChartBezoutInternal
import TranslatedDepthSeven.Salberger2023PlaneCurveGlobalCountInternal

/-!
# The internal high-degree count for a projected source curve

The bounded affine projection either finds at most `δ²` source points, or
gives one literal primitive plane equation for the entire projected image.
In the latter case the internal plane-curve prime-cover theorem counts the
distinct image points, and the proved finite-projection fibre bound loses at
most `δ`.  Both polynomial degree losses are absorbed uniformly under
`δ ≤ Cd * (1 + log V)`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Filter Published
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2500000

/-- The `δ²` branch of the small-equation alternative is uniformly
negligible under a logarithmic degree bound. -/
theorem eventually_degree_sq_le_rpow_of_log_degree
    (Cd ε : ℝ) (_hCd : 0 ≤ Cd) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ δ : ℕ,
      (δ : ℝ) ≤ Cd * (1 + Real.log V) →
      ((δ ^ 2 : ℕ) : ℝ) ≤ V ^ (ε / 2) := by
  have habsorb := eventually_polylog_mul_rpow_le_rpow
    (Cd ^ 2) 0 (ε / 2) 2 (sq_nonneg Cd) (by linarith)
  filter_upwards [habsorb, eventually_ge_atTop (1 : ℝ)] with V habsorb hV
  intro δ hδ
  have hlog : 0 ≤ 1 + Real.log V := by
    have := Real.log_nonneg hV
    linarith
  have hδsq : (δ : ℝ) ^ 2 ≤ Cd ^ 2 * (1 + Real.log V) ^ 2 := by
    calc
      (δ : ℝ) ^ 2 ≤ (Cd * (1 + Real.log V)) ^ 2 := by gcongr
      _ = Cd ^ 2 * (1 + Real.log V) ^ 2 := by ring
  calc
    ((δ ^ 2 : ℕ) : ℝ) = (δ : ℝ) ^ 2 := by norm_num
    _ ≤ Cd ^ 2 * (1 + Real.log V) ^ 2 := hδsq
    _ = Cd ^ 2 * (1 + Real.log V) ^ 2 * V ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
    _ ≤ V ^ (ε / 2) := habsorb

/-- The complete high-degree projected-source curve estimate.  The cutoff
and the height threshold are selected before the curve, the bounded
projection, its equation and the finite point set.  The theorem uses no
Salberger callback: the plane determinant method and its prime cover have
already been proved internally. -/
theorem exists_eventually_projectedCurve_count_internal
    (N : ℕ) (Cd ε : ℝ) (hCd : 0 ≤ Cd) (hε : 0 < ε) :
    ∃ cutoff : ℕ,
      ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
        cutoff < δ →
        (δ : ℝ) ≤ Cd * (1 + Real.log V) →
        (M : ℝ) ≤ V →
        ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime),
          I.IsHomogeneous
              (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
          HasProjectiveDimensionDegree I 1 δ →
        ∀ (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
          (G : MvPolynomial (Fin 3) ℚ),
          A ∈ boundedIntegralAffineProjectionMatrices N 1 δ →
          StandardAG.IsAffineChartFiniteBirationalLinearProjection
              (degree := δ) I hI A G →
        ∀ X : Finset (IntVector N),
          (∀ z ∈ X, ∀ f ∈ I,
            MvPolynomial.eval
              (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0) →
          (∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) →
          (X.card : ℝ) ≤ V ^ (ε / 2) := by
  let εplane : ℝ := ε / 2
  let cutoff : ℕ := ⌈16 / εplane⌉₊
  have hεplane : 0 < εplane := by dsimp only [εplane]; linarith
  have hplane := eventually_integralPlaneCurve_count_of_projectedBounds
    N Cd εplane hCd hεplane
  have hfibre := eventually_count_le_rpow_of_projectedImage_count
    Cd (ε / 4) (ε / 2) hCd (by linarith)
  have hsmall := eventually_degree_sq_le_rpow_of_log_degree Cd ε hCd hε
  refine ⟨cutoff, ?_⟩
  filter_upwards [hplane, hfibre, hsmall] with V hplaneV hfibreV hsmallV
  intro δ M hhigh hδ hM I hI hIhom hIdim A G hA hprojection X hsource hbox
  have hδpos : 0 < δ := by
    have : 0 ≤ cutoff := Nat.zero_le cutoff
    omega
  rcases projectedCurve_smallEquation_or_bounded_exceptional_set_of_mem_bounded
      rationalProjectiveCurveAuxiliaryFirstChartBezout_internal hδpos
      I hI hIhom hIdim A hA G hprojection X hsource hbox with
    hfew | ⟨P, _hPne, _hPprimitive, hPhom, hPzero, hPcoeff,
      hPirred, _himage, _hclosure, hsingular⟩
  · have hfew' : X.card ≤ δ ^ 2 := by simpa only [pow_two] using hfew
    exact (show (X.card : ℝ) ≤ ((δ ^ 2 : ℕ) : ℝ) by exact_mod_cast hfew').trans
      (hsmallV δ hδ)
  · let Y : Finset (IntVector 2) := projectedCurvePlaneImage A X
    have hPcoeff' : ∀ m, (P.coeff m).natAbs ≤
        projectedCurveSmallEquationCoefficientBound N δ M := by
      intro m
      simpa only [projectedCurveSmallEquationCoefficientBound,
        projectedCurveCertificateRadius] using hPcoeff m
    obtain ⟨hYzeroAffine, hYbox, hYDheight, hYexceptional⟩ :=
      projectedCurvePlaneImage_data A hA hprojection.1 X hbox P hPhom
        hPzero hPcoeff' hsingular
    have hYzero : ∀ y ∈ Y,
        MvPolynomial.eval (integralAffineChartVector y) P = 0 := by
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
        (Y.filter (fun y ↦ planeCurveDerivativeCertificate
          (planeCurveFirstChartDehomogenize P) y = 0)).card ≤ δ ^ 2 :=
      hYexceptional.trans (by
        calc
          δ * (δ - 1) ≤ δ * δ := Nat.mul_le_mul_left δ (Nat.sub_le δ 1)
          _ = δ ^ 2 := by ring)
    have hYcount : (Y.card : ℝ) ≤ V ^ (ε / 4) := by
      have hplaneBound := hplaneV δ M
        (by simpa only [cutoff, εplane] using hhigh) hδ hM
        P hPhom hPirred Y hYzero hYbox' hYDheight hYexceptional'
      have hexponent : εplane / 2 = ε / 4 := by
        dsimp only [εplane]
        ring
      simpa only [hexponent] using hplaneBound
    have hsourceCard : X.card ≤ δ * Y.card := by
      simpa only [Y, projectedCurvePlaneImage] using
        card_source_le_degree_mul_projectedAffineImage_card
          I hI A G hprojection X hsource
    exact hfibreV δ X.card Y.card hδ hsourceCard hYcount

end

end TranslatedDepthSeven
