import TranslatedDepthSeven.PlaneCurveDerivativeCertificate
import TranslatedDepthSeven.ProjectedCurvePolylogHeight
import TranslatedDepthSeven.ProjectedCurveImageCard
import TranslatedDepthSeven.ProjectedSourcePacketGradientSplit

/-!
# Literal data on the projected affine plane image

For a bounded affine projection of a finite source packet, this file moves
the displayed plane equation and its derivative certificate to the finite
set of distinct affine image points.  It records the exact projected box,
the coefficient-uniform derivative bound, and the fact that the zero
certificate image points come from the already bounded source singular
locus.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- The finite set of distinct affine tails of the projected source points. -/
def projectedCurvePlaneImage
    {N : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (X : Finset (IntVector N)) : Finset (IntVector 2) :=
  X.image (projectedSourceAffineTail A)

/-- The dehomogenized image equation vanishes on every distinct affine
image point. -/
theorem projectedCurvePlaneImage_zero
    {N : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (X : Finset (IntVector N))
    (P : MvPolynomial (Fin 3) ℤ)
    (hPzero : ∀ z ∈ X,
      MvPolynomial.eval (integralAffineChartProjection A z) P = 0) :
    ∀ y ∈ projectedCurvePlaneImage A X,
      MvPolynomial.eval y (planeCurveFirstChartDehomogenize P) = 0 := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [planeCurveFirstChart_eval]
  have hfull := integralAffineProjectivePoint_projectedSourceAffineTail
    A hfirst z
  change MvPolynomial.eval
    (integralAffineProjectivePoint (projectedSourceAffineTail A z)) P = 0
  rw [hfull]
  exact hPzero z hz

/-- Every homogeneous coordinate `(1,y)` of a projected affine image point
lies in the explicit radius used in the height calculation. -/
theorem projectedCurvePlaneImage_homogeneousBox
    {N δ M : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N 1 δ)
    (X : Finset (IntVector N))
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) :
    ∀ y ∈ projectedCurvePlaneImage A X, ∀ i,
      (integralAffineChartVector y i).natAbs ≤
        projectedCurveCertificateRadius N δ M := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [projectedCurveCertificateRadius]
  · change (integralAffineChartProjection A z j.succ).natAbs ≤ _
    calc
      (integralAffineChartProjection A z j.succ).natAbs ≤
          affineChartProjectionCoefficientMass A * max 1 M :=
        integralAffineChartProjection_coordinate_natAbs_le A z
          (hbox z hz) j.succ
      _ ≤ boundedAffineProjectionRowMassBound N δ * max 1 M :=
        Nat.mul_le_mul_right _
          (affineChartProjectionCoefficientMass_le_of_mem_bounded hA)
      _ ≤ projectedCurveCertificateRadius N δ M := by
        exact Nat.le_max_right _ _

/-- The chosen affine derivative at every image point has the exact common
majorant used by the polylogarithmic-height theorem. -/
theorem projectedCurvePlaneImage_derivativeCertificate_natAbs_le
    {N δ M : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N 1 δ)
    (X : Finset (IntVector N))
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M)
    (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous δ)
    (hPcoeff : ∀ m, (P.coeff m).natAbs ≤
      projectedCurveSmallEquationCoefficientBound N δ M) :
    ∀ y ∈ projectedCurvePlaneImage A X,
      (planeCurveDerivativeCertificate
        (planeCurveFirstChartDehomogenize P) y).natAbs ≤
          projectedCurveDerivativeCertificateBound N δ M := by
  intro y hy
  apply planeCurveDerivativeCertificate_natAbs_le
  intro j
  rw [eval_pderiv_planeCurveFirstChartDehomogenize]
  have hraw := bounded_homogeneous_partial_derivative P hPhom hPcoeff
    (integralAffineChartVector y)
    (projectedCurvePlaneImage_homogeneousBox A hA X hbox y hy) j.succ
  have hR : 1 ≤ projectedCurveCertificateRadius N δ M :=
    Nat.le_max_left _ _
  simpa only [projectedCurveDerivativeCertificateBound,
    max_eq_right hR] using hraw

/-- Image points where the literal derivative certificate vanishes inject
into the image of the source projective-gradient-zero subset.  Hence their
number is bounded by the already proved source exceptional count. -/
theorem card_projectedCurvePlaneImage_certificateZero_le
    {N δ : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (X : Finset (IntVector N))
    (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous δ)
    (hPzero : ∀ z ∈ X,
      MvPolynomial.eval (integralAffineChartProjection A z) P = 0)
    (hsingular : (projectedSourceGradientZeroPoints A P X).card ≤
      δ * (δ - 1)) :
    ((projectedCurvePlaneImage A X).filter fun y ↦
      planeCurveDerivativeCertificate
        (planeCurveFirstChartDehomogenize P) y = 0).card ≤
      δ * (δ - 1) := by
  classical
  let bad := (projectedCurvePlaneImage A X).filter fun y ↦
    planeCurveDerivativeCertificate
      (planeCurveFirstChartDehomogenize P) y = 0
  let sourceBad := projectedSourceGradientZeroPoints A P X
  have hsubset : bad ⊆ sourceBad.image (projectedSourceAffineTail A) := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    obtain ⟨z, hz, hyz⟩ := Finset.mem_image.mp hy'.1
    subst y
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    apply (mem_projectedSourceGradientZeroPoints_iff A P X z).mpr
    refine ⟨hz, ?_⟩
    have hfull := integralAffineProjectivePoint_projectedSourceAffineTail
      A hfirst z
    have hzeroAffine :
        MvPolynomial.eval
          (integralAffineChartVector (projectedSourceAffineTail A z)) P = 0 := by
      change MvPolynomial.eval
        (integralAffineProjectivePoint (projectedSourceAffineTail A z)) P = 0
      rw [hfull]
      exact hPzero z hz
    have hgradient :=
      (planeCurveDerivativeCertificate_eq_zero_iff_projective_gradient
        P hPhom (projectedSourceAffineTail A z) hzeroAffine).mp hy'.2
    intro i
    have hi := hgradient i
    change MvPolynomial.eval
      (integralAffineProjectivePoint (projectedSourceAffineTail A z))
        (MvPolynomial.pderiv i P) = 0 at hi
    rw [hfull] at hi
    exact hi
  calc
    bad.card ≤ (sourceBad.image (projectedSourceAffineTail A)).card :=
      Finset.card_le_card hsubset
    _ ≤ sourceBad.card := Finset.card_image_le
    _ ≤ δ * (δ - 1) := hsingular

/-- All plane-image data needed by the prime-cover count, bundled in the
form in which the subsequent global argument consumes it. -/
theorem projectedCurvePlaneImage_data
    {N δ M : ℕ} (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralAffineProjectionMatrices N 1 δ)
    (hfirst : FirstFinProjectionRowIsHomogenizingCoordinate
      (A.map (Int.castRingHom ℚ)))
    (X : Finset (IntVector N))
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M)
    (P : MvPolynomial (Fin 3) ℤ)
    (hPhom : P.IsHomogeneous δ)
    (hPzero : ∀ z ∈ X,
      MvPolynomial.eval (integralAffineChartProjection A z) P = 0)
    (hPcoeff : ∀ m, (P.coeff m).natAbs ≤
      projectedCurveSmallEquationCoefficientBound N δ M)
    (hsingular : (projectedSourceGradientZeroPoints A P X).card ≤
      δ * (δ - 1)) :
    let Y := projectedCurvePlaneImage A X
    let f := planeCurveFirstChartDehomogenize P
    let D := planeCurveDerivativeCertificate f
    (∀ y ∈ Y, MvPolynomial.eval y f = 0) ∧
    (∀ y ∈ Y, ∀ i,
      (integralAffineChartVector y i).natAbs ≤
        projectedCurveCertificateRadius N δ M) ∧
    (∀ y ∈ Y, (D y).natAbs ≤
      projectedCurveDerivativeCertificateBound N δ M) ∧
    ((Y.filter fun y ↦ D y = 0).card ≤ δ * (δ - 1)) := by
  exact ⟨projectedCurvePlaneImage_zero A hfirst X P hPzero,
    projectedCurvePlaneImage_homogeneousBox A hA X hbox,
    projectedCurvePlaneImage_derivativeCertificate_natAbs_le
      A hA X hbox P hPhom hPcoeff,
    card_projectedCurvePlaneImage_certificateZero_le
      A hfirst X P hPhom hPzero hsingular⟩

end

end TranslatedDepthSeven
