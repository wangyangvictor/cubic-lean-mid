import TranslatedDepthSeven.ProjectedSourcePacketGradientSplit
import TranslatedDepthSeven.ProjectiveCurveSalbergerConstant

/-!
# Small equations on the whole finite set of points of a curve

Fix the curve, its bounded affine projection, and the whole finite source
set before selecting a residue modulus. Primitive interpolation either cuts
the source curve properly, or supplies a small equation for its exact image.
In the latter case the inverse image of the singular locus is a proper
derivative section. Ordinary curve Bezout bounds both exceptional sets.

The interpolation is the elementary coefficient-removal argument already
proved in `ProjectedSourcePacketSmallEquation`; the derivative section is
the standard device in Heath-Brown's proof of Theorem 14 (Annals 2002).
No relative curve model or assertion about its special fibres is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectedCurve_gradientZero_card_le
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N e : ℕ} (he : 0 < e)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdim : HasProjectiveDimensionDegree I 1 e)
    (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin 3) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := e) I hI A G)
    (P : MvPolynomial (Fin 3) ℤ)
    (hPirred : Irreducible (P.map (Int.castRingHom ℚ)))
    (hPhom : P.IsHomogeneous e)
    (himage : RingHom.ker
      (StandardAG.projectiveMatrixCoordinateMap I
        (A.map (Int.castRingHom ℚ))).toRingHom =
        Ideal.span {P.map (Int.castRingHom ℚ)})
    (X : Finset (IntVector N))
    (hsource : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0) :
    (projectedSourceGradientZeroPoints A P X).card ≤ e * (e - 1) := by
  obtain ⟨j, hhom, hnot, hzero⟩ :=
    projectedSourceGradientZeroPoints_vanish_on_properCut he I hI A G
      hprojection P hPirred hPhom himage X
  apply card_integralAffinePoints_on_projectiveCurve_auxiliary_le
    hBezout I _ hI hIhom hIdim hhom hnot
  · intro z hz
    simpa only [rationalIntegralAffineChartPoint] using
      hsource z ((mem_projectedSourceGradientZeroPoints_iff A P X z).mp hz).1
  · intro z hz
    simpa only [rationalIntegralAffineChartPoint] using hzero z hz

/-- The equation and its singular-image subset are fixed on the whole
finite source set, independently of every subsequent residue modulus. -/
theorem projectedCurve_smallEquation_or_bounded_exceptional_set
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N e M : ℕ} (he : 0 < e)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdim : HasProjectiveDimensionDegree I 1 e)
    (A : Matrix (Fin 3) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin 3) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := e) I hI A G)
    (X : Finset (IntVector N))
    (hsource : ∀ z ∈ X, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0)
    (hbox : ∀ z ∈ X, ∀ j, (z j).natAbs ≤ M) :
    X.card ≤ e * e ∨
      ∃ P : MvPolynomial (Fin 3) ℤ,
        P ≠ 0 ∧ IsPrimitiveIntegralMvPolynomial P ∧
        P.IsHomogeneous e ∧
        (∀ z ∈ X,
          MvPolynomial.eval (integralAffineChartProjection A z) P = 0) ∧
        (∀ m, (P.coeff m).natAbs ≤
          (e + 1) ^ 3 * ((e + 1) ^ 3).factorial *
            max 1 (affineChartProjectionCoefficientMass A * max 1 M) ^
              (e * (e + 1) ^ 3)) ∧
        Irreducible (P.map (Int.castRingHom ℚ)) ∧
        RingHom.ker
          (StandardAG.projectiveMatrixCoordinateMap I
            (A.map (Int.castRingHom ℚ))).toRingHom =
              Ideal.span {P.map (Int.castRingHom ℚ)} ∧
        projectiveIntegralClosureIdeal
          (RingHom.ker
            (StandardAG.projectiveMatrixCoordinateMap I
              (A.map (Int.castRingHom ℚ))).toRingHom) = Ideal.span {P} ∧
        (projectedSourceGradientZeroPoints A P X).card ≤ e * (e - 1) := by
  obtain ⟨P, hP, hprimitive, hhom, hzero, hcoeff, hproper | hdefining⟩ :=
    exists_projectedSourcePacket_smallEquation_or_properCut I hI A G
      hprojection X hsource hbox
  · left
    obtain ⟨hFhom, hFnot, hFzero⟩ := hproper
    apply card_integralAffinePoints_on_projectiveCurve_auxiliary_le
      hBezout I _ hI hIhom hIdim hFhom hFnot X
    · intro z hz
      simpa only [rationalIntegralAffineChartPoint] using hsource z hz
    · intro z hz
      simpa only [rationalIntegralAffineChartPoint] using hFzero z hz
  · right
    obtain ⟨hirred, himage, hclosure⟩ := hdefining
    exact ⟨P, hP, hprimitive, hhom, hzero, hcoeff, hirred, himage,
      hclosure, projectedCurve_gradientZero_card_le hBezout he I hI hIhom
        hIdim A G hprojection P hirred hhom himage X hsource⟩

end

end TranslatedDepthSeven
