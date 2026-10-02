import TranslatedDepthSeven.PlaneCurveResidueDiscFirstChart
import TranslatedDepthSeven.Salberger2023LocalCurveThreshold

/-!
# Salberger's local packet bound for a literal plane equation

This closes the chart-construction seam in equation (3.14): a packet of
integral affine points on a homogeneous plane curve, all reducing to a point
where one affine partial is nonzero, automatically has the formally-etale
residue disc required by the local determinant argument.
-/

namespace TranslatedDepthSeven
noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equation (3.14) for a literal homogeneous plane equation.  There is no
residue-disc, smooth-chart, or formal-etaleness premise. -/
theorem card_planeCurvePacket_le_degree_sq_of_prime_threshold
    (hMonomial : StandardAG.RationalProjectiveCurveDegreeMonomialBlock)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {δ p V : ℕ} (hδ : 1 ≤ δ) (hV : 1 ≤ V) (hpprime : p.Prime)
    (P : MvPolynomial (Fin 3) ℤ)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 δ)
    (points : Finset (IntVector 2))
    (hIzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0)
    (hPzero : ∀ z ∈ points,
      MvPolynomial.eval (integralAffineChartVector z) P = 0)
    (center : Fin 2 → ℤ)
    (hsame : ∀ z ∈ points, ∀ i, (p : ℤ) ∣ z i - center i)
    (v : Fin 2)
    (hpartial : (MvPolynomial.eval center
      (MvPolynomial.pderiv v (planeCurveFirstChartDehomogenize P)) : ZMod p) ≠ 0)
    (hbox : ∀ z ∈ points, ∀ i,
      (integralAffineChartVector z i).natAbs ≤ V)
    (hpositive : 0 < affineLineJetWeight (salbergerCurveMonomialCount δ))
    (hp : 4 * (V : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p) :
    points.card ≤ δ ^ 2 := by
  classical
  by_cases hnonempty : points.Nonempty
  · letI : Nonempty (Fin points.card) :=
      ⟨⟨0, Finset.card_pos.mpr hnonempty⟩⟩
    let y : Fin points.card → Fin 2 → ℤ :=
      fun j ↦ (points.equivFin.symm j).1
    have hyP : ∀ j, MvPolynomial.eval (planeCurveFirstChartPoint (y j)) P = 0 := by
      intro j
      simpa only [planeCurveFirstChartPoint, integralAffineChartVector] using
        hPzero (points.equivFin.symm j).1 (points.equivFin.symm j).2
    have hyz : ∀ j i, (p : ℤ) ∣ y j i - center i := by
      intro j i
      exact hsame (points.equivFin.symm j).1 (points.equivFin.symm j).2 i
    let disc : CurveNormalizationResidueDisc
        (Fin 3) (Fin points.card) p
        (affineLineJetWeight (salbergerCurveMonomialCount δ)) hpositive
        (fun j ↦ integralAffineChartVector (points.equivFin.symm j).1) := by
      simpa only [y, planeCurveFirstChartPoint, integralAffineChartVector] using
        planeCurveFirstChartResidueDiscAt p
          (affineLineJetWeight (salbergerCurveMonomialCount δ))
          hpprime hpositive P y center hyP hyz v hpartial
    exact card_curvePacket_le_degree_sq_of_prime_threshold
      hMonomial hBezout hδ hV I hIprime hIhomogeneous hIdegree points
        hIzero hbox hpositive disc hp
  · simp only [Finset.not_nonempty_iff_eq_empty] at hnonempty
    simp [hnonempty]

end
end TranslatedDepthSeven
