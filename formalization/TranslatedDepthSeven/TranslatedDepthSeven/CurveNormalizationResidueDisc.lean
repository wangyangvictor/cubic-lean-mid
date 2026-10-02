import TranslatedDepthSeven.FormallyEtaleCurveDeterminant

/-!
# Actual residue discs for a smooth curve chart

This packages the literal ring maps needed for the local curve determinant.
The chart may be localized: its specializations are required only modulo the
prime power, and no map from the chart to `ℤ` is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u v w

/-- A common formally-étale one-parameter residue disc for a finite family
of ambient integral points. -/
structure CurveNormalizationResidueDisc
    (σ : Type u) (ι : Type v) (p E : ℕ) (hE : 0 < E)
    (y : ι → σ → ℤ) where
  Chart : Type w
  [commRing : CommRing Chart]
  [algebra : Algebra UnivariateIntPolynomial Chart]
  [formallyEtale : Algebra.FormallyEtale UnivariateIntPolynomial Chart]
  ambient : MvPolynomial σ ℤ →+* Chart
  center : Fin 1 → ℤ
  parameters : ι → Fin 1 → ℤ
  congruent : ∀ j i, (p : ℤ) ∣ parameters j i - center i
  point : Chart →+* ZMod p
  point_base : point.comp (algebraMap UnivariateIntPolynomial Chart) =
    evalUnivariateIntPolynomialZMod p center
  specialization : ι → Chart →+* ZMod (p ^ E)
  specialization_base : ∀ j,
    (specialization j).comp (algebraMap UnivariateIntPolynomial Chart) =
      evalUnivariateIntPolynomialZMod (p ^ E) (parameters j)
  specialization_reduction : ∀ j,
    (zmodPrimePowerReduction p E hE).comp (specialization j) = point
  specialization_ambient : ∀ j,
    (specialization j).comp ambient =
      MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (p ^ E)))
        (fun i ↦ (y j i : ZMod (p ^ E)))

attribute [instance] CurveNormalizationResidueDisc.commRing
  CurveNormalizationResidueDisc.algebra
  CurveNormalizationResidueDisc.formallyEtale

/-- Restrict a common residue disc to a selected subfamily. -/
def CurveNormalizationResidueDisc.reindex
    {σ : Type u} {ι : Type v} {κ : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → σ → ℤ}
    (disc : CurveNormalizationResidueDisc.{u,v,w} σ ι p E hE y)
    (f : κ → ι) :
    CurveNormalizationResidueDisc σ κ p E hE (fun j ↦ y (f j)) where
  Chart := disc.Chart
  ambient := disc.ambient
  center := disc.center
  parameters j := disc.parameters (f j)
  congruent j := disc.congruent (f j)
  point := disc.point
  point_base := disc.point_base
  specialization j := disc.specialization (f j)
  specialization_base j := disc.specialization_base (f j)
  specialization_reduction j := disc.specialization_reduction (f j)
  specialization_ambient j := disc.specialization_ambient (f j)

/-- The actual modular chart maps imply the exact local determinant
divisibility for arbitrary ambient polynomial evaluations. -/
theorem CurveNormalizationResidueDisc.det_dvd
    {σ : Type u} {ι : Type v} [Fintype ι] [DecidableEq ι]
    (hE : 0 < affineLineJetWeight (Fintype.card ι))
    (p : ℕ) (y : ι → σ → ℤ)
    (disc : CurveNormalizationResidueDisc.{u,v,w} σ ι p
      (affineLineJetWeight (Fintype.card ι)) hE y)
    (F : ι → MvPolynomial σ ℤ) :
    (p : ℤ) ^ affineLineJetWeight (Fintype.card ι) ∣
      (Matrix.of (fun i j ↦ MvPolynomial.eval (y j) (F i))).det := by
  apply formallyEtaleCurveIntegerEvaluations_det_dvd
    hE p disc.center disc.parameters disc.congruent disc.point
    disc.point_base (fun i ↦ disc.ambient (F i)) disc.specialization
    disc.specialization_base disc.specialization_reduction
    (Matrix.of (fun i j ↦ MvPolynomial.eval (y j) (F i)))
  intro i j
  have h := RingHom.congr_fun (disc.specialization_ambient j) (F i)
  change disc.specialization j (disc.ambient (F i)) = _ at h
  rw [h]
  exact MvPolynomial.eval₂_comp
    (Int.castRingHom
      (ZMod (p ^ affineLineJetWeight (Fintype.card ι)))) (y j) (F i)

end

end TranslatedDepthSeven
