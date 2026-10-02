import TranslatedDepthSeven.PlaneCurveResidueDisc

/-! The literal plane-curve residue disc in the first homogeneous chart. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

/-- The projective point `[1,y₀,y₁]` attached to an affine plane point. -/
def planeCurveFirstChartPoint (y : Fin 2 → ℤ) : Fin 3 → ℤ :=
  Fin.cases 1 y

/-- The literal map `X₀ ↦ 1`, `Xᵢ₊₁ ↦ Xᵢ`. -/
def planeCurveFirstChartDehomogenize :
    MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

theorem planeCurveFirstChart_eval (y : Fin 2 → ℤ)
    (F : MvPolynomial (Fin 3) ℤ) :
    MvPolynomial.eval y (planeCurveFirstChartDehomogenize F) =
      MvPolynomial.eval (planeCurveFirstChartPoint y) F := by
  have h : (MvPolynomial.eval y).comp planeCurveFirstChartDehomogenize =
      MvPolynomial.eval (planeCurveFirstChartPoint y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [planeCurveFirstChartDehomogenize]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;>
        simp [planeCurveFirstChartDehomogenize, planeCurveFirstChartPoint]
  exact RingHom.congr_fun h F

/-- Compose an affine curve disc with first-chart dehomogenization. -/
def planeCurveResidueDiscFirstChart {ι : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → Fin 2 → ℤ}
    (d : CurveNormalizationResidueDisc (Fin 2) ι p E hE y) :
    CurveNormalizationResidueDisc (Fin 3) ι p E hE
      (fun j ↦ planeCurveFirstChartPoint (y j)) where
  Chart := d.Chart
  ambient := d.ambient.comp planeCurveFirstChartDehomogenize
  center := d.center
  parameters := d.parameters
  congruent := d.congruent
  point := d.point
  point_base := d.point_base
  specialization := d.specialization
  specialization_base := d.specialization_base
  specialization_reduction := d.specialization_reduction
  specialization_ambient j := by
    rw [← RingHom.comp_assoc, d.specialization_ambient]
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [planeCurveFirstChartDehomogenize]
    · intro i
      refine Fin.cases ?_ (fun a ↦ ?_) i <;>
        simp [planeCurveFirstChartDehomogenize, planeCurveFirstChartPoint]

/-- A nonzero affine partial of a homogeneous plane-curve equation produces
the `Fin 3` residue disc used by the projective auxiliary-form argument. -/
def planeCurveFirstChartResidueDiscAt {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : MvPolynomial (Fin 3) ℤ) (y : ι → Fin 2 → ℤ) (z : Fin 2 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (planeCurveFirstChartPoint (y j)) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 2)
    (hzJ : (MvPolynomial.eval z
      (MvPolynomial.pderiv v (planeCurveFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    CurveNormalizationResidueDisc (Fin 3) ι p E hE
      (fun j ↦ planeCurveFirstChartPoint (y j)) :=
  planeCurveResidueDiscFirstChart
    (planeCurveResidueDiscAt p E hp hE
      (planeCurveFirstChartDehomogenize F) y z
      (fun j ↦ (planeCurveFirstChart_eval (y j) F).trans (hyF j)) hyz v hzJ)

end
end TranslatedDepthSeven
