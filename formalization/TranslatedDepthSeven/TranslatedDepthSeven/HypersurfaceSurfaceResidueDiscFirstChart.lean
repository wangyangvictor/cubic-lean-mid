import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscCoordinates

/-! The affine hypersurface residue disc in the first homogeneous chart. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

/-- The integral point with homogeneous first coordinate one. -/
def surfaceHypersurfaceFirstChartPoint (y : Fin 3 → ℤ) : Fin 4 → ℤ :=
  Fin.cases 1 y

/-- The literal map `X₀ ↦ 1`, `Xᵢ₊₁ ↦ Xᵢ`. -/
def surfaceHypersurfaceFirstChartDehomogenize :
    MvPolynomial (Fin 4) ℤ →+* MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

theorem surfaceHypersurfaceFirstChart_eval (y : Fin 3 → ℤ)
    (F : MvPolynomial (Fin 4) ℤ) :
    MvPolynomial.eval y (surfaceHypersurfaceFirstChartDehomogenize F) =
      MvPolynomial.eval (surfaceHypersurfaceFirstChartPoint y) F := by
  have h : (MvPolynomial.eval y).comp surfaceHypersurfaceFirstChartDehomogenize =
      MvPolynomial.eval (surfaceHypersurfaceFirstChartPoint y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [surfaceHypersurfaceFirstChartDehomogenize]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [surfaceHypersurfaceFirstChartDehomogenize, surfaceHypersurfaceFirstChartPoint]
  exact RingHom.congr_fun h F

/-- Compose an actual affine disc with dehomogenization.  The resulting
ambient evaluations are exactly those at `(1,y₀,y₁,y₂)`. -/
def surfaceHypersurfaceResidueDiscFirstChart {ι : Type*} {p E : ℕ} {hE : 0 < E}
    {y : ι → Fin 3 → ℤ}
    (d : SurfaceNormalizationResidueDisc (Fin 3) ι p E hE y) :
    SurfaceNormalizationResidueDisc (Fin 4) ι p E hE
      (fun j => surfaceHypersurfaceFirstChartPoint (y j)) where
  Chart := d.Chart
  ambient := d.ambient.comp surfaceHypersurfaceFirstChartDehomogenize
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
      simp [surfaceHypersurfaceFirstChartDehomogenize]
    · intro i
      refine Fin.cases ?_ (fun a => ?_) i <;>
        simp [surfaceHypersurfaceFirstChartDehomogenize, surfaceHypersurfaceFirstChartPoint]

/-- First-chart packets on a literal four-variable hypersurface supply the
`Fin 4` residue discs consumed by the homogeneous auxiliary-form theorem.
The hypersurface polynomial need not be homogeneous for this construction. -/
def surfaceHypersurfaceFirstChartResidueDiscAt {ι : Type*} [Nonempty ι]
    (p E : ℕ) (hp : p.Prime) (hE : 0 < E)
    (F : MvPolynomial (Fin 4) ℤ) (y : ι → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (surfaceHypersurfaceFirstChartPoint (y j)) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 3)
    (hzJ : (MvPolynomial.eval z
      (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    SurfaceNormalizationResidueDisc (Fin 4) ι p E hE
      (fun j => surfaceHypersurfaceFirstChartPoint (y j)) :=
  surfaceHypersurfaceResidueDiscFirstChart
    (surfaceHypersurfaceResidueDiscAt p E hp hE
      (surfaceHypersurfaceFirstChartDehomogenize F) y z
      (fun j => (surfaceHypersurfaceFirstChart_eval (y j) F).trans (hyF j)) hyz v hzJ)

end
end TranslatedDepthSeven
