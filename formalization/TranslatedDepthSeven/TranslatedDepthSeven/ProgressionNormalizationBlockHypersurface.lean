import TranslatedDepthSeven.ProgressionNormalizationBlockEvaluation
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscFirstChart

/-! Literal polynomial hypotheses supply the local divisibility of the
normalized progression matrix.  No etale chart is an input. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

/-- A nonsingular common reduction of actual points on a four-variable
hypersurface gives the surface determinant exponent. The congruence is
stated in displacement coordinates; the derivative is taken at the actual
unscaled point. -/
theorem progressionNormalizationBlock_det_dvd_of_hypersurface
    {d : ℕ} (hd : 0 < d) (k t s p m : ℕ)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hcard : Fintype.card (Fin d × AffinePlaneMonomialIndex k) = affinePlaneMonomialCount t + s)
    (hE : 0 < affinePlaneMonomialWeight t + (t + 1) * s)
    (L : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : L 0 = X 0)
    (G : Fin d → MvPolynomial (Fin 4) ℤ)
    (F : MvPolynomial (Fin 4) ℤ) (u : Fin 3 → ℤ)
    (y : Fin d × AffinePlaneMonomialIndex k → Fin 3 → ℤ) (z : Fin 3 → ℤ)
    (hyF : ∀ j, MvPolynomial.eval (progressionHomogeneousPoint u m (y j)) F = 0)
    (hyz : ∀ j i, (p : ℤ) ∣ y j i - z i)
    (v : Fin 3)
    (hzJ : (MvPolynomial.eval (fun i => u i + (m : ℤ) * z i)
      (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) : ZMod p) ≠ 0) :
    (p : ℤ) ^ (affinePlaneMonomialWeight t + (t + 1) * s) ∣
      (Matrix.of (fun j i => progressionNormalizationBlockEntry L G u m k (y j) i)).det := by
  letI : Nonempty (Fin d × AffinePlaneMonomialIndex k) :=
    ⟨(⟨0, hd⟩, ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩)⟩
  have hcong : ∀ j i, (p : ℤ) ∣
      (u i + (m : ℤ) * y j i) - (u i + (m : ℤ) * z i) := by
    intro j i
    convert dvd_mul_of_dvd_right (hyz j i) (m : ℤ) using 1 <;> ring
  let disc := surfaceHypersurfaceFirstChartResidueDiscAt p
    (affinePlaneMonomialWeight t + (t + 1) * s) hp hE F
    (fun j i => u i + (m : ℤ) * y j i) (fun i => u i + (m : ℤ) * z i)
    hyF hcong v hzJ
  exact progressionNormalizationBlock_det_dvd_of_residueDisc
    k t s p m hp hpm hcard hE L hL hL0 G u y disc

end
end TranslatedDepthSeven
