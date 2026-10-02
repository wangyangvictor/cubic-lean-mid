import TranslatedDepthSeven.AllResidueSurfaceDeterminant
import TranslatedDepthSeven.MixedResidueClasses

/-! Retain the determinant contributions of actual smooth discs even when
other columns have no smooth chart. Every discarded column is represented
by its literal constant entries and has zero local jet exponent. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
universe u v w
set_option maxHeartbeats 1000000

/-- No condition is imposed on the discarded integer columns. The exponent
is the sum over the supplied actual good discs alone. -/
theorem mixedSurfaceResidueDiscBlocks_det_dvd
    {σ : Type u} {ι : Type v} {ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (p : ℕ) (good : ι → Prop) [DecidablePred good]
    (label : {j // good j} → ν) (y : ι → σ → ℤ)
    (hE : 0 < ∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c}))
    (disc : ∀ c, SurfaceNormalizationResidueDisc.{u,v,w}
      σ {j : {j // good j} // label j = c} p
      (∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c})) hE
      (fun j => y j.val.val))
    (G : ι → MvPolynomial σ ℤ) :
    (p : ℤ) ^ (∑ c, smoothSurfaceJetExponent (Fintype.card {j // label j = c})) ∣
      (Matrix.of (fun i j => MvPolynomial.eval (y j) (G i))).det := by
  classical
  choose R hR using fun c => (disc c).exists_bivariate_representatives G
  let cls := mixedResidueLabel good label
  let center : ν ⊕ ι → Fin 2 → ℤ := Sum.elim (fun c => (disc c).center) (fun _ => 0)
  let polys : ν ⊕ ι → ι → BivariateIntPolynomial :=
    Sum.elim R (fun j i => MvPolynomial.C (MvPolynomial.eval (y j) (G i)))
  let coord : ι → Fin 2 → ℤ := fun j =>
    if h : good j then (disc (label ⟨j, h⟩)).parameters ⟨⟨j, h⟩, rfl⟩ else 0
  have hsum := sum_mixedResidueLabel_jetExponent good label
  have hdiv := blockBivariateIntegerEvaluations_det_dvd p cls center polys coord
    (A := Matrix.of (fun i j => MvPolynomial.eval (y j) (G i)))
    (by
      intro j i
      by_cases h : good j
      · simpa [coord, center, cls, mixedResidueLabel, h] using
          (disc (label ⟨j, h⟩)).congruent ⟨⟨j, h⟩, rfl⟩ i
      · simp [coord, center, cls, mixedResidueLabel, h])
    (by
      intro i j
      change (MvPolynomial.eval (y j) (G i) :
        ZMod (p ^ (∑ c, smoothSurfaceJetExponent
          (Fintype.card {j // mixedResidueLabel good label j = c})))) = _
      rw [hsum]
      by_cases h : good j
      · simpa [coord, polys, cls, mixedResidueLabel, h] using
          hR (label ⟨j, h⟩) i ⟨⟨j, h⟩, rfl⟩
      · simp [coord, polys, cls, mixedResidueLabel, h])
  simpa only [cls, hsum] using hdiv

end
end TranslatedDepthSeven
