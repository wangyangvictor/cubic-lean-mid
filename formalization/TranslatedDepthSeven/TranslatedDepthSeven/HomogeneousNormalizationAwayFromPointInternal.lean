import TranslatedDepthSeven.HomogeneousLinearElimination

/-!
# Linear normalization whose parameters vanish at an exterior point

An equation of the homogeneous ideal that does not vanish at `[1:c]`
makes the quotient finite over the linear forms `X_i-c_i X_0`.  Normalizing
the kernel of this map and composing retains the vanishing of every
parameter at that point.  No projective projection or degree theorem is
assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

universe u

variable {K : Type u} [Field K] [Infinite K]

/-- Full homogeneous linear normalization can be chosen with all its
parameter forms vanishing at a displayed point outside the projective
zero set. -/
theorem exists_homogeneousLinearNormalization_vanishing_at_affinePoint
    {n : ℕ} (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Fin n)) K))
    (c : Fin n → K)
    (hexterior : ∃ f ∈ I, eval (affineChartVector c) f ≠ 0) :
    ∃ D : HomogeneousLinearNormalizationData I,
      ∀ i, eval (affineChartVector c) (D.forms i) = 0 := by
  classical
  obtain ⟨f₀, hf₀I, hf₀eval⟩ := hexterior
  have hex : ∃ j ∈ Finset.range (f₀.totalDegree + 1),
      eval (affineChartVector c) (homogeneousComponent j f₀) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf₀eval
    rw [← f₀.sum_homogeneousComponent, map_sum]
    exact Finset.sum_eq_zero h
  obtain ⟨j, _hj, hjeval⟩ := hex
  let f := homogeneousComponent j f₀
  have hfI : f ∈ I := by
    have h := hIhom j hf₀I
    change (MvPolynomial.decomposition.decompose' f₀ j :
      MvPolynomial (Option (Fin n)) K) ∈ I at h
    simpa only [MvPolynomial.decomposition.decompose'_apply] using h
  have hfhom : f.IsHomogeneous j := homogeneousComponent_isHomogeneous j f₀
  let h := homogeneousLinearEliminationHom c I
  let l := homogeneousLinearEliminationForm c
  have hh : h = (Ideal.Quotient.mkₐ K I).comp (aeval l) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h, l, homogeneousLinearEliminationHom_X,
      homogeneousLinearEliminationForm]
  have hhfinite : h.Finite :=
    finite_homogeneousLinearEliminationHom_of_eval_ne_zero I f j hfI hfhom c hjeval
  let P : Ideal (MvPolynomial (Fin n) K) := RingHom.ker h
  have hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) K) :=
    kernel_homogeneousLinearEliminationHom_isHomogeneous c I hIhom
  letI : I.IsPrime := hIprime
  have hPprime : P.IsPrime := RingHom.ker_isPrime h
  obtain ⟨D⟩ := exists_homogeneousLinearNormalizationData n P hPprime hPhom
  have hl : ∀ i, (l i).IsHomogeneous 1 :=
    homogeneousLinearEliminationForm_isHomogeneous c
  let DI : HomogeneousLinearNormalizationData I :=
    { parameterCount := D.parameterCount
      forms := fun i ↦ aeval l (D.forms i)
      forms_isHomogeneous := fun i ↦ by
        simpa using (D.forms_isHomogeneous i).aeval l hl
      injective := by
        rw [← kerLift_comp_normalizationHom I l h hh D.parameterCount D.forms]
        exact (Ideal.kerLiftAlg_injective h).comp D.injective
      finite := by
        rw [← kerLift_comp_normalizationHom I l h hh D.parameterCount D.forms]
        exact AlgHom.Finite.comp (kerLiftAlg_finite_of_finite h hhfinite) D.finite }
  refine ⟨DI, ?_⟩
  intro i
  have hlezero : ∀ j, eval (affineChartVector c) (l j) = 0 := by
    intro j
    simp [l, homogeneousLinearEliminationForm, affineChartVector]
  have hcompose :
      (aeval (affineChartVector c)).comp (aeval l) =
        aeval (0 : Fin n → K) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change eval (affineChartVector c) (l j) = 0
    exact hlezero j
  have hzero : coeff 0 (D.forms i) = 0 := by
    by_contra hne
    have h := D.forms_isHomogeneous i hne
    simpa using h
  change eval (affineChartVector c) (aeval l (D.forms i)) = 0
  have heval := DFunLike.congr_fun hcompose (D.forms i)
  simpa [MvPolynomial.aeval_eq_eval, MvPolynomial.constantCoeff_eq, hzero] using heval

end

end TranslatedDepthSeven
