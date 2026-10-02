import TranslatedDepthSeven.IsolatedVertexQuotientPersistentPila
import TranslatedDepthSeven.AffineChartProjectionMenu

/-!
# Literal rational data for a stable geometric curve

The actual nonempty finite set supplies the affine-chart condition.  Galois
descent, preservation of Hilbert degree, and descent of its point equations
are proved internally.  No curve-count estimate is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

/-- Descend the geometric curve and all actual integral points, retaining
the exact ideal equality and the same dimension and degree. -/
theorem exists_rationalCurveData_of_stableQbar
    {N δ : ℕ} (Q : Ideal (MvPolynomial (Fin (N + 1)) Qbar))
    (hQprime : Q.IsPrime)
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) Qbar))
    (hQdegree : HasProjectiveDimensionDegree Q 1 δ)
    (hstable : ∀ g : Qbar ≃ₐ[ℚ] Qbar, conjugateIdeal g Q = Q)
    (S : Finset (IntVector N)) (hS : S.Nonempty)
    (hzero : ∀ z ∈ S, ∀ f ∈ Q,
      eval (fun i ↦ (integralAffineChartVector z i : Qbar)) f = 0) :
    ∃ I : Ideal (MvPolynomial (Fin (N + 1)) ℚ),
      I.IsPrime ∧
      I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
      HasProjectiveDimensionDegree I 1 δ ∧
      X (0 : Fin (N + 1)) ∉ I ∧
      I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = Q ∧
      ∀ z ∈ S, ∀ f ∈ I,
        eval (fun i ↦ (integralAffineChartVector z i : ℚ)) f = 0 := by
  obtain ⟨I, hIhom, hIQ⟩ :=
    rationalHomogeneousIdeal_descent_of_galoisInvariant Q hstable hQhom
  have hIQprime : (I.map (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime := by
    rwa [hIQ]
  have hIprime := rationalIdeal_isPrime_of_qbarCoefficientExtension_isPrime I hIQprime
  have hIdegree := rationalHasProjectiveDimensionDegree_of_qbar_map_eq
    I Q hIQ hQprime hQdegree
  have hmem (f : MvPolynomial (Fin (N + 1)) ℚ) (hf : f ∈ I) :
      MvPolynomial.map (algebraMap ℚ Qbar) f ∈ Q := by
    rw [← hIQ]
    exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap ℚ Qbar)) hf
  have hIX : X (0 : Fin (N + 1)) ∉ I := by
    intro hX
    obtain ⟨z, hz⟩ := hS
    have hzeroX := hzero z hz (X 0) (by simpa using hmem (X 0) hX)
    simpa using hzeroX
  refine ⟨I, hIprime, hIhom, hIdegree, hIX, hIQ, ?_⟩
  intro z hz f hf
  apply (map_eq_zero_iff (algebraMap ℚ Qbar) (algebraMap ℚ Qbar).injective).mp
  calc
    algebraMap ℚ Qbar (eval (fun i ↦ (integralAffineChartVector z i : ℚ)) f) =
        eval (fun i ↦ (integralAffineChartVector z i : Qbar))
          (MvPolynomial.map (algebraMap ℚ Qbar) f) := by
      simpa only [Function.comp_def, map_intCast] using
        (MvPolynomial.map_eval (algebraMap ℚ Qbar)
          (fun i ↦ (integralAffineChartVector z i : ℚ)) f)
    _ = 0 := hzero z hz _ (hmem f hf)

end

end TranslatedDepthSeven
