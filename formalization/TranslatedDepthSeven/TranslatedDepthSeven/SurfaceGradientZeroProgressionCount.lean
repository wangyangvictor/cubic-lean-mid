import TranslatedDepthSeven.SurfaceProperCutProgressionBoxCount
import TranslatedDepthSeven.HypersurfaceProperDerivative
import TranslatedDepthSeven.ProjectedHypersurfaceDerivativeBridge
import TranslatedDepthSeven.HypersurfaceSurfaceResidueDiscFirstChart
import TranslatedDepthSeven.HomogeneousCone

/-! The actual zero-gradient locus of a fixed hypersurface surface has a
coefficient-uniform linear progression bound. A proper partial derivative
is constructed internally; all curve components and their counts are proved.
The smooth-locus determinant-method amplification is a separate problem. -/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000

/-- The zero projective gradient lies on one actual proper derivative cut.
Its progression-point bound is d(d-1)(2B+1). -/
theorem card_hypersurface_progression_gradientZero_le
    {N d B m : ℕ} (hm : 0 < m)
    (F : MvPolynomial (Fin (N + 1)) ℚ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hprime : (Ideal.span {F}).IsPrime)
    (hdegree : HasProjectiveDimensionDegree (Ideal.span {F}) 2 d)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        affineIdealZeroLocus (Ideal.span {F}))
    (hgrad : ∀ z ∈ S, ∀ i,
      eval (fun j => (progressionHomogeneousPoint u m z j : ℚ)) (pderiv i F) = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * (d - 1) * (2 * B + 1) := by
  obtain ⟨i, _hi, hnot⟩ := exists_proper_partial_of_positive_homogeneous
    F hF hFhom hdegree.2.1
  have hhom : (Ideal.span {F}).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
    apply Ideal.homogeneous_span
    intro G hG
    exact ⟨d, (Set.mem_singleton_iff.mp hG).symm ▸ hFhom⟩
  exact card_surface_progression_properCut_le hm (Ideal.span {F}) hprime hhom hdegree
    (pderiv i F) hFhom.pderiv hnot u S hsource (fun z hz => hgrad z hz i) hbox

/-- On the first chart, zero spatial gradient and the hypersurface equation
force zero full gradient by Euler's identity. -/
theorem card_hypersurface_progression_affineGradientZero_le
    {N d B m : ℕ} (hm : 0 < m)
    (F : MvPolynomial (Fin (N + 1)) ℚ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hprime : (Ideal.span {F}).IsPrime)
    (hdegree : HasProjectiveDimensionDegree (Ideal.span {F}) 2 d)
    (u : Fin N → ℤ) (S : Finset (Fin N → ℤ))
    (hsource : ∀ z ∈ S,
      (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
        affineIdealZeroLocus (Ideal.span {F}))
    (hgrad : ∀ z ∈ S, ∀ i : Fin N,
      eval (fun j => (progressionHomogeneousPoint u m z j : ℚ)) (pderiv i.succ F) = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * (d - 1) * (2 * B + 1) := by
  apply card_hypersurface_progression_gradientZero_le hm F hF hFhom hprime hdegree u S
    hsource _ hbox
  intro z hz i
  by_contra hi
  obtain ⟨j, hj⟩ := exists_nonzero_affine_partial_of_homogeneous_gradient F hFhom
    (fun j => (progressionHomogeneousPoint u m z j : ℚ))
    (by simp [progressionHomogeneousPoint])
    (hsource z hz F (Ideal.subset_span (Set.mem_singleton F))) ⟨i, hi⟩
  exact hj (hgrad z hz j)

/-- The exact integer first-chart convention used by the smooth-prime
reservoir has the same elementary zero-gradient bound. The principal ideal
of the displayed fixed equation is required to be the actual prime surface. -/
theorem card_surface_progression_integerGradientZero_le
    {d B m : ℕ} (hm : 0 < m)
    (F : MvPolynomial (Fin 4) ℤ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hprime : (Ideal.span {map (Int.castRingHom ℚ) F}).IsPrime)
    (hdegree : HasProjectiveDimensionDegree (Ideal.span {map (Int.castRingHom ℚ) F}) 2 d)
    (u : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ))
    (hzero : ∀ z ∈ S, eval (progressionHomogeneousPoint u m z) F = 0)
    (hgrad : ∀ z ∈ S, ∀ i : Fin 3,
      eval (fun j => u j + (m : ℤ) * z j)
        (pderiv i (surfaceHypersurfaceFirstChartDehomogenize F)) = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ B) :
    S.card ≤ d * (d - 1) * (2 * B + 1) := by
  have hFQ : map (Int.castRingHom ℚ) F ≠ 0 := by
    intro hz
    exact hF ((map_injective _ Int.cast_injective) (by simpa only [map_zero] using hz))
  apply card_hypersurface_progression_affineGradientZero_le hm
    (map (Int.castRingHom ℚ) F) hFQ (hFhom.map _) hprime hdegree u S _ _ hbox
  · intro z hz
    have hle : Ideal.span {map (Int.castRingHom ℚ) F} ≤
        RingHom.ker (eval (fun i => (progressionHomogeneousPoint u m z i : ℚ))) := by
      apply Ideal.span_le.mpr
      intro G hG
      obtain rfl := Set.mem_singleton_iff.mp hG
      change eval _ (map (Int.castRingHom ℚ) F) = 0
      rw [eval_map_intCast, hzero z hz, Int.cast_zero]
    intro G hG
    exact hle hG
  · intro z hz i
    rw [pderiv_map, eval_map_intCast]
    suffices he : eval (progressionHomogeneousPoint u m z) (pderiv i.succ F) = 0 by
      rw [he, Int.cast_zero]
    have heq : surfaceHypersurfaceFirstChartDehomogenize F = integralDehomogenizeAtZeroHom F := by
      congr 1
    have he := hgrad z hz i
    rw [heq, eval_pderiv_integralDehomogenizeAtZeroHom] at he
    exact he

end
end TranslatedDepthSeven
