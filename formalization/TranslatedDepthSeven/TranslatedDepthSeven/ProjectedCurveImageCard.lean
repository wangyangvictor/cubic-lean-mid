import TranslatedDepthSeven.ProjectedSourcePacketSmallEquation
import TranslatedDepthSeven.Salberger2023CurveCountNumerics

/-!
# Transfer a plane-image count back to its source curve

The residue and determinant estimates can be applied to the finite set of
distinct projected affine points.  The proved finite-projection fibre bound
then loses at most the curve degree.  A logarithmically growing degree is
absorbed by any fixed positive exponent gap.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published Filter
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Counting distinct plane image points loses at most the source degree
when lifted back through the bounded affine projection. -/
theorem card_source_le_degree_mul_projectedAffineImage_card
    {N r degree : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hprojection : StandardAG.IsAffineChartFiniteBirationalLinearProjection
      (degree := degree) I hI A G)
    (points : Finset (IntVector N))
    (hsource : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval
        (fun j ↦ (integralAffineChartVector z j : ℚ)) f = 0) :
    points.card ≤ degree * (points.image (projectedSourceAffineTail A)).card := by
  classical
  apply Finset.card_le_mul_card_image
  intro target _htarget
  have hfull : points.filter (fun z ↦ projectedSourceAffineTail A z = target) =
      points.filter (fun z ↦ integralAffineChartProjection A z =
        integralAffineProjectivePoint target) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hz, heq⟩
      refine ⟨hz, ?_⟩
      rw [← integralAffineProjectivePoint_projectedSourceAffineTail A hprojection.1,
        heq]
    · rintro ⟨hz, heq⟩
      refine ⟨hz, ?_⟩
      funext i
      exact congrFun heq i.succ
  rw [hfull]
  apply integralAffineChartProjection_fibre_card_le_degree I hI A G hprojection
  intro z hz f hf
  exact RingHom.mem_ker.mpr (hsource z hz f hf)

/-- Uniform absorption of the finite projection fibre loss, with no fixed
curve-degree hypothesis. -/
theorem eventually_count_le_rpow_of_projectedImage_count
    (Cd a b : ℝ) (hCd : 0 ≤ Cd) (hab : a < b) :
    ∀ᶠ V : ℝ in atTop, ∀ δ sourceCount imageCount : ℕ,
      (δ : ℝ) ≤ Cd * (1 + Real.log V) →
      sourceCount ≤ δ * imageCount →
      (imageCount : ℝ) ≤ V ^ a →
      (sourceCount : ℝ) ≤ V ^ b := by
  filter_upwards [eventually_polylog_mul_rpow_le_rpow Cd a b 1 hCd hab,
    eventually_ge_atTop (1 : ℝ)] with V habsorb hV
  intro δ sourceCount imageCount hδ hsource himage
  have hlog : 0 ≤ Real.log V := Real.log_nonneg hV
  have hsourceReal : (sourceCount : ℝ) ≤ (δ : ℝ) * imageCount := by
    exact_mod_cast hsource
  calc
    (sourceCount : ℝ) ≤ (δ : ℝ) * imageCount := hsourceReal
    _ ≤ (Cd * (1 + Real.log V)) * V ^ a :=
      mul_le_mul hδ himage (by positivity)
        (by positivity)
    _ ≤ V ^ b := by simpa only [pow_one] using habsorb

end

end TranslatedDepthSeven
