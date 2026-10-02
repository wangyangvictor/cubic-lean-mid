import CubicTenVariables.FixedLeadingSurfaceLineFamilyCount
import CubicTenVariables.FixedLeadingCurveProjectiveCount

/-!
# Uniform line contribution from the fixed leading curve

Heath--Brown's explicit primitive plane-curve count is the sole numerical
literature premise in this endpoint. The constant precedes the varying
surface equation, its leading scalar, the line family and the box. All
direction incidence and multiplicity arguments are proved internally.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLinesFromCurveCount

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceParallelLineTransport FixedLeadingSurfaceDirectionMultiplicity
open FixedLeadingSurfaceLineDirectionSumNumerical
open scoped BigOperators

theorem exists_uniform_line_contribution
    (curveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k₀ : MvPolynomial (Fin 3) ℤ)
    (hk₀ : k₀.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k₀))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k₀ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
        (points : ι → Finset (IntVector 3)) (base v : ι → IntVector 3)
        (hp : ∀ l, PrimitiveDirection (v l)),
      Function.Injective (fun l =>
        affineLine (rationalVector (base l)) (rationalVector (v l))) →
      (∀ l, linePolynomial g (base l) (v l) = 0) →
      ∀ B : ℕ, 1 ≤ B →
      (∀ l, ∀ x ∈ points l, ∃ t : ℚ, ∀ i,
        ((x i - base l i : ℤ) : ℚ) = t * (v l i : ℚ)) →
      (∀ l, ∀ x ∈ points l, ∀ i, |x i| ≤ (B : ℤ)) →
      (∑ l, ((points l).card : ℝ)) ≤ (Fintype.card ι : ℝ) + A * (B : ℝ) ^ (1 + ε) := by
  obtain ⟨C₀, hC₀, hcurve⟩ :=
    FixedLeadingCurveProjectiveCount.exists_fixed_projective_curve_half_epsilon_bound
      curveCount hd k₀ hk₀ hirr ε hε
  let A := 4 * (d ^ 2 : ℕ) * C₀ * (1 + pSeriesConstant (ε / 2)) * (2 : ℝ) ^ ε
  have hA : 0 < A := by
    have hp := pSeriesConstant_nonneg (ε / 2)
    have hdpos : 0 < d := by omega
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop ι _ _ points base v hp hdistinct hcontained B hB hline hbox
  exact FixedLeadingSurfaceLineFamilyCount.line_points_sum_le_of_fixed_leading_form
    hd g k₀ hk₀ hirr hc hdegree htop points base v hp hdistinct hcontained
    B C₀ ε hB hC₀.le hε hline hbox hcurve

end CubicTenVariables.FixedLeadingSurfaceLinesFromCurveCount
