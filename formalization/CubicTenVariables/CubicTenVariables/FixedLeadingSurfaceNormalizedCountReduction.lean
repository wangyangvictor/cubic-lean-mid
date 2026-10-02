import CubicTenVariables.FixedLeadingSurfaceCoordinateBoxCount
import CubicTenVariables.FixedLeadingSurfaceCoefficientReduction

/-!
# Reduction to normalized regular points of bounded coefficient height

The remaining counting hypothesis is stated for literal integer points on
the actual normalized homogeneous equation, with a nonzero integer partial
of its actual first affine chart. The coordinate choice and all constants
precede the varying equation. Inverse integral coordinate transport, the
proved singular-point bound and the proved coefficient-height reduction
give the exact existing fixed-leading surface-count endpoint.

This is a reduction theorem: the normalized regular counting proposition
is an explicit argument and is not asserted or added as an axiom.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceNormalizedCountReduction

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedPrimeCount FixedLeadingSurfaceCoordinateBoxCount
open FixedLeadingSurfaceCoefficientReduction FixedLeadingSurfaceSingularCount
open FixedLeadingSurfaceHeightAlternative FixedLeadingSurfaceHeightAlternativeChart
open FixedLeadingFormGoodSurfaceCountReduction

/-- A literal normalized nonsingular-point count. The coefficient bound
is on the original g, before the fixed coordinate substitution. Every
coordinate and constant is chosen before g, its leading scalar and H. -/
def NormalizedRegularPolynomialHeightCount (d : ℕ) (ε : ℝ) : Prop :=
  ∀ k : MvPolynomial (Fin 3) ℤ,
    k.IsHomogeneous d → IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k) →
    ∃ (a b : ℤ) (C₀ : ℝ) (H₀ : ℕ), 0 < C₀ ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
      map (Int.castRingHom ℚ) (homogeneousComponent d g) =
        C c * map (Int.castRingHom ℚ) k →
      ∀ H : ℕ, max H₀ 1 ≤ H →
      mvPolynomialCoefficientNatAbsMax g ≤ H ^ heightExponent d →
      ∀ S : Finset (IntVector 3),
      (∀ z ∈ S, eval (progressionHomogeneousPoint 0 1 z)
        (projectiveEquiv a b (homogenize d g)) = 0) →
      (∀ z ∈ S, ∃ i : Fin 3, eval z (pderiv i
        (surfaceHypersurfaceFirstChartDehomogenize
          (projectiveEquiv a b (homogenize d g)))) ≠ 0) →
      (∀ z ∈ S, ∀ i, (z i).natAbs ≤ H) →
      (S.card : ℝ) ≤ C₀ * (H : ℝ) ^ (1 + ε)

/-- The actual fixed-leading surface-count endpoint follows from one
normalized regular-point estimate. All coordinate and singular-point
losses are absorbed into constants chosen before the varying equation. -/
theorem fixedIntegralLeadingSurfaceBounds_of_normalized_regular_polynomial_height_count
    {d : ℕ} (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε)
    (hnormalized : NormalizedRegularPolynomialHeightCount d ε) :
    FixedIntegralLeadingSurfaceBounds d ε := by
  classical
  apply fixedIntegralLeadingSurfaceBounds_of_polynomial_height_count hd ε hε
  intro k hk hirr
  obtain ⟨a, b, C₀, H₀, hC₀, hcount⟩ := hnormalized k hk hirr
  let K : ℕ := 1 + a.natAbs + b.natAbs
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKcast : (K : ℝ) = boxFactor a b := by
    simp [K, boxFactor]
  let C₁ : ℝ := (3 * (d : ℝ) ^ 2 + C₀) * (K : ℝ) ^ (1 + ε)
  have hC₁ : 0 < C₁ := by
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hKpos _)
  refine ⟨C₁, H₀, hC₁, ?_⟩
  intro g c hc hdegree htop H hH hcoefficient S hzero hbox
  have hH1 : 1 ≤ H := (le_max_left 1 (heightThreshold d)).trans
    ((le_max_right H₀ _).trans hH)
  have hHH₀ : H₀ ≤ H := (le_max_left _ _).trans hH
  let R : ℕ := K * H
  have hHR : H ≤ R := by
    simpa only [R, one_mul] using Nat.mul_le_mul_right H hK
  have hR1 : 1 ≤ R := hH1.trans hHR
  have hRthreshold : max H₀ 1 ≤ R := max_le (hHH₀.trans hHR) hR1
  have hcoefficientR : mvPolynomialCoefficientNatAbsMax g ≤ R ^ heightExponent d :=
    hcoefficient.trans (Nat.pow_le_pow_left hHR _)
  let T := S.image (coordinatePointEquiv a b).symm
  let F := projectiveEquiv a b (homogenize d g)
  let chart := surfaceHypersurfaceFirstChartDehomogenize F
  have hTcard : T.card = S.card :=
    Finset.card_image_of_injective _ (coordinatePointEquiv a b).symm.injective
  have hTbox : ∀ z ∈ T, ∀ i, (z i).natAbs ≤ R := by
    intro z hz i
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxR : ∀ j, |(x j : ℝ)| ≤ (H : ℝ) := by
      intro j
      have hh : ((x j).natAbs : ℝ) ≤ (H : ℝ) := Nat.cast_le.mpr (hbox x hx j)
      simpa using hh
    have hh := inverse_coordinate_mem_box a b x (H : ℝ) (Nat.cast_nonneg _) hxR i
    rw [← hKcast] at hh
    have hh' : (((coordinatePointEquiv a b).symm x i).natAbs : ℝ) ≤ (R : ℝ) := by
      simpa [R] using hh
    exact_mod_cast hh'
  have hpoint (z : IntVector 3) : progressionHomogeneousPoint 0 1 z = Fin.cases 1 z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [TranslatedDepthSeven.progressionHomogeneousPoint]
  have hTzero : ∀ z ∈ T, eval (progressionHomogeneousPoint 0 1 z) F = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [hpoint, ← eval_standardDehomogenizationHom]
    change eval ((coordinatePointEquiv a b).symm x)
      (surfaceHypersurfaceFirstChartDehomogenize F) = 0
    rw [firstChart_transformed_homogenize a b g hdegree,
      eval_coordinateEquiv, ← coordinatePointEquiv_eq_mulVec, Equiv.apply_symm_apply]
    exact hzero x hx
  let singular := T.filter fun z => ∀ i : Fin 3, eval z (pderiv i chart) = 0
  let regular := T.filter fun z => ∃ i : Fin 3, eval z (pderiv i chart) ≠ 0
  have hsingular : singular.card ≤ d * (d - 1) * (2 * R + 1) := by
    apply card_normalized_progression_gradientZero_le hd (by decide : 0 < 1)
      k g c hirr hc hdegree htop a b 0 singular
      (fun z hz => hTzero z (Finset.mem_filter.mp hz).1) _
      (fun z hz => hTbox z (Finset.mem_filter.mp hz).1)
    intro z hz i
    simpa only [chart, F, Pi.zero_apply, Nat.cast_one, one_mul, zero_add] using
      (Finset.mem_filter.mp hz).2 i
  have hregular : (regular.card : ℝ) ≤ C₀ * (R : ℝ) ^ (1 + ε) :=
    hcount g c hc hdegree htop R hRthreshold hcoefficientR regular
      (fun z hz => hTzero z (Finset.mem_filter.mp hz).1)
      (fun _ hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hTbox z (Finset.mem_filter.mp hz).1)
  have hpartition : singular.card + regular.card = S.card := by
    have hh : singular.card + regular.card = T.card := by
      simpa only [singular, regular, not_forall] using
        T.filter_card_add_filter_neg_card_eq_card (fun z =>
          ∀ i : Fin 3, eval z (pderiv i chart) = 0)
    exact hh.trans hTcard
  have hRreal : 1 ≤ (R : ℝ) := by exact_mod_cast hR1
  have hRpower : (R : ℝ) ≤ (R : ℝ) ^ (1 + ε) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hRreal
      (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hsingularLinear : (singular.card : ℝ) ≤ 3 * (d : ℝ) ^ 2 * R := by
    have hh : singular.card ≤ d * d * (2 * R + 1) :=
      hsingular.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d (Nat.sub_le d 1)))
    have hhR : (singular.card : ℝ) ≤ (d : ℝ) * d * (2 * R + 1) := by
      exact_mod_cast hh
    nlinarith [sq_nonneg (d : ℝ)]
  have hsingularPower : (singular.card : ℝ) ≤
      (3 * (d : ℝ) ^ 2) * (R : ℝ) ^ (1 + ε) :=
    hsingularLinear.trans (mul_le_mul_of_nonneg_left hRpower (by positivity))
  calc
    (S.card : ℝ) = (singular.card : ℝ) + (regular.card : ℝ) := by
      exact_mod_cast hpartition.symm
    _ ≤ (3 * (d : ℝ) ^ 2) * (R : ℝ) ^ (1 + ε) +
        C₀ * (R : ℝ) ^ (1 + ε) := add_le_add hsingularPower hregular
    _ = C₁ * (H : ℝ) ^ (1 + ε) := by
      dsimp only [C₁, R]
      rw [Nat.cast_mul, Real.mul_rpow hKpos.le (Nat.cast_nonneg H)]
      ring

end CubicTenVariables.FixedLeadingSurfaceNormalizedCountReduction
