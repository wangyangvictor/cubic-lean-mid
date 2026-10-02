import TranslatedDepthSeven.ProjectedSourceDerivativeHeight
import TranslatedDepthSeven.ThreeCertificateReservoirSelection

/-!
# An explicit common exponent for the projected-surface certificates

The maximum below depends only on the fixed equations, their fixed
denominator and the original degree bound. No relative component model
or smooth-chart catalogue enters it. The projection coefficient bound
affects only the eventual height threshold.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter

theorem eventually_projectedSurface_commonCertificate_bounds
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (denominator : ℤ) (D Cmenu : ℕ) :
    let A : ℕ := max (2 * strictChartCertificateExponent equations denominator)
      (D * (D + 1) ^ 4 + D + 1)
    ∀ᶠ H : ℝ in atTop, ∀ p : Parameters, p.H = H →
      ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ (A : ℝ) ∧
      (∀ (x₀ : IntVector 13) (CF : ℕ)
        (C : IntegralDepthSevenJacobianChartIndex equations),
        ∀ z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C,
          (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
            C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ (A : ℝ) ∧
          (((((p.m : ℤ) * denominator) *
            MvPolynomial.eval (integralAffineMap x₀ z p.m)
              C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ (A : ℝ)) ∧
      (∀ d b Ccoeff : ℕ, d ≤ D → b ≤ Cmenu →
        Ccoeff ≤ (d + 1) ^ 4 * ((d + 1) ^ 4).factorial *
          max 1 (b * max 1 (2 * surfaceTangentNaturalSide p)) ^
            (d * (d + 1) ^ 4) →
        (((d + 1) ^ 4 * d * Ccoeff *
          max 1 (b * max 1 (2 * surfaceTangentNaturalSide p)) ^ d : ℕ) : ℝ) ≤
          H ^ (A : ℝ)) := by
  dsimp only
  let A : ℕ := max (2 * strictChartCertificateExponent equations denominator)
    (D * (D + 1) ^ 4 + D + 1)
  have hdouble : 2 * strictChartCertificateExponent equations denominator ≤ A :=
    Nat.le_max_left _ _
  have hsingle : strictChartCertificateExponent equations denominator ≤ A := by omega
  have hderiv : D * (D + 1) ^ 4 + D + 1 ≤ A := Nat.le_max_right _ _
  filter_upwards [eventually_projectedSourceDerivative_tangentPacket_bound D Cmenu]
    with H hderivative
  intro p hpH
  have hHone : 1 ≤ H := by rw [← hpH]; linarith [p.five_le_H]
  have hmono {a : ℕ} (ha : a ≤ A) : H ^ a ≤ H ^ (A : ℝ) := by
    have hcast : (a : ℝ) ≤ A := by exact_mod_cast ha
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hHone hcast)
  refine ⟨?_, ?_, ?_⟩
  · have hfixed := scale_mul_denominator_natAbs_le_heightPower p equations denominator
    rw [hpH] at hfixed
    exact hfixed.trans (hmono hsingle)
  · intro x₀ CF C z hz
    constructor
    · have hdet := chartDeterminant_natAbs_le_heightPower
        p x₀ equations CF C denominator hz
      rw [hpH] at hdet
      exact hdet.trans (hmono hsingle)
    · have hproduct := scale_denominator_chartDeterminant_product_natAbs_le_heightPower
        p x₀ equations CF C denominator hz
      rw [hpH] at hproduct
      exact hproduct.trans (hmono hdouble)
  · intro d b Ccoeff hd hb hcoeff
    have hbound := hderivative p hpH d b Ccoeff hd hb hcoeff
    apply hbound.trans
    exact Real.rpow_le_rpow_of_exponent_le hHone (by exact_mod_cast hderiv)

end

end TranslatedDepthSeven
