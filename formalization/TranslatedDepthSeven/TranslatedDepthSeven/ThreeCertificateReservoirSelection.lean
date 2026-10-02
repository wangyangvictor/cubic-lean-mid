import TranslatedDepthSeven.CertificateDeletedReservoirPartition
import TranslatedDepthSeven.StrictChartReservoirBridge

/-!
# Selecting a modulus avoiding a third certificate

The manuscript reservoir permits the deletion of the prime divisors of two
integers.  In the persistent-surface term the first two existing
certificates may be multiplied together, leaving the second slot for the
local multiplicity-one certificate.  This file records that elementary
repackaging with all three coprimality conclusions displayed literally.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- A nonempty subreservoir obtained by deleting the prime divisors of
`D₁ * D₂` and `D₃` supplies an ambient reservoir modulus avoiding each of
`D₁`, `D₂`, and `D₃` separately. -/
theorem exists_reservoirModulus_avoiding_three_certificates
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    (D₁ D₂ D₃ : ℤ)
    (hnonempty : Nonempty (ReservoirModulus
      (certificateAllowedPrimesTwo P (D₁ * D₂) D₃) k)) :
    ∃ q : ReservoirModulus P k,
      survivesTwoCertificates q D₁ D₂ ∧
      Nat.Coprime q.1 D₃.natAbs := by
  obtain ⟨q⟩ := hnonempty
  let q' : ReservoirModulus P k :=
    certificateAllowedTwoModulusEmbedding hP (D₁ * D₂) D₃ q
  have hsurvives : survivesTwoCertificates q' (D₁ * D₂) D₃ :=
    certificateAllowedTwoModulusEmbedding_survives
      hP (D₁ * D₂) D₃ q
  refine ⟨q', ?_, hsurvives.2⟩
  exact (coprime_two_natAbs_iff_coprime_mul q'.1 D₁ D₂).mpr
    hsurvives.1

/-- Height-qualified form using exactly the two-certificate conclusion of
the manuscript reservoir.  No three-certificate reservoir theorem is being
assumed: the first two integers are replaced by their product before the
published two-slot conclusion is invoked. -/
theorem exists_reservoirModulus_avoiding_three_certificates_of_bounds
    {P : Finset ℕ} {k : ℕ} (hP : ∀ p ∈ P, p.Prime)
    {H A : ℝ}
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo P E₁ E₂) k))
    (D₁ D₂ D₃ : ℤ)
    (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0) (hD₃ : D₃ ≠ 0)
    (hD₁D₂size : (((D₁ * D₂).natAbs : ℕ) : ℝ) ≤ H ^ A)
    (hD₃size : (D₃.natAbs : ℝ) ≤ H ^ A) :
    ∃ q : ReservoirModulus P k,
      survivesTwoCertificates q D₁ D₂ ∧
      Nat.Coprime q.1 D₃.natAbs := by
  apply exists_reservoirModulus_avoiding_three_certificates hP D₁ D₂ D₃
  exact hsurvival (D₁ * D₂) D₃ (mul_ne_zero hD₁ hD₂) hD₃
    hD₁D₂size hD₃size

/-- The product of the fixed scale/denominator certificate and the selected
chart determinant has twice the elementary chart-certificate exponent.
This is the product placed in the first deletion slot in the persistent
surface argument. -/
theorem scale_denominator_chartDeterminant_product_natAbs_le_heightPower
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C) :
    (((((p.m : ℤ) * denominator) *
      MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs : ℕ) : ℝ) ≤
      p.H ^ (2 * strictChartCertificateExponent equations denominator) := by
  let A := strictChartCertificateExponent equations denominator
  have hfixed := scale_mul_denominator_natAbs_le_heightPower
    p equations denominator
  have hdet := chartDeterminant_natAbs_le_heightPower
    p x₀ equations CF C denominator hz
  rw [Int.natAbs_mul]
  norm_num only [Nat.cast_mul]
  calc
    (((p.m : ℤ) * denominator).natAbs : ℝ) *
        ((MvPolynomial.eval (integralAffineMap x₀ z p.m)
          C.determinant).natAbs : ℝ) ≤ p.H ^ A * p.H ^ A :=
      mul_le_mul hfixed hdet (Nat.cast_nonneg _)
        (pow_nonneg p.H_pos.le _)
    _ = p.H ^ (2 * A) := by
      rw [← pow_add]
      congr 1
      omega

/-- The same product bound at any larger real reservoir exponent. -/
theorem scale_denominator_chartDeterminant_product_natAbs_le_rpow
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) {z : IntVector 13}
    (hz : z ∈ depthSevenNormalizedJacobianChartCell
      p x₀ equations CF C)
    {A : ℝ}
    (hA : ((2 * strictChartCertificateExponent
      equations denominator : ℕ) : ℝ) ≤ A) :
    (((((p.m : ℤ) * denominator) *
      MvPolynomial.eval (integralAffineMap x₀ z p.m)
        C.determinant).natAbs : ℕ) : ℝ) ≤ p.H ^ A := by
  have hbase :=
    scale_denominator_chartDeterminant_product_natAbs_le_heightPower
      p x₀ equations CF C denominator hz
  apply hbase.trans
  simpa only [Real.rpow_natCast] using
    (Real.rpow_le_rpow_of_exponent_le
      (by linarith [p.five_le_H]) hA)

end

end TranslatedDepthSeven
