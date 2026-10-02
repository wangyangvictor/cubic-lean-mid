import TranslatedDepthSeven.ProjectedSurfaceCertificateExponent
import TranslatedDepthSeven.FixedConstantModulusReservoir

/-!
# The common modulus family for the projected-surface proof

The prime pool and its product cardinality are fixed from the displayed
equations, denominator and degree bound, before epsilon. This theorem
supplies both the original chart certificates and every bounded-projection
image derivative on that same family. It uses no relative component or
smooth-chart model.
-/

namespace TranslatedDepthSeven

noncomputable section

open Filter

set_option maxHeartbeats 6000000

theorem eventually_exists_projectedSurface_canonicalReservoir
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (denominator : ℤ) (D Cmenu : ℕ) (b : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    let A : ℝ := (max (2 * strictChartCertificateExponent equations denominator)
      (D * (D + 1) ^ 4 + D + 1) : ℕ)
    let M₀ : ℝ := 2 * manuscriptPoolDepthCoefficient A (5 / 7) + 1
    ∀ᶠ H : ℝ in atTop, ∀ p : Parameters, p.H = H →
      ∃ (P : Finset ℕ) (k : ℕ) (hP : ∀ s ∈ P, s.Prime),
        P = manuscriptPrimePoolAt A (5 / 7) H ∧
        k = manuscriptCrossingAt A (5 / 7)
          normalizedSurfaceReservoirConstant H p.T ∧
        2 * k ≤ reservoirDepth M₀ H ∧
        reservoirSubpowerThreshold M₀ b δ ≤ H ∧
        (∀ q : ReservoirModulus P k,
          Squarefree q.1 ∧
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ q.1 ∧
          (q.1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
            p.T ^ (5 / 7 : ℝ) * H ^ δ) ∧
        ((((modulusReservoir P k).card +
          (modulusReservoirDirectedEdges P k hP).card : ℕ) : ℝ) ≤
            2 * H ^ δ) ∧
        (∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hP).Adj q r →
          manuscriptReservoirTarget normalizedSurfaceReservoirConstant
            p.T (5 / 7) ≤ Nat.lcm q.1 r.1 ∧
          (Nat.lcm q.1 r.1 : ℝ) ≤ normalizedSurfaceReservoirConstant *
            p.T ^ (5 / 7 : ℝ) * H ^ δ) ∧
        (∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
          (E₁.natAbs : ℝ) ≤ H ^ A → (E₂.natAbs : ℝ) ≤ H ^ A →
          Nonempty (ReservoirModulus (certificateAllowedPrimesTwo P E₁ E₂) k) ∧
          (modulusReservoirGraph (certificateAllowedPrimesTwo P E₁ E₂) k
            (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) ∧
        ((((p.m : ℤ) * denominator).natAbs : ℕ) : ℝ) ≤ H ^ A ∧
        (∀ (x₀ : IntVector 13) (CF : ℕ)
          (C : IntegralDepthSevenJacobianChartIndex equations),
          ∀ z ∈ depthSevenNormalizedJacobianChartCell p x₀ equations CF C,
            (((MvPolynomial.eval (integralAffineMap x₀ z p.m)
              C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A ∧
            (((((p.m : ℤ) * denominator) *
              MvPolynomial.eval (integralAffineMap x₀ z p.m)
                C.determinant).natAbs : ℕ) : ℝ) ≤ H ^ A) ∧
        (∀ d mass Ccoeff : ℕ, d ≤ D → mass ≤ Cmenu →
          Ccoeff ≤ (d + 1) ^ 4 * ((d + 1) ^ 4).factorial *
            max 1 (mass * max 1 (2 * surfaceTangentNaturalSide p)) ^
              (d * (d + 1) ^ 4) →
          (((d + 1) ^ 4 * d * Ccoeff *
            max 1 (mass * max 1 (2 * surfaceTangentNaturalSide p)) ^ d : ℕ) : ℝ) ≤
            H ^ A) := by
  let A : ℝ := (max (2 * strictChartCertificateExponent equations denominator)
    (D * (D + 1) ^ 4 + D + 1) : ℕ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hCres : (1 : ℝ) < normalizedSurfaceReservoirConstant := by
    norm_num [normalizedSurfaceReservoirConstant, tangentReservoirConstant,
      tangentCoordinateConstant, Nat.factorial]
  have hreservoir := eventually_exists_fixedConstant_modulusReservoir
    (A := A) (a := (5 / 7 : ℝ))
    (Cres := normalizedSurfaceReservoirConstant)
    hA (by norm_num) (by norm_num) hCres b hδ
  filter_upwards [hreservoir,
    eventually_projectedSurface_commonCertificate_bounds equations denominator D Cmenu]
      with H hfamily hcertificates
  intro p hpH
  have hTH : p.T ≤ H := by simpa only [← hpH] using p.T_le_H
  obtain ⟨P, k, hP, hPcanonical, hkcanonical, _hPcard, _hPinterval,
    _hkP, hkDepth, hthreshold, hmoduli, _hconnected, hmass, hlcm,
    _hcertOne, hcertTwo⟩ := hfamily p.T p.one_le_T hTH
  obtain ⟨hfixed, hchart, hderivative⟩ := hcertificates p hpH
  refine ⟨P, k, hP, hPcanonical, hkcanonical, hkDepth, hthreshold,
    hmoduli, hmass, hlcm, ?_, hfixed, hchart, hderivative⟩
  intro E₁ E₂ hE₁ hE₂ hsize₁ hsize₂
  exact (hcertTwo E₁ E₂ hE₁ hE₂ hsize₁ hsize₂).2

end

end TranslatedDepthSeven
