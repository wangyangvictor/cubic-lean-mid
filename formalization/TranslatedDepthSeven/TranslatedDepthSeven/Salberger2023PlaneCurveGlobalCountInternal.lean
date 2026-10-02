import TranslatedDepthSeven.Salberger2023PlaneCurvePrimePackets
import TranslatedDepthSeven.Salberger2023ProjectedBoxThreshold
import TranslatedDepthSeven.ProjectedCurvePolylogHeight
import TranslatedDepthSeven.Salberger2023PolylogCurveCount

/-!
# A uniform high-degree plane-curve count from literal projected data

This composes the proved prime supply, the actual smooth residue packets,
the determinant estimate, and the explicit small-equation height bounds.
The inputs on the finite point set are concrete coordinate and derivative
bounds and a bound on its gradient-zero points.  They are precisely the
properties supplied by the projected small-equation construction.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Filter
open scoped Topology

set_option maxHeartbeats 2000000

/-- The eventual threshold is selected before the varying degree, equation,
and finite set.  There is no local point-count or literature premise. -/
theorem eventually_integralPlaneCurve_count_of_projectedBounds
    (N : ℕ) (Cd ε : ℝ) (hCd : 0 ≤ Cd) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
      ⌈16 / ε⌉₊ < δ →
      (δ : ℝ) ≤ Cd * (1 + Real.log V) → (M : ℝ) ≤ V →
      ∀ P : MvPolynomial (Fin 3) ℤ,
        P.IsHomogeneous δ → Irreducible (P.map (Int.castRingHom ℚ)) →
      ∀ S : Finset (IntVector 2),
        (∀ z ∈ S, eval (integralAffineChartVector z) P = 0) →
        (∀ z ∈ S, ∀ i, (integralAffineChartVector z i).natAbs ≤
          salbergerProjectedCurveBoxRadius N δ M) →
        (∀ z ∈ S,
          (planeCurveDerivativeCertificate (planeCurveFirstChartDehomogenize P) z).natAbs ≤
            projectedCurveDerivativeCertificateBound N δ M) →
        (S.filter (fun z ↦
          planeCurveDerivativeCertificate (planeCurveFirstChartDehomogenize P) z = 0)).card ≤
            δ ^ 2 →
        (S.card : ℝ) ≤ V ^ (ε / 2) := by
  obtain ⟨β, hβ, hβε, _hβdegree, hboxThreshold⟩ :=
    exists_uniform_projectedCurve_boxPrimeExponent N Cd ε hCd hε
  let A := projectedCurvePolylogHeightConstant N Cd
  have hA : 0 ≤ A := (eventually_projectedCurve_polylogHeight N Cd hCd).1
  have hcount := eventually_count_of_polylog_certificates_at_exponent
    A Cd (Cd ^ 2) ε β 5 2 hA hCd (sq_nonneg Cd) hβ hβε
  filter_upwards [hcount, hboxThreshold,
    (eventually_projectedCurve_polylogHeight N Cd hCd).2,
    eventually_ge_atTop (1 : ℝ)] with V hcountV hboxV hheightV hV
  intro δ M hhigh hδ hM P hPhom hPirred S hPzero hbox hDheight hexceptional
  let f := planeCurveFirstChartDehomogenize P
  let D := planeCurveDerivativeCertificate f
  have hδpos : 1 ≤ δ := by omega
  have hlog : 0 ≤ 1 + Real.log V := by
    have := Real.log_nonneg hV
    linarith
  apply hcountV 2 δ hδ S D (planeCurveSmoothResidues f)
  · intro z hz _hD
    have hzbound : ((D z).natAbs : ℝ) ≤
        (projectedCurveDerivativeCertificateBound N δ M : ℝ) := by
      exact_mod_cast hDheight z hz
    exact hzbound.trans (hheightV δ M hδ hM).2
  · have hexceptionalReal : ((S.filter (fun z ↦ D z = 0)).card : ℝ) ≤
        (δ : ℝ) ^ 2 := by exact_mod_cast hexceptional
    calc
      ((S.filter (fun z ↦ D z = 0)).card : ℝ) ≤ (δ : ℝ) ^ 2 := hexceptionalReal
      _ ≤ (Cd * (1 + Real.log V)) ^ 2 := by gcongr
      _ = Cd ^ 2 * (1 + Real.log V) ^ 2 := by ring
  · intro p hp hplow _hphigh
    have hlocalThreshold :
        4 * (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
          (8 / ((δ : ℝ) + 3)) < p :=
      (mul_le_mul_of_nonneg_left (hboxV δ M hhigh hδ hM)
        (by norm_num : (0 : ℝ) ≤ 4)).trans_lt hplow
    exact integralPlaneCurve_primePacket_data hδpos (Nat.le_max_left _ _) hp
      P hPhom hPirred S hPzero hbox hlocalThreshold

end

end TranslatedDepthSeven
