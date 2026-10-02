import TranslatedDepthSeven.QuadraticFilteredPlaneCurvePrimePackets
import TranslatedDepthSeven.QuadraticFilteredProjectedBoxThreshold
import TranslatedDepthSeven.ProjectedCurvePolylogHeight
import TranslatedDepthSeven.Salberger2023PolylogCurveCount

/-!
# Coefficient-uniform half-power count for bounded-degree plane curves

The fixed degree cap and epsilon select the height threshold before the
equation and finite point set. Small-equation and derivative-certificate
bounds are the literal data furnished by the bounded projection bridge.
No Pila or other integer point-count premise occurs.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Filter
open scoped Topology
set_option maxHeartbeats 2000000

theorem eventually_boundedDegree_integralPlaneCurve_count_of_projectedBounds
    (N D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ V : ℝ in atTop, ∀ δ M : ℕ,
      2 ≤ δ → δ ≤ D → (M : ℝ) ≤ V →
      ∀ P : MvPolynomial (Fin 3) ℤ,
        P.IsHomogeneous δ → Irreducible (P.map (Int.castRingHom ℚ)) →
      ∀ S : Finset (IntVector 2),
        (∀ z ∈ S, eval (integralAffineChartVector z) P = 0) →
        (∀ z ∈ S, ∀ i, (integralAffineChartVector z i).natAbs ≤
          salbergerProjectedCurveBoxRadius N δ M) →
        (∀ z ∈ S,
          (planeCurveDerivativeCertificate (planeCurveFirstChartDehomogenize P) z).natAbs ≤
            projectedCurveDerivativeCertificateBound N δ M) →
        (S.filter (fun z =>
          planeCurveDerivativeCertificate (planeCurveFirstChartDehomogenize P) z = 0)).card ≤
            δ ^ 2 →
        (S.card : ℝ) ≤ V ^ ((1 : ℝ) / 2 + ε) := by
  let β : ℝ := 1 / 2 + ε / 2
  have hβhalf : (1 : ℝ) / 2 < β := by dsimp only [β]; linarith
  obtain ⟨k, hk, hrβ⟩ := exists_quadraticFilteredCurveExponent_lt β hβhalf
  let E : ℕ := max D k
  let A := projectedCurvePolylogHeightConstant N (D : ℝ)
  have hA : 0 ≤ A := (eventually_projectedCurve_polylogHeight N D (by positivity)).1
  have hcount := eventually_count_of_polylog_certificates_at_exponent
    A E ((D : ℝ) ^ 2) (1 + 2 * ε) β 5 0 hA (by positivity) (sq_nonneg _)
      (by linarith) (by dsimp only [β]; linarith)
  have hboxThreshold := eventually_boundedDegree_projectedCurve_boxPower_le
    N D (quadraticFilteredCurveExponent k) β
      (quadraticFilteredCurveExponent_pos k).le hrβ
  filter_upwards [hcount, hboxThreshold,
    (eventually_projectedCurve_polylogHeight N D (by positivity)).2,
    eventually_ge_atTop (1 : ℝ)] with V hcountV hboxV hheightV hV
  intro δ M hδtwo hδD hM P hPhom hPirred S hPzero hbox hDheight hexceptional
  let f := planeCurveFirstChartDehomogenize P
  let certificate := planeCurveDerivativeCertificate f
  have hlog : 1 ≤ 1 + Real.log V := by
    have := Real.log_nonneg hV
    linarith
  have hδlog : (δ : ℝ) ≤ (D : ℝ) * (1 + Real.log V) := by
    exact (show (δ : ℝ) ≤ D by exact_mod_cast hδD).trans
      (le_mul_of_one_le_right (by positivity) hlog)
  have hElog : (E : ℝ) ≤ (E : ℝ) * (1 + Real.log V) :=
    le_mul_of_one_le_right (by positivity) hlog
  have hδE : δ ≤ E := hδD.trans (Nat.le_max_left _ _)
  have hkE : k ≤ E := Nat.le_max_right _ _
  have hbound := hcountV 2 E hElog S certificate (planeCurveSmoothResidues f)
    (by
      intro z hz _hD
      have hzbound : ((certificate z).natAbs : ℝ) ≤
          (projectedCurveDerivativeCertificateBound N δ M : ℝ) := by
        exact_mod_cast hDheight z hz
      exact hzbound.trans (hheightV δ M hδlog hM).2)
    (by
      simp only [pow_zero, mul_one]
      have hbad : ((S.filter (fun z => certificate z = 0)).card : ℝ) ≤ (δ : ℝ) ^ 2 := by
        exact_mod_cast hexceptional
      exact hbad.trans (by gcongr))
    (by
      intro p hp hplow _hphigh
      have hlocalThreshold :
          4 * (salbergerProjectedCurveBoxRadius N δ M : ℝ) ^
            quadraticFilteredCurveExponent k < p :=
        (mul_le_mul_of_nonneg_left (hboxV δ M hδD hM)
          (by norm_num : (0 : ℝ) ≤ 4)).trans_lt hplow
      refine ⟨?_, ?_, ?_⟩
      · intro z hz hcert
        apply residue_mem_planeCurveSmoothResidues_of_certificate f z ?_ hp hcert
        exact (planeCurveFirstChart_eval z P).trans (hPzero z hz)
      · exact (card_planeCurveSmoothResidues_le f hp).trans
          (Nat.mul_le_mul_right p
            (((totalDegree_planeCurveFirstChartDehomogenize_le P).trans
              hPhom.totalDegree_le).trans hδE))
      · intro rho hrho
        exact (card_integralPlaneCurve_smoothResiduePacket_le_degree_mul
          hδtwo hk (Nat.le_max_left _ _) hp P hPhom hPirred S hPzero hbox
          hlocalThreshold rho hrho).trans (by
            calc
              δ * k ≤ E * E := Nat.mul_le_mul hδE hkE
              _ = E ^ 2 := by ring))
  convert hbound using 1 <;> congr 1 <;> ring

end
end TranslatedDepthSeven
