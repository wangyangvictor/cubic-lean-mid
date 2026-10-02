import TranslatedDepthSeven.Salberger2023LocalCurveThreshold

/-! The fixed homogeneous degree block already suffices for the weak
B^(1+epsilon) primitive plane-curve bound. -/
namespace TranslatedDepthSeven

 theorem planeCurve_jetWeight_ge_degree_mul_count {d : ℕ} (hd : 2 ≤ d) :
    d * salbergerCurveMonomialCount d ≤
      affineLineJetWeight (salbergerCurveMonomialCount d) := by
  let s := salbergerCurveMonomialCount d
  have hs : 2 * s = d * (d + 3) := two_mul_salbergerCurveMonomialCount d
  have hsge : 2 * d + 1 ≤ s := by nlinarith
  have hweight := two_mul_affineLineJetWeight s
  have hsone : 1 ≤ s := by omega
  have hsub : s - 1 + 1 = s := Nat.sub_add_cancel hsone
  nlinarith [Nat.mul_le_mul_left s (show 2 * d ≤ s - 1 by omega)]

/-- A prime exceeding 4B kills the homogeneous evaluation minors in every
degree d>=2; no coefficient-height uniformity is needed here. -/
theorem primitivePlaneCurve_determinant_size_of_linear_threshold
    {d B p : ℕ} (hd : 2 ≤ d) (hB : 1 ≤ B) (hp : 4 * B < p) :
    (salbergerCurveMonomialCount d).factorial *
      B ^ (d * salbergerCurveMonomialCount d) <
        p ^ affineLineJetWeight (salbergerCurveMonomialCount d) := by
  let s := salbergerCurveMonomialCount d
  let E := affineLineJetWeight s
  have hs : 2 ≤ s := salbergerCurveMonomialCount_two_le (by omega)
  have hpos : 0 < E := by
    have h := two_mul_affineLineJetWeight s
    have hsub : 1 ≤ s - 1 := by omega
    have hprod := Nat.mul_le_mul hs hsub
    dsimp only [E]
    omega
  have hfac : s.factorial ≤ 4 ^ E :=
    (Nat.factorial_le_pow s).trans (self_pow_le_four_pow_affineLineJetWeight s (by omega))
  have hexp : d * s ≤ E := planeCurve_jetWeight_ge_degree_mul_count hd
  calc
    s.factorial * B ^ (d * s) ≤ 4 ^ E * B ^ E :=
      Nat.mul_le_mul hfac (Nat.pow_le_pow_right hB hexp)
    _ = (4 * B) ^ E := (Nat.mul_pow 4 B E).symm
    _ < p ^ E := Nat.pow_lt_pow_left hp (Nat.ne_zero_of_lt hpos)

end TranslatedDepthSeven
