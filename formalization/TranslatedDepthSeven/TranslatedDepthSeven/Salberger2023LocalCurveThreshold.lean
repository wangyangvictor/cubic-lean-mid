import TranslatedDepthSeven.Salberger2023LocalCurvePacket

/-!
# The numerical threshold in Salberger's local curve estimate

This file discharges the elementary inequality which turns
`p > 4 V^(8/(δ+3))` into the determinant-size inequality used by
`card_curvePacket_le_degree_sq_of_residue_disc`.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators
open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

universe w

private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

theorem self_pow_le_four_pow_affineLineJetWeight
    (s : ℕ) (hs : 1 ≤ s) :
    s ^ s ≤ 4 ^ affineLineJetWeight s := by
  have hsTwo : s ≤ 2 ^ (s - 1) := by
    have h := succ_le_two_pow (s - 1)
    simpa [Nat.sub_add_cancel hs] using h
  calc
    s ^ s ≤ (2 ^ (s - 1)) ^ s := Nat.pow_le_pow_left hsTwo s
    _ = 2 ^ ((s - 1) * s) := by rw [pow_mul]
    _ = 2 ^ (2 * affineLineJetWeight s) := by
      rw [two_mul_affineLineJetWeight]
      rw [Nat.mul_comm (s - 1) s]
    _ = 4 ^ affineLineJetWeight s := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

theorem two_mul_salbergerCurveMonomialCount (δ : ℕ) :
    2 * salbergerCurveMonomialCount δ = δ * (δ + 3) := by
  rcases δ.even_or_odd' with ⟨k, hk | hk⟩
  · subst δ
    simp only [salbergerCurveMonomialCount]
    have hrewrite : (2 * k) * (2 * k + 3) =
        2 * (k * (2 * k + 3)) := by ring
    rw [hrewrite, Nat.mul_div_cancel_left _ (by omega)]
  · subst δ
    simp only [salbergerCurveMonomialCount]
    have hrewrite : (2 * k + 1) * (2 * k + 1 + 3) =
        2 * ((2 * k + 1) * (k + 2)) := by ring
    rw [hrewrite, Nat.mul_div_cancel_left _ (by omega)]

theorem salbergerCurveMonomialCount_two_le
    {δ : ℕ} (hδ : 1 ≤ δ) :
    2 ≤ salbergerCurveMonomialCount δ := by
  have hfour : 4 ≤ δ * (δ + 3) := by
    have hright : 4 ≤ δ + 3 := by omega
    simpa using Nat.mul_le_mul hδ hright
  have htwo := two_mul_salbergerCurveMonomialCount δ
  omega

theorem salberger_curve_exponent_comparison
    {δ : ℕ} (hδ : 1 ≤ δ) :
    (δ : ℝ) * salbergerCurveMonomialCount δ ≤
      (8 / ((δ : ℝ) + 3)) *
        affineLineJetWeight (salbergerCurveMonomialCount δ) := by
  let s := salbergerCurveMonomialCount δ
  let A := affineLineJetWeight s
  have hs : 2 ≤ s := salbergerCurveMonomialCount_two_le hδ
  have hsEqNat : 2 * s = δ * (δ + 3) :=
    two_mul_salbergerCurveMonomialCount δ
  have hAEqNat : 2 * A = s * (s - 1) :=
    two_mul_affineLineJetWeight s
  have hsEq : (2 : ℝ) * s = (δ : ℝ) * ((δ : ℝ) + 3) := by
    exact_mod_cast hsEqNat
  have hAEq : (2 : ℝ) * A = (s : ℝ) * ((s : ℝ) - 1) := by
    calc
      (2 : ℝ) * A = ((2 * A : ℕ) : ℝ) := by norm_num
      _ = ((s * (s - 1) : ℕ) : ℝ) := by rw [hAEqNat]
      _ = (s : ℝ) * ((s : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]
        norm_num
  have hden : (0 : ℝ) < (δ : ℝ) + 3 := by positivity
  change (δ : ℝ) * (s : ℝ) ≤ (8 / ((δ : ℝ) + 3)) * (A : ℝ)
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [show (0 : ℝ) ≤ s by positivity,
    show (2 : ℝ) ≤ s by exact_mod_cast hs]

/-- Salberger's displayed prime threshold implies the exact integer
determinant-size inequality. -/
theorem salberger_curve_determinant_size_of_prime_threshold
    {δ V p : ℕ} (hδ : 1 ≤ δ) (hV : 1 ≤ V)
    (hp : 4 * (V : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p) :
    (salbergerCurveMonomialCount δ).factorial *
        V ^ (δ * salbergerCurveMonomialCount δ) <
      p ^ affineLineJetWeight (salbergerCurveMonomialCount δ) := by
  let s := salbergerCurveMonomialCount δ
  let A := affineLineJetWeight s
  let r : ℝ := 8 / ((δ : ℝ) + 3)
  have hs : 2 ≤ s := salbergerCurveMonomialCount_two_le hδ
  have hAeq : 2 * A = s * (s - 1) := two_mul_affineLineJetWeight s
  have hsSub : 1 ≤ s - 1 := by omega
  have hprod : 2 ≤ s * (s - 1) := by
    simpa using Nat.mul_le_mul hs hsSub
  have hApos : 0 < A := by omega
  have hself : s ^ s ≤ 4 ^ A :=
    self_pow_le_four_pow_affineLineJetWeight s (by omega)
  have hfacNat : s.factorial ≤ 4 ^ A :=
    (Nat.factorial_le_pow s).trans hself
  have hfac : (s.factorial : ℝ) ≤ (4 : ℝ) ^ A := by
    exact_mod_cast hfacNat
  have hVreal : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hexponent : (δ : ℝ) * (s : ℝ) ≤ r * (A : ℝ) := by
    simpa only [s, A, r] using salberger_curve_exponent_comparison hδ
  have hVexp : ((V ^ (δ * s) : ℕ) : ℝ) ≤
      (V : ℝ) ^ (r * (A : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hVreal (by
      simpa only [Nat.cast_mul] using hexponent)
  have hleft :
      (((s.factorial * V ^ (δ * s) : ℕ) : ℝ)) ≤
        (4 : ℝ) ^ A * (V : ℝ) ^ (r * (A : ℝ)) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hfac hVexp (by positivity) (by positivity)
  have hbase : 0 ≤ 4 * (V : ℝ) ^ r := by positivity
  have hright :
      (4 : ℝ) ^ A * (V : ℝ) ^ (r * (A : ℝ)) <
        (p : ℝ) ^ A := by
    have hpow : (4 * (V : ℝ) ^ r) ^ A < (p : ℝ) ^ A :=
      pow_lt_pow_left₀ hp hbase (Nat.ne_zero_of_lt hApos)
    rw [mul_pow, ← Real.rpow_mul_natCast (show (0 : ℝ) ≤ V by positivity)] at hpow
    exact hpow
  have hreal :
      (((s.factorial * V ^ (δ * s) : ℕ) : ℝ)) <
        ((p ^ A : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact hleft.trans_lt hright
  exact_mod_cast hreal

/-- Salberger 2023, equation (3.14), with the published threshold in its
literal form.  The formally-étale disc is the concrete realization of the
single nonsingular special-fiber residue class. -/
theorem card_curvePacket_le_degree_sq_of_prime_threshold
    (hMonomial : StandardAG.RationalProjectiveCurveDegreeMonomialBlock)
    (hBezout : StandardAG.RationalProjectiveCurveAuxiliaryFirstChartBezout)
    {N δ p V : ℕ} (hδ : 1 ≤ δ) (hV : 1 ≤ V)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhomogeneous : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIdegree : HasProjectiveDimensionDegree I 1 δ)
    (points : Finset (IntVector N))
    (hIzero : ∀ z ∈ points, ∀ f ∈ I,
      MvPolynomial.eval (rationalIntegralAffineChartPoint z) f = 0)
    (hbox : ∀ z ∈ points, ∀ i,
      (integralAffineChartVector z i).natAbs ≤ V)
    (hpositive : 0 <
      affineLineJetWeight (salbergerCurveMonomialCount δ))
    (disc : CurveNormalizationResidueDisc.{0,0,w}
      (Fin (N + 1)) (Fin points.card) p
      (affineLineJetWeight (salbergerCurveMonomialCount δ)) hpositive
      (fun j ↦ integralAffineChartVector (points.equivFin.symm j).1))
    (hp : 4 * (V : ℝ) ^ (8 / ((δ : ℝ) + 3)) < p) :
    points.card ≤ δ ^ 2 := by
  apply card_curvePacket_le_degree_sq_of_residue_disc
    hMonomial hBezout I hIprime hIhomogeneous hIdegree points hIzero
      hbox hpositive disc
  exact salberger_curve_determinant_size_of_prime_threshold hδ hV hp

end

end TranslatedDepthSeven
