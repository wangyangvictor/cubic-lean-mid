import TranslatedDepthSeven.Salberger2023LocalCurveThreshold

/-! # The half-power prime threshold from the quadratic forbidden block -/

namespace TranslatedDepthSeven
noncomputable section

def quadraticFilteredCurveExponent (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)

theorem affineLineJetWeight_two_mul_add_one (k : ℕ) :
    affineLineJetWeight (2 * k + 1) = k * (2 * k + 1) := by
  have h := two_mul_affineLineJetWeight (2 * k + 1)
  simp only [Nat.add_sub_cancel] at h
  nlinarith

theorem quadraticFilteredCurveExponent_pos (k : ℕ) :
    0 < quadraticFilteredCurveExponent k := by
  unfold quadraticFilteredCurveExponent
  positivity

theorem quadraticFilteredCurveExponent_mul_weight (k : ℕ) :
    quadraticFilteredCurveExponent k *
        affineLineJetWeight (2 * k + 1) = (k * (k + 1) : ℕ) := by
  rw [quadraticFilteredCurveExponent, affineLineJetWeight_two_mul_add_one]
  push_cast
  field_simp

/-- A common column degree works for every exponent strictly larger than
one half; it is independent of the equation and its coefficients. -/
theorem exists_quadraticFilteredCurveExponent_lt
    (β : ℝ) (hβ : (1 : ℝ) / 2 < β) :
    ∃ k : ℕ, 2 ≤ k ∧ quadraticFilteredCurveExponent k < β := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 (1 / (2 * β - 1)))
  have hk2 : (2 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkbig : 1 / (2 * β - 1) < (k : ℝ) :=
    (le_max_right _ _).trans_lt hk
  have hpos : 0 < 2 * β - 1 := by linarith
  have hmul : 1 < (k : ℝ) * (2 * β - 1) := (div_lt_iff₀ hpos).mp hkbig
  refine ⟨k, by exact_mod_cast hk2.le, ?_⟩
  rw [quadraticFilteredCurveExponent, div_lt_iff₀ (by positivity)]
  nlinarith

/-- The exact integer determinant inequality for the weighted block. -/
theorem quadraticFiltered_curve_determinant_size_of_prime_threshold
    {k V p : ℕ} (hk : 1 ≤ k) (hV : 1 ≤ V)
    (hp : 4 * (V : ℝ) ^ quadraticFilteredCurveExponent k < p) :
    (2 * k + 1).factorial * V ^ (k * (k + 1)) <
      p ^ affineLineJetWeight (2 * k + 1) := by
  let s := 2 * k + 1
  let E := affineLineJetWeight s
  let r := quadraticFilteredCurveExponent k
  have hEpos : 0 < E := by
    dsimp only [E, s]
    rw [affineLineJetWeight_two_mul_add_one]
    positivity
  have hfacNat : s.factorial ≤ 4 ^ E :=
    (Nat.factorial_le_pow s).trans
      (self_pow_le_four_pow_affineLineJetWeight s (by dsimp only [s]; omega))
  have hfac : (s.factorial : ℝ) ≤ (4 : ℝ) ^ E := by exact_mod_cast hfacNat
  have hVexp : ((V ^ (k * (k + 1)) : ℕ) : ℝ) =
      (V : ℝ) ^ (r * (E : ℝ)) := by
    rw [show r * (E : ℝ) = (k * (k + 1) : ℕ) from
      quadraticFilteredCurveExponent_mul_weight k]
    simp only [Real.rpow_natCast, Nat.cast_pow]
  have hleft : (((s.factorial * V ^ (k * (k + 1)) : ℕ) : ℝ)) ≤
      (4 : ℝ) ^ E * (V : ℝ) ^ (r * (E : ℝ)) := by
    rw [Nat.cast_mul, hVexp]
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  have hright : (4 : ℝ) ^ E * (V : ℝ) ^ (r * (E : ℝ)) < (p : ℝ) ^ E := by
    have hpow : (4 * (V : ℝ) ^ r) ^ E < (p : ℝ) ^ E :=
      pow_lt_pow_left₀ hp (by positivity) (Nat.ne_zero_of_lt hEpos)
    rw [mul_pow, ← Real.rpow_mul_natCast (show (0 : ℝ) ≤ V by positivity)] at hpow
    exact hpow
  have hreal : (((s.factorial * V ^ (k * (k + 1)) : ℕ) : ℝ)) <
      ((p ^ E : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact hleft.trans_lt hright
  exact_mod_cast hreal

end
end TranslatedDepthSeven
