import TranslatedDepthSeven.LowRadialProjectiveCount
import TranslatedDepthSeven.ManuscriptReservoirTarget
import TranslatedDepthSeven.PrimitivePowerLaws
import Mathlib.Tactic

/-! # The canonical low-radial cutoff and its final exponent -/

namespace TranslatedDepthSeven

noncomputable section

/-- The integral version of the manuscript cutoff `X = T^(4/13)`. -/
def quotientLowRadialNaturalCutoff (T : ℝ) : ℕ :=
  manuscriptReservoirTarget 1 T (4 / 13)

theorem one_le_quotientLowRadialNaturalCutoff
    {T : ℝ} (hT : 1 ≤ T) :
    1 ≤ quotientLowRadialNaturalCutoff T := by
  have hpow : 1 ≤ T ^ (4 / 13 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hceil := manuscriptReservoirTarget_cast_lower 1 T (4 / 13)
  have hreal : (1 : ℝ) ≤ quotientLowRadialNaturalCutoff T :=
    hpow.trans (by simpa [quotientLowRadialNaturalCutoff] using hceil)
  exact_mod_cast hreal

theorem quotientLowRadialNaturalCutoff_cast_le
    {T : ℝ} (hT : 1 ≤ T) :
    (quotientLowRadialNaturalCutoff T : ℝ) ≤
      2 * T ^ (4 / 13 : ℝ) := by
  calc
    (quotientLowRadialNaturalCutoff T : ℝ) =
        (manuscriptReservoirTarget 1 T (4 / 13) : ℝ) := rfl
    _ ≤ 2 * 1 * T ^ (4 / 13 : ℝ) :=
      manuscriptReservoirTarget_cast_le_two_mul
        (Cres := (1 : ℝ)) (T := T) (a := (4 / 13 : ℝ))
        (by norm_num) hT (by norm_num)
    _ = 2 * T ^ (4 / 13 : ℝ) := by ring

theorem quotientLowRadial_scale_le
    {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) :
    T * (quotientLowRadialNaturalCutoff T : ℝ) ^ ((4 : ℝ) + ε) +
        T ^ 2 * (quotientLowRadialNaturalCutoff T : ℝ) ^ ((3 : ℝ) + ε) ≤
      (2 ^ ((4 : ℝ) + ε) + 2 ^ ((3 : ℝ) + ε)) *
        T ^ ((38 / 13 : ℝ) + ε) := by
  let X : ℝ := quotientLowRadialNaturalCutoff T
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ 2 * T ^ (4 / 13 : ℝ) := by
    simpa only [X] using quotientLowRadialNaturalCutoff_cast_le hT
  have hs4 : 0 ≤ (4 : ℝ) + ε := by linarith
  have hs3 : 0 ≤ (3 : ℝ) + ε := by linarith
  have hpow4 : X ^ ((4 : ℝ) + ε) ≤
      2 ^ ((4 : ℝ) + ε) *
        T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε)) := by
    calc
      X ^ ((4 : ℝ) + ε) ≤
          (2 * T ^ (4 / 13 : ℝ)) ^ ((4 : ℝ) + ε) :=
        Real.rpow_le_rpow hX0 hX hs4
      _ = 2 ^ ((4 : ℝ) + ε) *
          (T ^ (4 / 13 : ℝ)) ^ ((4 : ℝ) + ε) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0 _)]
      _ = 2 ^ ((4 : ℝ) + ε) *
          T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε)) := by
        rw [← Real.rpow_mul hT0]
  have hpow3 : X ^ ((3 : ℝ) + ε) ≤
      2 ^ ((3 : ℝ) + ε) *
        T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε)) := by
    calc
      X ^ ((3 : ℝ) + ε) ≤
          (2 * T ^ (4 / 13 : ℝ)) ^ ((3 : ℝ) + ε) :=
        Real.rpow_le_rpow hX0 hX hs3
      _ = 2 ^ ((3 : ℝ) + ε) *
          (T ^ (4 / 13 : ℝ)) ^ ((3 : ℝ) + ε) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0 _)]
      _ = 2 ^ ((3 : ℝ) + ε) *
          T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε)) := by
        rw [← Real.rpow_mul hT0]
  have hexp4 :
      (1 : ℝ) + (4 / 13 : ℝ) * ((4 : ℝ) + ε) ≤
        (38 / 13 : ℝ) + ε := by nlinarith
  have hexp3 :
      (2 : ℝ) + (4 / 13 : ℝ) * ((3 : ℝ) + ε) ≤
        (38 / 13 : ℝ) + ε := by nlinarith
  have hTpow4 :
      T * T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε)) ≤
        T ^ ((38 / 13 : ℝ) + ε) := by
    calc
      T * T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε)) =
          T ^ ((1 : ℝ) + (4 / 13 : ℝ) * ((4 : ℝ) + ε)) := by
        rw [Real.rpow_add hTpos, Real.rpow_one]
      _ ≤ T ^ ((38 / 13 : ℝ) + ε) :=
        Real.rpow_le_rpow_of_exponent_le hT hexp4
  have hTpow3 :
      T ^ 2 * T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε)) ≤
        T ^ ((38 / 13 : ℝ) + ε) := by
    calc
      T ^ 2 * T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε)) =
          T ^ ((2 : ℝ) + (4 / 13 : ℝ) * ((3 : ℝ) + ε)) := by
        rw [Real.rpow_add hTpos, Real.rpow_two]
      _ ≤ T ^ ((38 / 13 : ℝ) + ε) :=
        Real.rpow_le_rpow_of_exponent_le hT hexp3
  calc
    T * X ^ ((4 : ℝ) + ε) + T ^ 2 * X ^ ((3 : ℝ) + ε) ≤
        T * (2 ^ ((4 : ℝ) + ε) *
          T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε))) +
        T ^ 2 * (2 ^ ((3 : ℝ) + ε) *
          T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε))) := by
      gcongr
    _ = 2 ^ ((4 : ℝ) + ε) *
          (T * T ^ ((4 / 13 : ℝ) * ((4 : ℝ) + ε))) +
        2 ^ ((3 : ℝ) + ε) *
          (T ^ 2 * T ^ ((4 / 13 : ℝ) * ((3 : ℝ) + ε))) := by ring
    _ ≤ 2 ^ ((4 : ℝ) + ε) * T ^ ((38 / 13 : ℝ) + ε) +
        2 ^ ((3 : ℝ) + ε) * T ^ ((38 / 13 : ℝ) + ε) := by
      gcongr
    _ = (2 ^ ((4 : ℝ) + ε) + 2 ^ ((3 : ℝ) + ε)) *
        T ^ ((38 / 13 : ℝ) + ε) := by ring

/-- The manuscript's complete low-radial estimate at the integral cutoff
`ceil(T^(4/13))`.  The constant depends on the fixed projective fourfold and
on `ε`, exactly as in Salberger 2023. -/
theorem finiteProjectiveFourfold_lowRadialCutoff_le_salberger2023
    (hSalberger : Published.Salberger2023Theorem01)
    {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : Published.IsIntegralProjectiveVariety I 4 d)
    (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ S : Finset (Projectivization ℚ (Fin (N + 1) → ℚ)),
        (∀ x ∈ S, ∀ f ∈ I, MvPolynomial.eval x.rep f = 0) →
        (∀ x ∈ S, primitiveRationalVectorHeight x.rep ≤
          quotientLowRadialNaturalCutoff T) →
        (∑ x ∈ S,
            ((1 : ℝ) + T +
              T ^ 2 / primitiveRationalVectorHeight x.rep)) ≤
          C * T ^ ((38 / 13 : ℝ) + ε) := by
  classical
  obtain ⟨C₀, hC₀, hsource⟩ :=
    finiteProjectiveFourfold_radialWeight_le_salberger2023
      hSalberger I hI hd ε hε
  let K : ℝ := 2 ^ ((4 : ℝ) + ε) + 2 ^ ((3 : ℝ) + ε)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨C₀ * K, mul_pos hC₀ hK, ?_⟩
  intro T hT S hvanish hheight
  have hraw := hsource (quotientLowRadialNaturalCutoff T)
    (one_le_quotientLowRadialNaturalCutoff hT) T hT S hvanish hheight
  have hscale := quotientLowRadial_scale_le hT hε
  calc
    (∑ x ∈ S,
        ((1 : ℝ) + T +
          T ^ 2 / primitiveRationalVectorHeight x.rep)) ≤
        C₀ *
          (T * (quotientLowRadialNaturalCutoff T : ℝ) ^ ((4 : ℝ) + ε) +
            T ^ 2 * (quotientLowRadialNaturalCutoff T : ℝ) ^
              ((3 : ℝ) + ε)) := hraw
    _ ≤ C₀ * (K * T ^ ((38 / 13 : ℝ) + ε)) :=
      mul_le_mul_of_nonneg_left (by simpa only [K] using hscale) hC₀.le
    _ = (C₀ * K) * T ^ ((38 / 13 : ℝ) + ε) := by ring

end

end TranslatedDepthSeven
