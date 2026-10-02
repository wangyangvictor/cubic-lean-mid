import TranslatedDepthSeven.PrimitivePowerLaws

/-!
# The canonical line power calculation

There are no geometric or aggregate hypotheses in this file.  We define the
four power-law factors which occur after those estimates have been proved and
derive their exponents directly from

`q = T^(5/7)`, `U = T/q`, and `X = U^(1/3)`.

Consequently this file isolates exactly what remains to be shown about the
actual counting functions: domination by these canonical factors, up to the
uniform constants and epsilon powers supplied by the geometric argument.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Exponents appearing in the two explicit line majorants.  These are
definitions, not assumed estimates. -/
def lineOccurrenceExponent : ℝ := 30 / 7
def highDirectionFactorExponent : ℝ := 4 / 21
def starPerDirectionExponent : ℝ := 4
def lowDirectionCountExponent : ℝ := 10 / 21
def sharpLineExponent : ℝ := 94 / 21

theorem highDirectionExponent_eq :
    lineOccurrenceExponent + highDirectionFactorExponent = sharpLineExponent := by
  norm_num [lineOccurrenceExponent, highDirectionFactorExponent, sharpLineExponent]

theorem lowDirectionExponent_eq :
    starPerDirectionExponent + lowDirectionCountExponent = sharpLineExponent := by
  norm_num [starPerDirectionExponent, lowDirectionCountExponent, sharpLineExponent]

/-- The split `X = T^(2/21)` balances the two displayed line powers. -/
theorem lineSplit_balances :
    lineOccurrenceExponent + (2 / 7 : ℝ) - (2 / 21 : ℝ) =
        sharpLineExponent ∧
      starPerDirectionExponent + 5 * (2 / 21 : ℝ) =
        sharpLineExponent := by
  norm_num [lineOccurrenceExponent, starPerDirectionExponent, sharpLineExponent]

/-- The maximum of the two affine functions of a possible splitting exponent
is minimized at `2/21`, with value `94/21`. -/
theorem lineSplit_optimal (theta : ℝ) :
    sharpLineExponent ≤ max
      (lineOccurrenceExponent + (2 / 7 : ℝ) - theta)
      (starPerDirectionExponent + 5 * theta) := by
  by_cases htheta : theta ≤ (2 / 21 : ℝ)
  · apply le_trans _ (le_max_left _ _)
    have h := lineSplit_balances.1
    dsimp only [lineOccurrenceExponent, starPerDirectionExponent,
      sharpLineExponent] at htheta h ⊢
    linarith
  · apply le_trans _ (le_max_right _ _)
    have h := lineSplit_balances.2
    dsimp only [lineOccurrenceExponent, starPerDirectionExponent,
      sharpLineExponent] at htheta h ⊢
    linarith

/-- The canonical six-dimensional residue-class mass `q^6`. -/
def primitiveOccurrenceMass : CountFunction := fun _ T ↦ (qScale T) ^ (6 : ℝ)

/-- The canonical tagged-line factor `1+U/X`. -/
def primitiveTaggedHighFactor : CountFunction := fun _ T ↦
  1 + uScale T / xScale T

/-- The worst star contribution for one low direction. -/
def primitiveStarPerDirection : CountFunction := fun _ T ↦ (T ^ (1 : ℝ)) ^ (4 : ℝ)

/-- The canonical number `X^5` of low directions. -/
def primitiveLowDirectionCount : CountFunction := fun _ T ↦
  (xScale T) ^ (5 : ℝ)

/-- The sum of the canonical high- and low-direction majorants. -/
def primitiveLineMajorant : CountFunction := fun H T ↦
  primitiveOccurrenceMass H T * primitiveTaggedHighFactor H T +
    primitiveStarPerDirection H T * primitiveLowDirectionCount H T

theorem primitiveOccurrenceMass_bound :
    UniformPowerBound primitiveOccurrenceMass lineOccurrenceExponent := by
  have h := ScalePowerLaw.toUniformPowerBound (by norm_num)
    (scaleFunction_scalePowerLaw (5 / 7 : ℝ) 6 (by norm_num))
  change UniformPowerBound (fun _ T ↦ (T ^ (5 / 7 : ℝ)) ^ (6 : ℝ)) _
  have hexponent : (5 / 7 : ℝ) * 6 = lineOccurrenceExponent := by
    norm_num [lineOccurrenceExponent]
  rwa [hexponent] at h

theorem primitiveStarPerDirection_bound :
    UniformPowerBound primitiveStarPerDirection starPerDirectionExponent := by
  have h := ScalePowerLaw.toUniformPowerBound (by norm_num)
    (scaleFunction_scalePowerLaw (1 : ℝ) 4 (by norm_num))
  change UniformPowerBound (fun _ T ↦ (T ^ (1 : ℝ)) ^ (4 : ℝ)) _
  have hexponent : (1 : ℝ) * 4 = starPerDirectionExponent := by
    norm_num [starPerDirectionExponent]
  rwa [hexponent] at h

theorem primitiveLowDirectionCount_bound :
    UniformPowerBound primitiveLowDirectionCount lowDirectionCountExponent := by
  have h := ScalePowerLaw.toUniformPowerBound (by norm_num)
    (scaleFunction_scalePowerLaw (2 / 21 : ℝ) 5 (by norm_num))
  change UniformPowerBound (fun _ T ↦ (T ^ (2 / 21 : ℝ)) ^ (5 : ℝ)) _
  have hexponent : (2 / 21 : ℝ) * 5 = lowDirectionCountExponent := by
    norm_num [lowDirectionCountExponent]
  rwa [hexponent] at h

theorem primitiveTaggedHighFactor_bound :
    UniformPowerBound primitiveTaggedHighFactor highDirectionFactorExponent := by
  intro ε hε
  refine ⟨2, ?_⟩
  intro H T hH hT hTH
  have hratio : uScale T / xScale T = T ^ highDirectionFactorExponent := by
    simpa [highDirectionFactorExponent] using uScale_div_xScale hT
  have honeRatio : 1 ≤ T ^ highDirectionFactorExponent :=
    NNReal.one_le_rpow hT (by norm_num [highDirectionFactorExponent])
  have hHpow : 1 ≤ H ^ ε := NNReal.one_le_rpow hH hε.le
  have hTpow : T ^ highDirectionFactorExponent ≤
      T ^ (highDirectionFactorExponent + ε) :=
    NNReal.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    primitiveTaggedHighFactor H T = 1 + T ^ highDirectionFactorExponent := by
      simp only [primitiveTaggedHighFactor]
      rw [hratio]
    _ ≤ 2 * T ^ highDirectionFactorExponent := by
      rw [two_mul]
      exact add_le_add_left honeRatio _
    _ ≤ 2 * (H ^ ε * T ^ (highDirectionFactorExponent + ε)) := by
      gcongr
      exact le_trans hTpow (le_mul_of_one_le_left' hHpow)
    _ = powerEnvelope 2 H T highDirectionFactorExponent ε := by
      simp only [powerEnvelope]
      ring

/-- The canonical line majorant has the sharp exponent `94/21`. -/
theorem primitiveLineMajorant_bound :
    UniformPowerBound primitiveLineMajorant sharpLineExponent := by
  have hHigh : UniformPowerBound
      (fun H T ↦ primitiveOccurrenceMass H T * primitiveTaggedHighFactor H T)
      (lineOccurrenceExponent + highDirectionFactorExponent) :=
    primitiveOccurrenceMass_bound.mul primitiveTaggedHighFactor_bound
  have hLow : UniformPowerBound
      (fun H T ↦ primitiveStarPerDirection H T * primitiveLowDirectionCount H T)
      (starPerDirectionExponent + lowDirectionCountExponent) :=
    primitiveStarPerDirection_bound.mul primitiveLowDirectionCount_bound
  rw [highDirectionExponent_eq] at hHigh
  rw [lowDirectionExponent_eq] at hLow
  exact hHigh.add hLow

end

end TranslatedDepthSeven
