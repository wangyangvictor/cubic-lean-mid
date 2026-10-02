import TranslatedDepthSeven.PrimitiveLineLedger

/-!
# Canonical terminal branch powers

This file contains no geometric hypotheses.  It records the power factors
which remain after the geometric and counting arguments have supplied their
pointwise inequalities, and derives every terminal exponent from those
factors.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The seven exponents in the displayed terminal sum.  They are numerical
definitions, not hypotheses about a counting function. -/
def targetExponent : ℝ := 94 / 21
def weakerExponent : ℝ := 449 / 100
def properExponent : ℝ := 4
def positiveVertexExponent : ℝ := 2
def curvePlaneExponent : ℝ := 31 / 7
def lineExponent : ℝ := 94 / 21
def isolatedVertexExponent : ℝ := 58 / 13
def isolatedVertexLowExponent : ℝ := 38 / 13
def zeroRecordExponent : ℝ := 30 / 7

theorem everyBranchExponent_le_target :
    properExponent ≤ targetExponent ∧
      positiveVertexExponent ≤ targetExponent ∧
      curvePlaneExponent ≤ targetExponent ∧
      lineExponent ≤ targetExponent ∧
      isolatedVertexExponent ≤ targetExponent ∧
      isolatedVertexLowExponent ≤ targetExponent ∧
      zeroRecordExponent ≤ targetExponent := by
  norm_num [properExponent, positiveVertexExponent, curvePlaneExponent,
    lineExponent, isolatedVertexExponent, isolatedVertexLowExponent,
    zeroRecordExponent, targetExponent]

/-- The exact saving delivered by the numerical ledger. -/
theorem halfNine_sub_targetExponent :
    (9 / 2 : ℝ) - targetExponent = 1 / 42 := by
  norm_num [targetExponent]

theorem targetExponent_lt_weaker : targetExponent < weakerExponent := by
  norm_num [targetExponent, weakerExponent]

/-- Pila's square-root factor `U^(1/2)` for a nonlinear curve. -/
def primitiveNonlinearPerObject : CountFunction := scaleFactor (2 / 7) (1 / 2)

/-- Occurrence mass times the nonlinear-curve factor. -/
def primitiveNonlinearCurveMajorant : CountFunction := fun H T ↦
  primitiveOccurrenceMass H T * primitiveNonlinearPerObject H T

/-- A smooth star contributes `T^3` points. -/
def primitiveSmoothStar : CountFunction := scaleFactor 1 3

/-- There are canonically `U^5` possible smooth directions. -/
def primitiveSmoothDirectionCount : CountFunction := scaleFactor (2 / 7) 5

/-- The smooth rank-two-plane contribution. -/
def primitiveSmoothPlaneMajorant : CountFunction := fun H T ↦
  primitiveSmoothStar H T * primitiveSmoothDirectionCount H T

/-- The proper/singular contribution `T^4`. -/
def primitiveProperMajorant : CountFunction := scaleFactor 1 4

/-- The sum of nonlinear curves, smooth rank-two planes, and singular planes. -/
def primitiveCurvePlaneMajorant : CountFunction := fun H T ↦
  primitiveNonlinearCurveMajorant H T + primitiveSmoothPlaneMajorant H T +
    primitiveProperMajorant H T

/-- A positive-dimensional projective vertex leaves a two-dimensional cone. -/
def primitivePositiveVertexMajorant : CountFunction := scaleFactor 1 2

/-- Quotient packets have `q_0^5`, with `q_0=T^(9/13)`. -/
def primitiveQuotientOccurrence : CountFunction := scaleFactor (9 / 13) 5

/-- Lifting one quotient point along the vertex costs `T`. -/
def primitiveVertexLift : CountFunction := scaleFactor 1 1

/-- Nonradial and high-radial isolated-vertex contribution. -/
def primitiveIsolatedVertexMajorant : CountFunction := fun H T ↦
  primitiveQuotientOccurrence H T * primitiveVertexLift H T

/-- Low radial directions of height at most `T^(4/13)`, counted without a
reciprocal height weight. -/
def primitiveLowRadialDirections : CountFunction := scaleFactor (4 / 13) 4

/-- Their reciprocal-height mass. -/
def primitiveLowRadialReciprocalMass : CountFunction := scaleFactor (4 / 13) 3

/-- The two low-radial terms `T X^4 + T^2 X^3`. -/
def primitiveIsolatedVertexLowMajorant : CountFunction := fun H T ↦
  scaleFactor 1 1 H T * primitiveLowRadialDirections H T +
    scaleFactor 1 2 H T * primitiveLowRadialReciprocalMass H T

/-- Zero-dimensional records cost only the surface occurrence mass. -/
def primitiveZeroRecordMajorant : CountFunction := primitiveOccurrenceMass

theorem primitiveNonlinearPerObject_bound :
    UniformPowerBound primitiveNonlinearPerObject (1 / 7) := by
  simpa only [primitiveNonlinearPerObject] using
    scaleFactor_bound_of_mul_eq (s := (2 / 7 : ℝ)) (r := (1 / 2 : ℝ))
      (a := (1 / 7 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem primitiveNonlinearCurveMajorant_bound :
    UniformPowerBound primitiveNonlinearCurveMajorant curvePlaneExponent := by
  change UniformPowerBound
    (fun H T ↦ primitiveOccurrenceMass H T * primitiveNonlinearPerObject H T) _
  exact UniformPowerBound.mul_of_add_eq
    (by norm_num [lineOccurrenceExponent, curvePlaneExponent])
    primitiveOccurrenceMass_bound primitiveNonlinearPerObject_bound

theorem primitiveSmoothStar_bound :
    UniformPowerBound primitiveSmoothStar 3 := by
  simpa only [primitiveSmoothStar] using
    scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (3 : ℝ)) (a := (3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)

theorem primitiveSmoothDirectionCount_bound :
    UniformPowerBound primitiveSmoothDirectionCount (10 / 7) := by
  simpa only [primitiveSmoothDirectionCount] using
    scaleFactor_bound_of_mul_eq (s := (2 / 7 : ℝ)) (r := (5 : ℝ))
      (a := (10 / 7 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem primitiveSmoothPlaneMajorant_bound :
    UniformPowerBound primitiveSmoothPlaneMajorant curvePlaneExponent := by
  change UniformPowerBound
    (fun H T ↦ primitiveSmoothStar H T * primitiveSmoothDirectionCount H T) _
  exact UniformPowerBound.mul_of_add_eq (by norm_num [curvePlaneExponent])
    primitiveSmoothStar_bound primitiveSmoothDirectionCount_bound

theorem primitiveProperMajorant_bound :
    UniformPowerBound primitiveProperMajorant properExponent := by
  simpa only [primitiveProperMajorant] using
    scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (4 : ℝ))
      (a := properExponent) (by norm_num) (by norm_num)
      (by norm_num [properExponent])

theorem primitiveCurvePlaneMajorant_bound :
    UniformPowerBound primitiveCurvePlaneMajorant curvePlaneExponent := by
  have hProper : UniformPowerBound primitiveProperMajorant curvePlaneExponent :=
    primitiveProperMajorant_bound.weaken
      (by norm_num [properExponent, curvePlaneExponent])
  change UniformPowerBound
    (fun H T ↦ primitiveNonlinearCurveMajorant H T +
      primitiveSmoothPlaneMajorant H T + primitiveProperMajorant H T) _
  exact (primitiveNonlinearCurveMajorant_bound.add
    primitiveSmoothPlaneMajorant_bound).add hProper

theorem primitivePositiveVertexMajorant_bound :
    UniformPowerBound primitivePositiveVertexMajorant positiveVertexExponent := by
  simpa only [primitivePositiveVertexMajorant] using
    scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (2 : ℝ))
      (a := positiveVertexExponent) (by norm_num) (by norm_num)
      (by norm_num [positiveVertexExponent])

theorem primitiveQuotientOccurrence_bound :
    UniformPowerBound primitiveQuotientOccurrence (45 / 13) := by
  simpa only [primitiveQuotientOccurrence] using
    scaleFactor_bound_of_mul_eq (s := (9 / 13 : ℝ)) (r := (5 : ℝ))
      (a := (45 / 13 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem primitiveVertexLift_bound : UniformPowerBound primitiveVertexLift 1 := by
  simpa only [primitiveVertexLift] using
    scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (1 : ℝ)) (a := (1 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)

theorem primitiveIsolatedVertexMajorant_bound :
    UniformPowerBound primitiveIsolatedVertexMajorant isolatedVertexExponent := by
  change UniformPowerBound
    (fun H T ↦ primitiveQuotientOccurrence H T * primitiveVertexLift H T) _
  exact UniformPowerBound.mul_of_add_eq (by norm_num [isolatedVertexExponent])
    primitiveQuotientOccurrence_bound primitiveVertexLift_bound

theorem primitiveLowRadialDirections_bound :
    UniformPowerBound primitiveLowRadialDirections (16 / 13) := by
  simpa only [primitiveLowRadialDirections] using
    scaleFactor_bound_of_mul_eq (s := (4 / 13 : ℝ)) (r := (4 : ℝ))
      (a := (16 / 13 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem primitiveLowRadialReciprocalMass_bound :
    UniformPowerBound primitiveLowRadialReciprocalMass (12 / 13) := by
  simpa only [primitiveLowRadialReciprocalMass] using
    scaleFactor_bound_of_mul_eq (s := (4 / 13 : ℝ)) (r := (3 : ℝ))
      (a := (12 / 13 : ℝ)) (by norm_num) (by norm_num) (by norm_num)

theorem primitiveIsolatedVertexLowMajorant_bound :
    UniformPowerBound primitiveIsolatedVertexLowMajorant isolatedVertexLowExponent := by
  have hT := scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (1 : ℝ))
    (a := (1 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hT2 := scaleFactor_bound_of_mul_eq (s := (1 : ℝ)) (r := (2 : ℝ))
    (a := (2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hFirst0 := UniformPowerBound.mul_of_add_eq
    (show (1 : ℝ) + 16 / 13 = 29 / 13 by norm_num)
    hT primitiveLowRadialDirections_bound
  have hFirst' : UniformPowerBound
      (fun H T ↦ scaleFactor 1 1 H T * primitiveLowRadialDirections H T)
      isolatedVertexLowExponent := by
    apply hFirst0.weaken
    norm_num [isolatedVertexLowExponent]
  have hSecond' : UniformPowerBound
      (fun H T ↦ scaleFactor 1 2 H T * primitiveLowRadialReciprocalMass H T)
      isolatedVertexLowExponent := by
    exact UniformPowerBound.mul_of_add_eq
      (by norm_num [isolatedVertexLowExponent]) hT2
      primitiveLowRadialReciprocalMass_bound
  exact hFirst'.add hSecond'

theorem primitiveZeroRecordMajorant_bound :
    UniformPowerBound primitiveZeroRecordMajorant zeroRecordExponent := by
  simpa [primitiveZeroRecordMajorant, lineOccurrenceExponent,
    zeroRecordExponent] using primitiveOccurrenceMass_bound

/-- The literal sum of the seven displayed canonical majorants.  No record of
assumed branch estimates intervenes. -/
def primitiveTerminalMajorant : CountFunction := fun H T ↦
  primitiveProperMajorant H T +
    (primitivePositiveVertexMajorant H T +
      (primitiveCurvePlaneMajorant H T +
        (primitiveLineMajorant H T +
          (primitiveIsolatedVertexMajorant H T +
            (primitiveIsolatedVertexLowMajorant H T +
              primitiveZeroRecordMajorant H T)))))

/-- Pure power-law closure of the entire terminal ledger. -/
theorem primitiveTerminalMajorant_bound :
    UniformPowerBound primitiveTerminalMajorant targetExponent := by
  obtain ⟨hProper, hPositive, hCurve, hLine, hIsolated, hLow, hZero⟩ :=
    everyBranchExponent_le_target
  have proper := primitiveProperMajorant_bound.weaken hProper
  have positive := primitivePositiveVertexMajorant_bound.weaken hPositive
  have curve := primitiveCurvePlaneMajorant_bound.weaken hCurve
  have line : UniformPowerBound primitiveLineMajorant lineExponent := by
    simpa [sharpLineExponent, lineExponent] using primitiveLineMajorant_bound
  have line' := line.weaken hLine
  have isolated := primitiveIsolatedVertexMajorant_bound.weaken hIsolated
  have low := primitiveIsolatedVertexLowMajorant_bound.weaken hLow
  have zero := primitiveZeroRecordMajorant_bound.weaken hZero
  exact proper.add (positive.add (curve.add (line'.add
    (isolated.add (low.add zero)))))

end

end TranslatedDepthSeven
