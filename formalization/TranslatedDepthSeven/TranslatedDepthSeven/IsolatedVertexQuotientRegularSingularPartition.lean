import TranslatedDepthSeven.IsolatedVertexQuotientStaticSetCover
import TranslatedDepthSeven.IsolatedVertexQuotientOccurrenceScale

/-!
# The regular--singular isolated-vertex quotient partition

This file adds the literal singular complement to the static quotient
reservoir cover.  The fixed deleted certificate is strengthened from the
affine scale `m` to `m * model.denominator`; this is exactly the
coprimality required by the existing occupied-residue estimate.  The static
component label itself is unchanged, since avoiding the product in
particular avoids `m`.

The resulting theorem is still a point-set and occurrence-count statement.
No estimate for the number of points in one geometric `Qbar` component is
introduced here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

local instance isolatedVertexQuotientRegularSingularPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The literal complement of the quotient Jacobian-regular locus inside
the full quotient point set. -/
def isolatedVertexSingularQuotientPointFinset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Finset (IntVector 12) :=
  (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF).filter
    fun w ↦ ¬ IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations) w

@[simp]
theorem mem_isolatedVertexSingularQuotientPointFinset_iff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (w : IntVector 12) :
    w ∈ isolatedVertexSingularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations ↔
      w ∈ isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF ∧
      ¬ IsQuotientJacobianRegularAt
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations) w := by
  classical
  simp [isolatedVertexSingularQuotientPointFinset]

/-- The full quotient set is the disjoint union of its regular and singular
parts. -/
theorem isolatedVertexRegular_union_singularQuotientPointFinset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    isolatedVertexRegularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations ∪
        isolatedVertexSingularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations =
      isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF := by
  classical
  ext w
  by_cases hregular : IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations) w <;>
    simp [isolatedVertexRegularQuotientPointFinset,
      isolatedVertexSingularQuotientPointFinset, hregular]

theorem isolatedVertexRegular_disjoint_singularQuotientPointFinset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    Disjoint
      (isolatedVertexRegularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations)
      (isolatedVertexSingularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwRegular hwSingular
  exact ((mem_isolatedVertexSingularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1 hwSingular).2
    ((mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations w).1 hwRegular).2

/-- The quotient certificate exponent is large enough to absorb one fixed
denominator together with the affine scale once that denominator is at most
the current height. -/
theorem two_le_isolatedVertexQuotientCertificateExponent
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ)) :
    2 ≤ isolatedVertexQuotientCertificateExponent U lowerEquations := by
  unfold isolatedVertexQuotientCertificateExponent
  dsimp only
  omega

theorem isolatedVertexQuotient_scale_mul_modelDenominator_height
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H) :
    ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent
        U lowerEquations := by
  have hm : (p.m : ℝ) ≤ p.H := by
    unfold Parameters.H
    nlinarith [p.hB, p.hL]
  have hproduct : (p.m : ℝ) * model.denominator.natAbs ≤ p.H ^ 2 := by
    calc
      (p.m : ℝ) * model.denominator.natAbs ≤ p.H * p.H := by
        exact mul_le_mul hm hdenominator
          (Nat.cast_nonneg _) p.H_pos.le
      _ = p.H ^ 2 := by ring
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  norm_num only [Nat.cast_mul]
  exact hproduct.trans <| pow_le_pow_right₀ p.one_le_strictHeight
    (two_le_isolatedVertexQuotientCertificateExponent U lowerEquations)

/-- Survival after deleting `m * denominator` implies the survival premise
used by the already-defined static packet label. -/
theorem survivesTwoCertificates_scale_mul_denominator_implies_scale
    {P : Finset ℕ} {k : ℕ} (q : ReservoirModulus P k)
    (m denominator D : ℤ)
    (h : survivesTwoCertificates q (m * denominator) D) :
    survivesTwoCertificates q m D := by
  refine ⟨?_, h.2⟩
  apply h.1.of_dvd_right
  rw [Int.natAbs_mul]
  exact dvd_mul_right m.natAbs denominator.natAbs

/-- Labels occurring after the denominator-compatible certificate deletion. -/
def occurringIsolatedVertexQuotientDenominatorCompatibleLabels
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1) :
    Finset (Option (Ideal (MvPolynomial (Fin 13) Qbar))) :=
  occurringCertificateDeletedLabels
    (isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations)
    (fun _ ↦ (p.m : ℤ) * model.denominator)
    (isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations)
    (isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower)

/-- The empty-label cell for one denominator-compatible surviving modulus. -/
def isolatedVertexQuotientDenominatorCompatibleVertexCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) : Finset (IntVector 12) :=
  (isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
      survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
          (isolatedVertexQuotientSelectedCertificateValue
            U p sourceEquations CF hx₀ lowerEquations w) ∧
        isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w q = none

/-- The unequal-nonempty-label cell for one directed ambient edge. -/
def isolatedVertexQuotientDenominatorCompatibleEdgeCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) : Finset (IntVector 12) :=
  (isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
      survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
          (isolatedVertexQuotientSelectedCertificateValue
            U p sourceEquations CF hx₀ lowerEquations w) ∧
      survivesTwoCertificates r ((p.m : ℤ) * model.denominator)
          (isolatedVertexQuotientSelectedCertificateValue
            U p sourceEquations CF hx₀ lowerEquations w) ∧
      (modulusReservoirGraph Ppool k hP).Adj q r ∧
      isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w q ≠
        isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w r ∧
      isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w q ≠ none ∧
      isolatedVertexQuotientStaticComponentLabel
          U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower w r ≠ none

/-- The cell on which one nonempty component label persists across every
denominator-compatible surviving modulus. -/
def isolatedVertexQuotientDenominatorCompatiblePersistentCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (o : Option (Ideal (MvPolynomial (Fin 13) Qbar))) :
    Finset (IntVector 12) :=
  (isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations).filter fun w ↦
      o ≠ none ∧ ∀ q : ReservoirModulus Ppool k,
        survivesTwoCertificates q ((p.m : ℤ) * model.denominator)
            (isolatedVertexQuotientSelectedCertificateValue
              U p sourceEquations CF hx₀ lowerEquations w) →
          isolatedVertexQuotientStaticComponentLabel
            U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower w q = o

/-- The certificate-deleted static cover with the fixed model denominator
included in the deleted scale.  This is the version compatible with the
occupied-residue theorem. -/
theorem isolatedVertexRegularQuotientPointFinset_subset_denominatorCompatible_staticVertex_edge_persistent
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) :
    isolatedVertexRegularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations ⊆
      Finset.biUnion
        (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun q ↦
          isolatedVertexQuotientDenominatorCompatibleVertexCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q) ∪
        (Finset.biUnion
          (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun q ↦
          Finset.biUnion
            (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun r ↦
            isolatedVertexQuotientDenominatorCompatibleEdgeCell
              U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower q r)) ∪
          Finset.biUnion
            (occurringIsolatedVertexQuotientDenominatorCompatibleLabels
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            Ppool k hqpos hqsf hqlower) (fun o ↦
              isolatedVertexQuotientDenominatorCompatiblePersistentCell
                U p sourceEquations CF hx₀ lowerEquations model hquotient
                hqpos hqsf hqlower o)) := by
  let X := isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations
  let D₁ : IntVector 12 → ℤ :=
    fun _ ↦ (p.m : ℤ) * model.denominator
  let D₂ : IntVector 12 → ℤ :=
    isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations
  let label : IntVector 12 → ReservoirModulus Ppool k →
      Option (Ideal (MvPolynomial (Fin 13) Qbar)) :=
    isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower
  have hfixedNe : (p.m : ℤ) * model.denominator ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.ne_of_gt p.one_le_m)
    · exact model.denominator_ne_zero
  have hfixedSize : ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations :=
    isolatedVertexQuotient_scale_mul_modelDenominator_height
      U p lowerEquations model hdenominator
  have hconnected : ∀ w ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool (D₁ w) (D₂ w)) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected := by
    intro w hw
    exact (hsurvival (D₁ w) (D₂ w) hfixedNe
      (isolatedVertexQuotientSelectedCertificateValue_ne_zero
        U p sourceEquations CF hx₀ lowerEquations hw)
      hfixedSize
      (isolatedVertexQuotientSelectedCertificateValue_height
        U p sourceEquations CF hx₀ lowerEquations hw)).2
  have hcover := subset_union_certificateDeleted_reservoir_nonemptyEdges
    hP X D₁ D₂ label hconnected
  simpa only [X, D₁, D₂, label,
    occurringIsolatedVertexQuotientDenominatorCompatibleLabels,
    isolatedVertexQuotientDenominatorCompatibleVertexCell,
    isolatedVertexQuotientDenominatorCompatibleEdgeCell,
    isolatedVertexQuotientDenominatorCompatiblePersistentCell] using hcover

/-- The same cover with the singular quotient locus carried as a separate
literal first term. -/
theorem isolatedVertexQuotientPointFinset_subset_singular_union_denominatorCompatible_staticVertex_edge_persistent
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) :
    isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF ⊆
      isolatedVertexSingularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations ∪
        (Finset.biUnion
          (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun q ↦
          isolatedVertexQuotientDenominatorCompatibleVertexCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q) ∪
        (Finset.biUnion
          (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun q ↦
          Finset.biUnion
            (Finset.univ : Finset (ReservoirModulus Ppool k)) (fun r ↦
            isolatedVertexQuotientDenominatorCompatibleEdgeCell
              U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower q r)) ∪
          Finset.biUnion
            (occurringIsolatedVertexQuotientDenominatorCompatibleLabels
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            Ppool k hqpos hqsf hqlower) (fun o ↦
              isolatedVertexQuotientDenominatorCompatiblePersistentCell
                U p sourceEquations CF hx₀ lowerEquations model hquotient
                hqpos hqsf hqlower o))) := by
  intro w hw
  by_cases hregular : IsQuotientJacobianRegularAt
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations) w
  · apply Finset.mem_union_right
    apply isolatedVertexRegularQuotientPointFinset_subset_denominatorCompatible_staticVertex_edge_persistent
      U p sourceEquations CF hx₀ lowerEquations model hdenominator
        hquotient Ppool k hP hqpos hqsf hqlower hsurvival
    exact (mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations w).2 ⟨hw, hregular⟩
  · apply Finset.mem_union_left
    exact (mem_isolatedVertexSingularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations w).2 ⟨hw, hregular⟩

/-- Cardinal form of the denominator-compatible regular partition. -/
theorem card_isolatedVertexRegularQuotientPointFinset_le_denominatorCompatible_staticVertex_edge_persistent
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) :
    (isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations).card ≤
      (∑ q : ReservoirModulus Ppool k,
        (isolatedVertexQuotientDenominatorCompatibleVertexCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q).card) +
      (∑ q : ReservoirModulus Ppool k,
        ∑ r : ReservoirModulus Ppool k,
          (isolatedVertexQuotientDenominatorCompatibleEdgeCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r).card) +
      (∑ o ∈ occurringIsolatedVertexQuotientDenominatorCompatibleLabels
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          Ppool k hqpos hqsf hqlower,
        (isolatedVertexQuotientDenominatorCompatiblePersistentCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower o).card) := by
  let X := isolatedVertexRegularQuotientPointFinset
    U p x₀ sourceEquations CF lowerEquations
  let D₁ : IntVector 12 → ℤ :=
    fun _ ↦ (p.m : ℤ) * model.denominator
  let D₂ : IntVector 12 → ℤ :=
    isolatedVertexQuotientSelectedCertificateValue
      U p sourceEquations CF hx₀ lowerEquations
  let label : IntVector 12 → ReservoirModulus Ppool k →
      Option (Ideal (MvPolynomial (Fin 13) Qbar)) :=
    isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower
  have hfixedNe : (p.m : ℤ) * model.denominator ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (Nat.ne_of_gt p.one_le_m)
    · exact model.denominator_ne_zero
  have hfixedSize : ((((p.m : ℤ) * model.denominator).natAbs : ℕ) : ℝ) ≤
      p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations :=
    isolatedVertexQuotient_scale_mul_modelDenominator_height
      U p lowerEquations model hdenominator
  have hconnected : ∀ w ∈ X,
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool (D₁ w) (D₂ w)) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected := by
    intro w hw
    exact (hsurvival (D₁ w) (D₂ w) hfixedNe
      (isolatedVertexQuotientSelectedCertificateValue_ne_zero
        U p sourceEquations CF hx₀ lowerEquations hw)
      hfixedSize
      (isolatedVertexQuotientSelectedCertificateValue_height
        U p sourceEquations CF hx₀ lowerEquations hw)).2
  have hpartition := card_le_sum_certificateDeleted_reservoir_nonemptyEdges
    hP X D₁ D₂ label hconnected
  simpa only [X, D₁, D₂, label,
    occurringIsolatedVertexQuotientDenominatorCompatibleLabels,
    isolatedVertexQuotientDenominatorCompatibleVertexCell,
    isolatedVertexQuotientDenominatorCompatibleEdgeCell,
    isolatedVertexQuotientDenominatorCompatiblePersistentCell] using hpartition

/-- Full quotient cardinality with the singular locus explicit and the
three regular static classes left literal. -/
theorem card_isolatedVertexQuotientPointFinset_le_singular_add_denominatorCompatible_staticVertex_edge_persistent
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hdenominator : (model.denominator.natAbs : ℝ) ≤ p.H)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hsurvival : ∀ E₁ E₂ : ℤ, E₁ ≠ 0 → E₂ ≠ 0 →
      (E₁.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      (E₂.natAbs : ℝ) ≤
        p.H ^ isolatedVertexQuotientCertificateExponent U lowerEquations →
      Nonempty (ReservoirModulus
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k) ∧
      (modulusReservoirGraph
        (certificateAllowedPrimesTwo Ppool E₁ E₂) k
        (fun s hs ↦ hP s (Finset.mem_filter.mp hs).1)).Connected) :
    (isolatedVertexQuotientPointFinset
      U p x₀ sourceEquations CF).card ≤
      (isolatedVertexSingularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations).card +
      ((∑ q : ReservoirModulus Ppool k,
        (isolatedVertexQuotientDenominatorCompatibleVertexCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q).card) +
      (∑ q : ReservoirModulus Ppool k,
        ∑ r : ReservoirModulus Ppool k,
          (isolatedVertexQuotientDenominatorCompatibleEdgeCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r).card) +
      (∑ o ∈ occurringIsolatedVertexQuotientDenominatorCompatibleLabels
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          Ppool k hqpos hqsf hqlower,
        (isolatedVertexQuotientDenominatorCompatiblePersistentCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower o).card)) := by
  have hregular :=
    card_isolatedVertexRegularQuotientPointFinset_le_denominatorCompatible_staticVertex_edge_persistent
      U p sourceEquations CF hx₀ lowerEquations model hdenominator
        hquotient Ppool k hP hqpos hqsf hqlower hsurvival
  have hsplit :
      (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF).card =
        (isolatedVertexRegularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations).card +
        (isolatedVertexSingularQuotientPointFinset
          U p x₀ sourceEquations CF lowerEquations).card := by
    rw [← isolatedVertexRegular_union_singularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations]
    exact Finset.card_union_of_disjoint
      (isolatedVertexRegular_disjoint_singularQuotientPointFinset
        U p x₀ sourceEquations CF lowerEquations)
  rw [hsplit]
  omega

/-! ## Compatibility with the occupied-residue estimate -/

/-- A denominator-compatible vertex cell is a literal subset of the full
quotient point set. -/
theorem isolatedVertexQuotientDenominatorCompatibleVertexCell_subset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q ⊆
      isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF := by
  intro w hw
  exact (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1
      (Finset.mem_filter.mp hw).1 |>.1

/-- Nonemptiness of a denominator-compatible vertex cell certifies exactly
the fixed coprimality tested in the occurrence sum. -/
theorem coprime_scale_modelDenominator_of_mem_denominatorCompatibleVertexCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q : ReservoirModulus Ppool k} {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q) :
    Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs) :=
  ((Finset.mem_filter.mp hw).2.1).1

/-- The occupied residues of a vertex cell are bounded by the exact
`if`-summand already present in the quotient occurrence estimate. -/
theorem card_occupiedResidues_denominatorCompatibleVertexCell_le_if
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    ((occupiedIntegralResidues q.1
      (isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q)).card : ℝ) ≤
      if Nat.Coprime q.1 (((p.m : ℤ) * model.denominator).natAbs)
      then ((occupiedIntegralResidues q.1
        (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF)).card : ℝ) else 0 := by
  by_cases hcop : Nat.Coprime q.1
      (((p.m : ℤ) * model.denominator).natAbs)
  · rw [if_pos hcop]
    exact_mod_cast Finset.card_le_card <|
      occupiedIntegralResidues_mono <|
        isolatedVertexQuotientDenominatorCompatibleVertexCell_subset
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q
  · rw [if_neg hcop]
    have hempty : isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hcop
        (coprime_scale_modelDenominator_of_mem_denominatorCompatibleVertexCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower hw)
    simp [hempty]

/-- An edge cell is likewise a subset of the full quotient point set. -/
theorem isolatedVertexQuotientDenominatorCompatibleEdgeCell_subset
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    isolatedVertexQuotientDenominatorCompatibleEdgeCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r ⊆
      isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF := by
  intro w hw
  exact (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1
      (Finset.mem_filter.mp hw).1 |>.1

/-- Survival at both endpoints makes the edge lcm coprime to the fixed
scale--denominator product. -/
theorem coprime_lcm_scale_modelDenominator_of_mem_denominatorCompatibleEdgeCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q r : ReservoirModulus Ppool k} {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r) :
    Nat.Coprime (Nat.lcm q.1 r.1)
      (((p.m : ℤ) * model.denominator).natAbs) := by
  obtain ⟨_hwRegular, hqSurvives, hrSurvives, _hadj,
      _hne, _hqNonempty, _hrNonempty⟩ := Finset.mem_filter.mp hw
  have hproduct : Nat.Coprime (q.1 * r.1)
      (((p.m : ℤ) * model.denominator).natAbs) :=
    hqSurvives.1.mul_left hrSurvives.1
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul q.1 r.1) hproduct

/-- The edge-cell residue count is bounded by the exact lcm summand in the
existing occurrence estimate. -/
theorem card_occupiedResidues_denominatorCompatibleEdgeCell_le_if
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    ((occupiedIntegralResidues (Nat.lcm q.1 r.1)
      (isolatedVertexQuotientDenominatorCompatibleEdgeCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r)).card : ℝ) ≤
      if Nat.Coprime (Nat.lcm q.1 r.1)
          (((p.m : ℤ) * model.denominator).natAbs)
      then ((occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF)).card : ℝ) else 0 := by
  by_cases hcop : Nat.Coprime (Nat.lcm q.1 r.1)
      (((p.m : ℤ) * model.denominator).natAbs)
  · rw [if_pos hcop]
    exact_mod_cast Finset.card_le_card <|
      occupiedIntegralResidues_mono <|
        isolatedVertexQuotientDenominatorCompatibleEdgeCell_subset
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r
  · rw [if_neg hcop]
    have hempty : isolatedVertexQuotientDenominatorCompatibleEdgeCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hcop
        (coprime_lcm_scale_modelDenominator_of_mem_denominatorCompatibleEdgeCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower hw)
    simp [hempty]

/-- The actual denominator-compatible vertex and directed-edge cells obey
the already-proved quotient occurrence-scale estimate.  This bounds their
number of occupied packets, not the number of integral points inside one
packet. -/
theorem isolatedVertexQuotient_denominatorCompatible_static_node_edge_occupiedResidues_cast_le_scale
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ)
    (hC₀ : 0 ≤ C₀)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (Ppool : Finset ℕ) (k : ℕ) (hP : ∀ l ∈ Ppool, l.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hk : k ≤ reservoirDepth M₀ p.H)
    (h2k : 2 * k ≤ reservoirDepth M₀ p.H)
    (hH : reservoirSubpowerThreshold M₀
      (model.localConstant : ℝ) δ ≤ p.H)
    (hfamily : ((((modulusReservoir Ppool k).card +
      (modulusReservoirDirectedEdges Ppool k hP).card : ℕ) : ℝ) ≤
        2 * p.H ^ δ))
    (hupperNode : ∀ q : ReservoirModulus Ppool k,
      (q.1 : ℝ) ≤ C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ)
    (hupperEdge : ∀ q r : ReservoirModulus Ppool k,
      (modulusReservoirGraph Ppool k hP).Adj q r →
      (Nat.lcm q.1 r.1 : ℝ) ≤
        C₀ * p.T ^ (9 / 13 : ℝ) * p.H ^ δ) :
    (∑ q : ReservoirModulus Ppool k,
        ((occupiedIntegralResidues q.1
          (isolatedVertexQuotientDenominatorCompatibleVertexCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower q)).card : ℝ)) +
      (∑ qr : ↑(modulusReservoirDirectedEdges Ppool k hP),
        ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1)
          (isolatedVertexQuotientDenominatorCompatibleEdgeCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower qr.1.1 qr.1.2)).card : ℝ)) ≤
      2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ) := by
  have hoccurrence :=
    isolatedVertexQuotient_node_edge_occupiedResidues_cast_le_scale
      hM₀ hδ hC₀ U p x₀ sourceEquations CF lowerEquations model
        hquotient Ppool k hP hqsf hk h2k hH hfamily
        hupperNode hupperEdge
  apply le_trans ?_ hoccurrence
  apply add_le_add
  · apply Finset.sum_le_sum
    intro q _hq
    exact card_occupiedResidues_denominatorCompatibleVertexCell_le_if
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q
  · apply Finset.sum_le_sum
    intro qr _hqr
    exact card_occupiedResidues_denominatorCompatibleEdgeCell_le_if
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower qr.1.1 qr.1.2

/-! ## Geometric meaning of the three regular classes -/

/-- A persistent nonempty label is a single retained nonradial quotient
curve through the point.  Only one explicit surviving modulus is needed to
specialize the persistent equality. -/
theorem mem_zeroLocus_and_retainedNonradial_of_mem_denominatorCompatiblePersistentCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {Q : Ideal (MvPolynomial (Fin 13) Qbar)}
    {w : IntVector 12} {q : ReservoirModulus Ppool k}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatiblePersistentCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower (some Q))
    (hqSurvives : survivesTwoCertificates q
      ((p.m : ℤ) * model.denominator)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w)) :
    geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus Q ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Q := by
  have hwdata := Finset.mem_filter.mp hw
  have hqScale :=
    survivesTwoCertificates_scale_mul_denominator_implies_scale q
      (p.m : ℤ) model.denominator
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) hqSurvives
  have hlabel : isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower w q = some Q := hwdata.2.2 q hqSurvives
  have hspec := isolatedVertexQuotientStaticComponentLabel_eq_some_spec
    U p sourceEquations CF hx₀ lowerEquations hquotient
      hqpos hqsf hqlower hwdata.1 q hqScale hlabel
  exact ⟨hspec.2.1, hspec.2.2.1⟩

/-- Every denominator-compatible edge point lies on the intersection of
two literal distinct retained nonradial quotient curves. -/
theorem exists_distinct_retainedNonradialQuotientNodeComponents_and_mem_sup_of_mem_denominatorCompatibleEdgeCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q r : ReservoirModulus Ppool k} {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r) :
    ∃ Qq Qr : Ideal (MvPolynomial (Fin 13) Qbar),
      Qq ≠ Qr ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus (Qq ⊔ Qr) ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Qq ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Qr := by
  obtain ⟨hwRegular, hqSurvives, hrSurvives, _hqr,
      hlabelsNe, hqNonempty, hrNonempty⟩ := Finset.mem_filter.mp hw
  have hqScale :=
    survivesTwoCertificates_scale_mul_denominator_implies_scale q
      (p.m : ℤ) model.denominator
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) hqSurvives
  have hrScale :=
    survivesTwoCertificates_scale_mul_denominator_implies_scale r
      (p.m : ℤ) model.denominator
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) hrSurvives
  obtain ⟨Qq, Qr, hne, _hqLabel, _hrLabel, hmem, hQq, hQr⟩ :=
    exists_distinct_retainedNonradialQuotientNodeComponents_and_mem_sup_of_static_edge
      U p sourceEquations CF hx₀ lowerEquations hquotient
        hqpos hqsf hqlower hwRegular hqScale hrScale
        hlabelsNe hqNonempty hrNonempty
  exact ⟨Qq, Qr, hne, hmem, hQq, hQr⟩

/-- A literal elementary component through a point on one actual integral
quotient packet plane. -/
def HasElementaryIntegralQuotientNodeComponentAtPoint
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ}
    {rho : Fin 12 → ZMod q} (w : IntVector 12) : Prop :=
  ∃ plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho,
    ∃ P ∈ integralQuotientNodeComponentsThroughPoint
        lowerEquations b m hm plane w,
      IsElementaryQuotientNodeComponent
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P

/-- A quotient point has a literal normalized source preimage which lies in
the bounded-height exceptional locus produced by the four-class theorem. -/
def HasIsolatedVertexQuotientSourceExceptionalLift
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (x₀ : IntVector 13) (w : IntVector 12) : Prop :=
  ∃ z ∈ depthSevenNormalizedDisplacementFinset
      p x₀ sourceEquations CF,
    dropFirstIntVector (U.pointEquiv z) = w ∧
      ∃ hx : integralAffineMap x₀ z p.m ≠ 0,
        MemDepthSevenExceptionalLocus sourceEquations
          ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊
          (integralProjectiveClass
            (integralAffineMap x₀ z p.m) hx)

/-- The empty-label vertex class contains no hidden nonradial curve: it is
the union of actual zero/radial component points and source-exceptional
lifts.  The only outside inputs are the three narrow projective-geometric
propositions already used by the four-class theorem. -/
theorem elementary_or_sourceExceptional_of_mem_denominatorCompatibleVertexCell
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hfamily : U.transformEquationFinset sourceEquations =
      liftEquationFinsetAfterFirst lowerEquations)
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : Published.HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q : ReservoirModulus Ppool k} {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q) :
    HasElementaryIntegralQuotientNodeComponentAtPoint lowerEquations
        (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ)
        (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
        (Z := isolatedVertexQuotientPointFinset
          U p x₀ sourceEquations CF)
        (q := q.1) (R := isolatedVertexTransformedNaturalSide U p)
        (rho := integralResidueVector w) w ∨
      HasIsolatedVertexQuotientSourceExceptionalLift
        U p sourceEquations CF x₀ w := by
  obtain ⟨hwRegular, hqSurvives, hlabelStatic⟩ := Finset.mem_filter.mp hw
  have hwPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1 hwRegular |>.1
  obtain ⟨z, hz, hzw⟩ := (mem_isolatedVertexQuotientPointFinset_iff
    U p x₀ sourceEquations CF w).1 hwPoint
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hbox, _hzero, hx, _hlinear, _hnotExceptional⟩ := hzdata
  have hm : (p.m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt p.one_le_m)
  have hqScale :=
    survivesTwoCertificates_scale_mul_denominator_implies_scale q
      (p.m : ℤ) model.denominator
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w) hqSurvives
  let heligible := isEligibleIsolatedVertexQuotientPacket_of_survives
    U p sourceEquations CF hx₀ lowerEquations q hwRegular hqScale
  let plane := selectedIntegralIsolatedVertexQuotientPacketPlane
    U p x₀ sourceEquations CF lowerEquations hquotient
      q.1 (hqpos q) (hqsf q) (hqlower q)
      (integralResidueVector w) heligible
  have hwPacket : w ∈ integralResiduePacket
      (isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF)
      (integralResidueVector w : Fin 12 → ZMod q.1) :=
    mem_integralResiduePacket_iff.mpr ⟨hwPoint, rfl⟩
  have hy := integralCommonZero_lower_of_mem_regularQuotient
    U p x₀ sourceEquations CF lowerEquations hquotient hwRegular
  let x := integralAffineMap x₀ z p.m
  have hspatial : dropFirstIntVector (U.pointEquiv x) =
      integralQuotientAffinePoint
        (dropFirstIntVector (U.pointEquiv x₀)) w (p.m : ℤ) := by
    dsimp only [x]
    rw [dropFirst_pointEquiv_integralAffineMap_eq_integralQuotientAffinePoint,
      hzw]
  have hlabel : integralQuotientPacketPriorityLabel lowerEquations
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm plane w = none := by
    unfold isolatedVertexQuotientStaticComponentLabel at hlabelStatic
    dsimp only at hlabelStatic
    rw [dif_pos heligible] at hlabelStatic
    exact hlabelStatic
  have hdisposition :=
    integralQuotientPacketPriorityLabel_eq_none_implies_elementary_or_exceptional
      hMass hProjection hRadial p sourceEquations U lowerEquations hfamily
        CF x₀ hx₀ hJprime hJhomogeneous degree hJHilbert hm
        plane w hwPacket hy x hx hspatial hlabel
  rcases hdisposition with helementary | hexceptional
  · left
    exact ⟨plane, helementary⟩
  · right
    exact ⟨z, hz, hzw, hx, by simpa only [x] using hexceptional⟩

end

end TranslatedDepthSeven
