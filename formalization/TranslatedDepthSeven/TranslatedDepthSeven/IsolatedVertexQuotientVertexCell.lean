import TranslatedDepthSeven.IsolatedVertexQuotientEdgeBezout
import TranslatedDepthSeven.ExceptionalCutoffMonotonicity

/-!
# The elementary content of the quotient empty-label cell

At the source-section cutoff already built into the quotient construction,
the exceptional alternative behind an empty static label contradicts the
literal defining nonexceptional condition of the normalized source point.
Thus, once the global cutoff is at least the fixed source-section exponent,
every point of the denominator-compatible vertex cell lies on an actual
zero-dimensional or radial component of its selected quotient node.

This file is only the set-theoretic adapter.  It does not assume a point
count for either elementary class.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance isolatedVertexQuotientVertexCellPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- A source-exceptional lift at the fixed quotient-section height cannot
occur in the normalized set once the global cutoff dominates that fixed
exponent. -/
theorem not_hasIsolatedVertexQuotientSourceExceptionalLift_of_cutoff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (x₀ : IntVector 13)
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
    (w : IntVector 12) :
    ¬ HasIsolatedVertexQuotientSourceExceptionalLift
        U p sourceEquations CF x₀ w := by
  rintro ⟨z, hz, _hzw, hx, hexceptional⟩
  have hzdata := (Finset.mem_filter.mp hz).2
  dsimp only at hzdata
  obtain ⟨_hbox, _hzero, hx', _hlinear, hnotExceptional⟩ := hzdata
  apply hnotExceptional
  exact memDepthSevenExceptionalLocus_mono_height sourceEquations
    (exceptionalHeightCutoff_mono p hCF) hexceptional

/-- At the final cutoff, every empty-label point has an actual elementary
component on the one selected integral packet plane. -/
theorem hasElementaryIntegralQuotientNodeComponentAtPoint_of_mem_denominatorCompatibleVertexCell
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
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
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
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
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
      (rho := integralResidueVector w) w := by
  rcases elementary_or_sourceExceptional_of_mem_denominatorCompatibleVertexCell
    hMass hProjection hRadial U p sourceEquations CF hx₀ lowerEquations
      model hfamily hJprime hJhomogeneous degree hJHilbert hquotient
        hqpos hqsf hqlower hw with helementary | hexceptional
  · exact helementary
  · exact False.elim
      (not_hasIsolatedVertexQuotientSourceExceptionalLift_of_cutoff
        U p sourceEquations CF x₀ hCF w hexceptional)

/-! ## The residue-static elementary record family -/

/-- The elementary members of the one node-component list selected before
choosing a point in the residue packet.  Keeping this filter on the static
list is important: allowing a fresh packet plane to be chosen for every
point would destroy the component-degree-mass bound. -/
def isolatedVertexQuotientStaticElementaryComponentsAtResidue
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
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
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1) :
    Finset (Ideal (MvPolynomial (Fin 13) Qbar)) :=
  (isolatedVertexQuotientStaticNodeComponentsAtResidue
    U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower q rho).filter fun P ↦
    IsElementaryQuotientNodeComponent
      (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
      (algebraMap ℚ Qbar (p.m : ℚ)) P

/-- At the final source-section cutoff, an empty-label point lies on an
elementary component of the *specific* node selected from its pair
`(q, residue(w))`.  This strengthens the existential-plane adapter above
to the form needed for degree-mass aggregation. -/
theorem exists_staticElementaryComponent_of_mem_denominatorCompatibleVertexCell
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
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
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
    {q : ReservoirModulus Ppool k} {w : IntVector 12}
    (hw : w ∈ isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q) :
    ∃ P ∈ isolatedVertexQuotientStaticElementaryComponentsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q (integralResidueVector w),
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P := by
  classical
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
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF)
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
  · obtain ⟨P, hPthrough, hPelem⟩ := helementary
    have hPdata := Finset.mem_filter.mp hPthrough
    refine ⟨P, ?_, hPdata.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hPelem⟩
    unfold isolatedVertexQuotientStaticNodeComponentsAtResidue
    rw [dif_pos heligible]
    exact hPdata.1
  · exact False.elim
      (not_hasIsolatedVertexQuotientSourceExceptionalLift_of_cutoff
        U p sourceEquations CF x₀ hCF w
          ⟨z, hz, hzw, hx, by simpa only [x] using hexceptional⟩)

/-- The elementary static list inherits the degree-mass cardinal bound of
the complete node-component list. -/
theorem card_isolatedVertexQuotientStaticElementaryComponentsAtResidue_le_degree
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (x₀ : IntVector 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1) :
    (isolatedVertexQuotientStaticElementaryComponentsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho).card ≤ degree := by
  exact (Finset.card_filter_le _ _).trans
    (card_isolatedVertexQuotientStaticNodeComponentsAtResidue_le_degree
      hMass U p sourceEquations CF x₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower q rho)

/-- One literal elementary component occurrence, indexed by the source
modulus and its actual occupied residue. -/
structure IsolatedVertexQuotientStaticElementaryRecord (q : ℕ) where
  residue : Fin 12 → ZMod q
  component : Ideal (MvPolynomial (Fin 13) Qbar)

/-- Elementary component records over one occupied residue. -/
def isolatedVertexQuotientStaticElementaryRecordsAtResidue
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1) :
    Finset (IsolatedVertexQuotientStaticElementaryRecord q.1) := by
  classical
  exact (isolatedVertexQuotientStaticElementaryComponentsAtResidue
    U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower q rho).image fun P ↦
    { residue := rho, component := P }

@[simp]
theorem mem_isolatedVertexQuotientStaticElementaryRecordsAtResidue_iff
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1)
    (record : IsolatedVertexQuotientStaticElementaryRecord q.1) :
    record ∈ isolatedVertexQuotientStaticElementaryRecordsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q rho ↔
      record.residue = rho ∧
      record.component ∈
        isolatedVertexQuotientStaticElementaryComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q rho := by
  classical
  constructor
  · intro hrecord
    obtain ⟨P, hP, hEq⟩ := Finset.mem_image.mp hrecord
    cases hEq
    exact ⟨rfl, hP⟩
  · rintro ⟨hresidue, hcomponent⟩
    apply Finset.mem_image.mpr
    refine ⟨record.component, hcomponent, ?_⟩
    cases record
    simp_all

/-- The finite elementary record list actually used by one
denominator-compatible vertex cell. -/
def occupiedIsolatedVertexQuotientStaticElementaryRecords
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    Finset (IsolatedVertexQuotientStaticElementaryRecord q.1) := by
  classical
  exact (occupiedIntegralResidues q.1
    (isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q)).biUnion fun rho ↦
    isolatedVertexQuotientStaticElementaryRecordsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho

/-- Points of the vertex cell in one literal residue/component record. -/
def isolatedVertexQuotientStaticElementaryRecordPointCell
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q : ReservoirModulus Ppool k}
    (record : IsolatedVertexQuotientStaticElementaryRecord q.1) :
    Finset (IntVector 12) :=
  (isolatedVertexQuotientDenominatorCompatibleVertexCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower q).filter fun w ↦
    (integralResidueVector w : Fin 12 → ZMod q.1) = record.residue ∧
    geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus record.component

/-- The cutoff-empty-label cell is covered by the literal occupied
elementary records attached to its own source modulus. -/
theorem isolatedVertexQuotientDenominatorCompatibleVertexCell_subset_elementaryRecordUnion
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
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
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
    (q : ReservoirModulus Ppool k) :
    isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q ⊆
      (occupiedIsolatedVertexQuotientStaticElementaryRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q).biUnion fun record ↦
        isolatedVertexQuotientStaticElementaryRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower record := by
  classical
  intro w hw
  obtain ⟨P, hP, hPw⟩ :=
    exists_staticElementaryComponent_of_mem_denominatorCompatibleVertexCell
      hMass hProjection hRadial U p sourceEquations CF hx₀ lowerEquations
        model hfamily hJprime hJhomogeneous degree hJHilbert hquotient
        hqpos hqsf hqlower hCF hw
  let rho : Fin 12 → ZMod q.1 := integralResidueVector w
  let record : IsolatedVertexQuotientStaticElementaryRecord q.1 :=
    { residue := rho, component := P }
  have hrho : rho ∈ occupiedIntegralResidues q.1
      (isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hrecord : record ∈
      occupiedIsolatedVertexQuotientStaticElementaryRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q := by
    apply Finset.mem_biUnion.mpr
    refine ⟨rho, hrho, ?_⟩
    apply (mem_isolatedVertexQuotientStaticElementaryRecordsAtResidue_iff
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho record).2
    exact ⟨rfl, by simpa only [rho] using hP⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨record, hrecord, Finset.mem_filter.mpr ⟨hw, rfl, ?_⟩⟩
  simpa only [record] using hPw

/-- Cardinal form of the literal elementary-record cover. -/
theorem card_isolatedVertexQuotientDenominatorCompatibleVertexCell_le_sum_elementaryRecordCells
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
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
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
    (q : ReservoirModulus Ppool k) :
    (isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q).card ≤
      ∑ record ∈ occupiedIsolatedVertexQuotientStaticElementaryRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q,
        (isolatedVertexQuotientStaticElementaryRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower record).card := by
  calc
    _ ≤ ((occupiedIsolatedVertexQuotientStaticElementaryRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q).biUnion fun record ↦
          isolatedVertexQuotientStaticElementaryRecordPointCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hqpos hqsf hqlower record).card :=
      Finset.card_le_card
        (isolatedVertexQuotientDenominatorCompatibleVertexCell_subset_elementaryRecordUnion
          hMass hProjection hRadial U p sourceEquations CF hx₀ lowerEquations
            model hfamily hJprime hJhomogeneous degree hJHilbert hquotient
            hqpos hqsf hqlower hCF q)
    _ ≤ _ := Finset.card_biUnion_le

/-- The number of occupied elementary component records over one source
modulus is at most `degree` times the number of occupied residue packets. -/
theorem card_occupiedIsolatedVertexQuotientStaticElementaryRecords_le
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    (occupiedIsolatedVertexQuotientStaticElementaryRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q).card ≤
      (occupiedIntegralResidues q.1
        (isolatedVertexQuotientDenominatorCompatibleVertexCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q)).card * degree := by
  classical
  let residues := occupiedIntegralResidues q.1
    (isolatedVertexQuotientDenominatorCompatibleVertexCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q)
  calc
    _ ≤ ∑ rho ∈ residues,
        (isolatedVertexQuotientStaticElementaryRecordsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q rho).card := Finset.card_biUnion_le
    _ ≤ ∑ _rho ∈ residues, degree := by
      apply Finset.sum_le_sum
      intro rho _hrho
      exact (Finset.card_image_le.trans
        (card_isolatedVertexQuotientStaticElementaryComponentsAtResidue_le_degree
          hMass U p sourceEquations CF x₀ lowerEquations hJprime
            hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
            q rho))
    _ = residues.card * degree := by simp

/-! ## Zero-dimensional versus radial records -/

namespace StandardAG

/-- A projective zero-fold of degree `d` has a reduced first affine-chart
coordinate algebra spanned by `d` elements.  This is the standard equality
between the degree of a reduced zero-dimensional projective variety and the
length of any affine chart.  The statement contains no integral-point or
reservoir count; the point injection is proved separately in
`IsolatedVertexQuotientEdgeBezout`.

For the integral prime components used below, `d = 1`, so their first chart
contains at most one geometric point. -/
def QbarIntegralProjectiveZerofoldFirstChartDegree : Prop :=
  ∀ (N d : ℕ) (P : Ideal (MvPolynomial (Fin (N + 1)) Qbar)),
    P.IsPrime →
    P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) →
    HasProjectiveDimensionDegree P 0 d →
      ∃ spanningFamily : Fin d →
          (MvPolynomial (Fin (N + 1)) Qbar ⧸
            qbarFirstAffineChartReducedIdeal P),
        Submodule.span Qbar (Set.range spanningFamily) = ⊤

end StandardAG

/-- The zero-dimensional elementary records. -/
def occupiedIsolatedVertexQuotientStaticZeroRecords
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    Finset (IsolatedVertexQuotientStaticElementaryRecord q.1) :=
  (occupiedIsolatedVertexQuotientStaticElementaryRecords
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower q).filter fun record ↦
    ∃ s e : ℕ,
      IsZeroDimensionalQuotientNodeComponent record.component s e

/-- The radial-line elementary records. -/
def occupiedIsolatedVertexQuotientStaticRadialRecords
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    Finset (IsolatedVertexQuotientStaticElementaryRecord q.1) :=
  (occupiedIsolatedVertexQuotientStaticElementaryRecords
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower q).filter fun record ↦
    ∃ s e : ℕ, IsRadialQuotientNodeLine
      (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
      (algebraMap ℚ Qbar (p.m : ℚ)) record.component s e

/-- Every occupied elementary record is literally zero-dimensional or
radial. -/
theorem staticElementaryRecord_zero_or_radial
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q : ReservoirModulus Ppool k}
    {record : IsolatedVertexQuotientStaticElementaryRecord q.1}
    (hrecord : record ∈
      occupiedIsolatedVertexQuotientStaticElementaryRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q) :
    (∃ s e : ℕ,
      IsZeroDimensionalQuotientNodeComponent record.component s e) ∨
    (∃ s e : ℕ, IsRadialQuotientNodeLine
      (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
      (algebraMap ℚ Qbar (p.m : ℚ)) record.component s e) := by
  obtain ⟨rho, _hrho, hrecordAt⟩ := Finset.mem_biUnion.mp hrecord
  have hcomponent :=
    (mem_isolatedVertexQuotientStaticElementaryRecordsAtResidue_iff
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho record).1 hrecordAt |>.2
  have helementary := (Finset.mem_filter.mp hcomponent).2
  obtain ⟨s, e, hzero | hradial⟩ := helementary
  · exact Or.inl ⟨s, e, hzero⟩
  · exact Or.inr ⟨s, e, hradial⟩

/-- The occupied elementary list is covered by its literal zero and radial
sublists. -/
theorem occupiedStaticElementaryRecords_subset_zero_union_radial
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    occupiedIsolatedVertexQuotientStaticElementaryRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q ⊆
      occupiedIsolatedVertexQuotientStaticZeroRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q ∪
        occupiedIsolatedVertexQuotientStaticRadialRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q := by
  intro record hrecord
  rcases staticElementaryRecord_zero_or_radial
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower hrecord with hzero | hradial
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrecord, hzero⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrecord, hradial⟩)

/-- One zero-dimensional record contributes at most one normalized affine
quotient point.  The only outside input is the chart-degree statement above. -/
theorem card_staticElementaryRecordPointCell_le_one_of_zero
    (hZeroChart : StandardAG.QbarIntegralProjectiveZerofoldFirstChartDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q : ReservoirModulus Ppool k}
    (record : IsolatedVertexQuotientStaticElementaryRecord q.1)
    (hzero : ∃ s e : ℕ,
      IsZeroDimensionalQuotientNodeComponent record.component s e) :
    (isolatedVertexQuotientStaticElementaryRecordPointCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower record).card ≤ 1 := by
  obtain ⟨s, e, hzero⟩ := hzero
  have hdegree : HasProjectiveDimensionDegree record.component 0 1 := by
    simpa only [hzero.2.2.1, hzero.2.2.2] using hzero.2.1
  obtain ⟨spanningFamily, hspan⟩ := hZeroChart 12 1 record.component
    hzero.1.1 hzero.1.2 hdegree
  exact card_le_of_geometricQuotientPoints_mem_firstChart_of_span
    record.component
    (isolatedVertexQuotientStaticElementaryRecordPointCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower record) 1
    (fun w hw ↦ (Finset.mem_filter.mp hw).2.2)
    spanningFamily hspan

/-- The actual zero-dimensional part of one denominator-compatible vertex
cell, still indexed by the original source modulus. -/
def isolatedVertexQuotientDenominatorCompatibleZeroPointUnion
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) : Finset (IntVector 12) :=
  (occupiedIsolatedVertexQuotientStaticZeroRecords
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower q).biUnion fun record ↦
    isolatedVertexQuotientStaticElementaryRecordPointCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower record

/-- The actual radial part of one denominator-compatible vertex cell. -/
def isolatedVertexQuotientDenominatorCompatibleRadialPointUnion
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) : Finset (IntVector 12) :=
  (occupiedIsolatedVertexQuotientStaticRadialRecords
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower q).biUnion fun record ↦
    isolatedVertexQuotientStaticElementaryRecordPointCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower record

/-- Literal zero/radial cover of the full cutoff vertex cell. -/
theorem isolatedVertexQuotientDenominatorCompatibleVertexCell_subset_zero_union_radial
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
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
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (hCF : isolatedVertexQuotientSourceSectionHeightExponent U ≤ CF)
    (q : ReservoirModulus Ppool k) :
    isolatedVertexQuotientDenominatorCompatibleVertexCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower q ⊆
      isolatedVertexQuotientDenominatorCompatibleZeroPointUnion
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q ∪
        isolatedVertexQuotientDenominatorCompatibleRadialPointUnion
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q := by
  classical
  intro w hw
  have hrecords :=
    isolatedVertexQuotientDenominatorCompatibleVertexCell_subset_elementaryRecordUnion
      hMass hProjection hRadial U p sourceEquations CF hx₀ lowerEquations
        model hfamily hJprime hJhomogeneous degree hJHilbert hquotient
        hqpos hqsf hqlower hCF q hw
  obtain ⟨record, hrecord, hwrecord⟩ := Finset.mem_biUnion.mp hrecords
  rcases staticElementaryRecord_zero_or_radial
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hqpos hqsf hqlower hrecord with hzero | hradialRecord
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨record, Finset.mem_filter.mpr ⟨hrecord, hzero⟩, hwrecord⟩
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨record, Finset.mem_filter.mpr ⟨hrecord, hradialRecord⟩,
      hwrecord⟩

/-- The complete zero-dimensional contribution of one source modulus is
bounded by `degree` times its actual occupied-residue count. -/
theorem card_isolatedVertexQuotientDenominatorCompatibleZeroPointUnion_le
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hZeroChart : StandardAG.QbarIntegralProjectiveZerofoldFirstChartDegree)
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (model : FixedQuotientFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset lowerEquations)))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) :
    (isolatedVertexQuotientDenominatorCompatibleZeroPointUnion
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hqpos hqsf hqlower q).card ≤
      (occupiedIntegralResidues q.1
        (isolatedVertexQuotientDenominatorCompatibleVertexCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q)).card * degree := by
  calc
    _ ≤ ∑ record ∈ occupiedIsolatedVertexQuotientStaticZeroRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q,
        (isolatedVertexQuotientStaticElementaryRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower record).card := Finset.card_biUnion_le
    _ ≤ ∑ _record ∈ occupiedIsolatedVertexQuotientStaticZeroRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q, 1 := by
      apply Finset.sum_le_sum
      intro record hrecord
      exact card_staticElementaryRecordPointCell_le_one_of_zero hZeroChart
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hqpos hqsf hqlower record (Finset.mem_filter.mp hrecord).2
    _ = (occupiedIsolatedVertexQuotientStaticZeroRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q).card := by simp
    _ ≤ (occupiedIsolatedVertexQuotientStaticElementaryRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hqpos hqsf hqlower q).card := Finset.card_filter_le _ _
    _ ≤ _ := card_occupiedIsolatedVertexQuotientStaticElementaryRecords_le
      hMass U p sourceEquations CF hx₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert model hquotient hqpos hqsf hqlower q

end

end TranslatedDepthSeven
