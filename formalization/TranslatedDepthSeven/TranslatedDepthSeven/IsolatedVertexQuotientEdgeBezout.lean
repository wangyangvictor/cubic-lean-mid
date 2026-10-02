import TranslatedDepthSeven.IsolatedVertexQuotientRegularSingularPartition
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount
import TranslatedDepthSeven.RankSevenRecordCardinality

/-!
# A literal Bezout bound for isolated-vertex quotient edge cells

The unequal-label edge class puts a normalized rational point on two
distinct geometric quotient curves.  This file turns the usual
scheme-theoretic Bezout rank bound for their first affine-chart
intersection into a cardinal bound by the kernel-proved linear
independence of distinct algebra homomorphisms.

The only new textbook premise is a degree statement about the coordinate
algebra of that zero-dimensional chart.  It contains no integral-point,
packet, reservoir, or branch-count conclusion.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance isolatedVertexQuotientEdgeBezoutPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The first affine chart of a homogeneous ideal, kept in homogeneous
coordinates by adjoining the literal equation `X₀ - 1`. -/
def qbarFirstAffineChartIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) Qbar)) :
    Ideal (MvPolynomial (Fin (N + 1)) Qbar) :=
  I ⊔ Ideal.span ({X 0 - C 1} : Set (MvPolynomial (Fin (N + 1)) Qbar))

/-- The reduced first affine-chart intersection.  Point counting sees this
radical and does not require a bound on nilpotent scheme thickness. -/
def qbarFirstAffineChartReducedIdeal {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) Qbar)) :
    Ideal (MvPolynomial (Fin (N + 1)) Qbar) :=
  (qbarFirstAffineChartIdeal I).radical

namespace StandardAG

/-- Reduced Bezout for the zero-dimensional first-chart intersection of two
distinct integral projective curves.  The conclusion is the degree statement
that its reduced coordinate algebra is spanned by at most `d * e` elements.
Point counting is deliberately absent.

This is the reduced-variety Bezout inequality (e.g. Fulton, *Intersection
Theory*, Example 8.4.6, or Heintz's affine Bezout inequality), followed by
the equality between degree and coordinate-algebra length for a reduced
zero-dimensional affine variety. -/
def QbarDistinctProjectiveCurveFirstChartBezout : Prop :=
  ∀ (N d e : ℕ)
    (P Q : Ideal (MvPolynomial (Fin (N + 1)) Qbar)),
    P.IsPrime →
    Q.IsPrime →
    P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) →
    Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) Qbar) →
    HasProjectiveDimensionDegree P 1 d →
    HasProjectiveDimensionDegree Q 1 e →
    P ≠ Q →
      ∃ spanningFamily : Fin (d * e) →
          (MvPolynomial (Fin (N + 1)) Qbar ⧸
            qbarFirstAffineChartReducedIdeal (P ⊔ Q)),
        Submodule.span Qbar (Set.range spanningFamily) = ⊤

end StandardAG

/-- The normalized quotient-point embedding is injective. -/
theorem geometricQuotientRationalHomogeneousAffinePoint_injective :
    Function.Injective
      (geometricQuotientRationalHomogeneousAffinePoint :
        IntVector 12 → Fin 13 → Qbar) := by
  intro w z hwz
  funext i
  have hi := congrFun hwz i.succ
  simpa [geometricQuotientRationalHomogeneousAffinePoint,
    quotientRationalHomogeneousAffinePoint, qbarIntVector] using hi

/-- A normalized quotient point on `I` is a zero of the literal first-chart
ideal. -/
theorem geometricQuotientPoint_mem_qbarFirstAffineChartIdeal
    (I : Ideal (MvPolynomial (Fin 13) Qbar)) (w : IntVector 12)
    (hw : geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus I) :
    geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus (qbarFirstAffineChartIdeal I) := by
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hw ⊢
  unfold qbarFirstAffineChartIdeal
  apply sup_le
  · exact hw
  · rw [Ideal.span_le]
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    change MvPolynomial.aeval
      (geometricQuotientRationalHomogeneousAffinePoint w) (X 0 - C 1) = 0
    simp [geometricQuotientRationalHomogeneousAffinePoint,
      quotientRationalHomogeneousAffinePoint]

/-- A normalized quotient point on `I` also annihilates the radical of its
literal first-chart ideal. -/
theorem geometricQuotientPoint_mem_qbarFirstAffineChartReducedIdeal
    (I : Ideal (MvPolynomial (Fin 13) Qbar)) (w : IntVector 12)
    (hw : geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus I) :
    geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus (qbarFirstAffineChartReducedIdeal I) := by
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
  apply (RingHom.ker_isPrime
    (MvPolynomial.eval
      (geometricQuotientRationalHomogeneousAffinePoint w))).radical_le_iff.mpr
  have hraw := geometricQuotientPoint_mem_qbarFirstAffineChartIdeal I w hw
  rw [mem_affineIdealZeroLocus_iff_le_ker_aeval] at hraw
  exact hraw

/-- Kernel counting step: a displayed `D`-element spanning family for the
first-chart coordinate algebra bounds every finite set of normalized
integral quotient points on that chart by `D`. -/
theorem card_le_of_geometricQuotientPoints_mem_firstChart_of_span
    (I : Ideal (MvPolynomial (Fin 13) Qbar))
    (S : Finset (IntVector 12)) (D : ℕ)
    (hzero : ∀ w ∈ S,
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus I)
    (spanningFamily : Fin D →
      (MvPolynomial (Fin 13) Qbar ⧸ qbarFirstAffineChartReducedIdeal I))
    (hspan : Submodule.span Qbar (Set.range spanningFamily) = ⊤) :
    S.card ≤ D := by
  classical
  let A := MvPolynomial (Fin 13) Qbar ⧸ qbarFirstAffineChartReducedIdeal I
  let pointHom : {w // w ∈ S} → (A →ₐ[Qbar] Qbar) := fun w ↦
    affineIdealPointToQuotientAlgHom (qbarFirstAffineChartReducedIdeal I)
      ⟨geometricQuotientRationalHomogeneousAffinePoint w.1,
        geometricQuotientPoint_mem_qbarFirstAffineChartReducedIdeal I w.1
          (hzero w.1 w.2)⟩
  have hinjective : Function.Injective pointHom := by
    intro w z hwz
    apply Subtype.ext
    apply geometricQuotientRationalHomogeneousAffinePoint_injective
    dsimp only [pointHom] at hwz
    have hpoint :
        (⟨geometricQuotientRationalHomogeneousAffinePoint w.1,
          geometricQuotientPoint_mem_qbarFirstAffineChartReducedIdeal I w.1
            (hzero w.1 w.2)⟩ :
          {x // x ∈ affineIdealZeroLocus
            (qbarFirstAffineChartReducedIdeal I)}) =
        ⟨geometricQuotientRationalHomogeneousAffinePoint z.1,
          geometricQuotientPoint_mem_qbarFirstAffineChartReducedIdeal I z.1
            (hzero z.1 z.2)⟩ :=
      (affineIdealZeroLocusEquivQuotientAlgHom
        (qbarFirstAffineChartReducedIdeal I)).injective hwz
    exact congrArg (fun x => x.1) hpoint
  have hfiniteA : Module.Finite Qbar A := Module.finite_def.mpr <|
    Submodule.fg_iff_exists_fin_generating_family.mpr
      ⟨D, spanningFamily, hspan⟩
  letI : Module.Finite Qbar A := hfiniteA
  calc
    S.card = Nat.card {w // w ∈ S} := by
      simp
    _ ≤ Nat.card (A →ₐ[Qbar] Qbar) :=
      Nat.card_le_card_of_injective pointHom hinjective
    _ ≤ Module.finrank Qbar A := card_algHom_le_finrank Qbar A Qbar
    _ ≤ D := by
      simpa [A] using finrank_le_of_span_eq_top hspan

/-- Bezout plus the preceding injection bounds normalized rational points
on two fixed distinct geometric curves by the product of their degrees. -/
theorem card_geometricQuotientPoints_on_distinct_curves_le_degree_mul
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    (P Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (hPprime : P.IsPrime) (hQprime : Q.IsPrime)
    (hPhomogeneous : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar))
    (hQhomogeneous : Q.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar))
    {d e : ℕ} (hPdegree : HasProjectiveDimensionDegree P 1 d)
    (hQdegree : HasProjectiveDimensionDegree Q 1 e)
    (hne : P ≠ Q) (S : Finset (IntVector 12))
    (hzero : ∀ w ∈ S,
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus (P ⊔ Q)) :
    S.card ≤ d * e := by
  obtain ⟨spanningFamily, hspan⟩ :=
    hBezout 12 d e P Q hPprime hQprime hPhomogeneous hQhomogeneous
      hPdegree hQdegree hne
  exact card_le_of_geometricQuotientPoints_mem_firstChart_of_span
    (P ⊔ Q) S (d * e) hzero spanningFamily hspan

/-! ## Static node component lists at one residue -/

/-- The literal node-component list determined before choosing a point, at
one modulus and residue.  It is empty when the packet is ineligible. -/
def isolatedVertexQuotientStaticNodeComponentsAtResidue
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
  if heligible : IsEligibleIsolatedVertexQuotientPacket
      U p x₀ sourceEquations CF lowerEquations q.1 rho then
    integralIsolatedVertexQuotientNodeComponents lowerEquations
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ)
      (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
      (selectedIntegralIsolatedVertexQuotientPacketPlane
        U p x₀ sourceEquations CF lowerEquations hquotient
        q.1 (hqpos q) (hqsf q) (hqlower q) rho heligible).matrix
  else ∅

/-- Every nonempty static label belongs to the residue-determined node list,
passes through the point, and is a retained nonradial curve. -/
theorem isolatedVertexQuotientStaticComponentLabel_eq_some_staticNode_spec
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (x₀ : IntVector 13)
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
    (w : IntVector 12) (q : ReservoirModulus Ppool k)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (hlabel : isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower w q = some Q) :
    Q ∈ isolatedVertexQuotientStaticNodeComponentsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q (integralResidueVector w) ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus Q ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) Q := by
  unfold isolatedVertexQuotientStaticComponentLabel at hlabel
  dsimp only at hlabel
  split at hlabel
  next heligible =>
    have hspec := integralQuotientPacketPriorityLabel_eq_some_spec
      lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
        (p.m : ℤ) (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
        (selectedIntegralIsolatedVertexQuotientPacketPlane
          U p x₀ sourceEquations CF lowerEquations hquotient
          q.1 (hqpos q) (hqsf q) (hqlower q)
          (integralResidueVector w) heligible) w hlabel
    refine ⟨?_, hspec.2.1, hspec.2.2.1⟩
    simp only [isolatedVertexQuotientStaticNodeComponentsAtResidue,
      dif_pos heligible]
    exact hspec.1
  next heligible => simp at hlabel

/-- Bezout degree mass on the four-plane section bounds the number of
actual node components at every static residue. -/
theorem card_isolatedVertexQuotientStaticNodeComponentsAtResidue_le_degree
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
    (isolatedVertexQuotientStaticNodeComponentsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho).card ≤ degree := by
  classical
  unfold isolatedVertexQuotientStaticNodeComponentsAtResidue
  split
  next heligible =>
    let plane := selectedIntegralIsolatedVertexQuotientPacketPlane
      U p x₀ sourceEquations CF lowerEquations hquotient
      q.1 (hqpos q) (hqsf q) (hqlower q) rho heligible
    have hAq : (qbarIntMatrix plane.matrix).rank = 4 :=
      (qbarIntMatrix_rank plane.matrix).trans plane.rank_matrix
    obtain ⟨componentDimension, componentDegree, hcomponents, hdegree⟩ :=
      hMass (geometricIsolatedVertexLowerIdeal lowerEquations)
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ))
        (qbarIntCast_ne_zero
          (by exact_mod_cast (Nat.ne_of_gt p.one_le_m)))
        (qbarIntMatrix plane.matrix) degree hJprime hJhomogeneous
        hJHilbert hAq
    apply Finset.card_le_of_sum_positive_mass _ componentDegree degree
    · intro Q hQ
      exact (hcomponents Q hQ).2.2.1
    · exact hdegree
  next _ => simp

/-- A retained component in one static node list has literal curve Hilbert
data of degree at most the degree of the quotient fivefold. -/
theorem isolatedVertexQuotientStaticNodeComponent_retained_degree_le
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
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {Ppool : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q : ReservoirModulus Ppool k) (rho : Fin 12 → ZMod q.1)
    (Q : Ideal (MvPolynomial (Fin 13) Qbar))
    (hQ : Q ∈ isolatedVertexQuotientStaticNodeComponentsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q rho)
    (hretained : IsRetainedNonradialQuotientNodeComponent
      (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
      (algebraMap ℚ Qbar (p.m : ℚ)) Q) :
    ∃ d : ℕ, HasProjectiveDimensionDegree Q 1 d ∧ d ≤ degree := by
  classical
  unfold isolatedVertexQuotientStaticNodeComponentsAtResidue at hQ
  split at hQ
  next heligible =>
    let plane := selectedIntegralIsolatedVertexQuotientPacketPlane
      U p x₀ sourceEquations CF lowerEquations hquotient
      q.1 (hqpos q) (hqsf q) (hqlower q) rho heligible
    have hAq : (qbarIntMatrix plane.matrix).rank = 4 :=
      (qbarIntMatrix_rank plane.matrix).trans plane.rank_matrix
    obtain ⟨componentDimension, componentDegree, hcomponents, hdegree⟩ :=
      hMass (geometricIsolatedVertexLowerIdeal lowerEquations)
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ))
        (qbarIntCast_ne_zero
          (by exact_mod_cast (Nat.ne_of_gt p.one_le_m)))
        (qbarIntMatrix plane.matrix) degree hJprime hJhomogeneous
        hJHilbert hAq
    have hcomponent := hcomponents Q hQ
    obtain ⟨s, e, hcurve⟩ := hretained
    have hs : s = 1 := hcurve.2.2.1
    have hdimension : componentDimension Q = 1 := by
      have hmassDim := hcomponent.2.1
      have hcurveDim := hcurve.2.1.1
      rw [hs] at hcurveDim
      rw [hmassDim] at hcurveDim
      have hnat : componentDimension Q + 1 = 1 + 1 := by
        exact_mod_cast hcurveDim
      omega
    have hdegreeQ : componentDegree Q ≤ degree :=
      (Finset.single_le_sum
        (fun R _hR => Nat.zero_le (componentDegree R)) hQ).trans hdegree
    exact ⟨componentDegree Q, by simpa [hdimension] using hcomponent.2,
      hdegreeQ⟩
  next heligible => simp at hQ

/-! ## Literal directed-edge records -/

structure IsolatedVertexQuotientStaticEdgeRecord (R : ℕ) where
  residue : Fin 12 → ZMod R
  leftComponent : Ideal (MvPolynomial (Fin 13) Qbar)
  rightComponent : Ideal (MvPolynomial (Fin 13) Qbar)

/-- All pairs of static node components over the two reductions of one lcm
residue. -/
def isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
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
    (q r : ReservoirModulus Ppool k)
    (rho : Fin 12 → ZMod (Nat.lcm q.1 r.1)) :
    Finset (IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1)) := by
  classical
  exact (isolatedVertexQuotientStaticNodeComponentsAtResidue
    U p x₀ sourceEquations CF lowerEquations hquotient hqpos hqsf hqlower q
      (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).biUnion fun Qq =>
    (isolatedVertexQuotientStaticNodeComponentsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient hqpos hqsf hqlower r
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).image fun Qr =>
      { residue := rho, leftComponent := Qq, rightComponent := Qr }

@[simp]
theorem mem_isolatedVertexQuotientStaticEdgeRecordPairsAtResidue_iff
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
    (q r : ReservoirModulus Ppool k)
    (rho : Fin 12 → ZMod (Nat.lcm q.1 r.1))
    (record : IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1)) :
    record ∈ isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q r rho ↔
      record.residue = rho ∧
      record.leftComponent ∈
        isolatedVertexQuotientStaticNodeComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q
            (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho) ∧
      record.rightComponent ∈
        isolatedVertexQuotientStaticNodeComponentsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower r
            (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho) := by
  classical
  constructor
  · intro hrecord
    obtain ⟨Qq, hQq, himage⟩ := Finset.mem_biUnion.mp hrecord
    obtain ⟨Qr, hQr, hEq⟩ := Finset.mem_image.mp himage
    cases hEq
    exact ⟨rfl, hQq, hQr⟩
  · rintro ⟨hresidue, hleft, hright⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨record.leftComponent, hleft, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨record.rightComponent, hright, ?_⟩
    cases record
    simp_all

/-- The finite record list actually needed by one edge cell.  It is indexed
by occupied lcm residues and retains only distinct nonradial curve pairs. -/
def occupiedIsolatedVertexQuotientStaticEdgeRecords
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    Finset (IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1)) := by
  classical
  exact (occupiedIntegralResidues (Nat.lcm q.1 r.1)
    (isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r)).biUnion fun rho =>
    (isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q r rho).filter fun record =>
      record.leftComponent ≠ record.rightComponent ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) record.leftComponent ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) record.rightComponent

/-- Points of the edge cell in one literal residue/component record. -/
def isolatedVertexQuotientStaticEdgeRecordPointCell
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q r : ReservoirModulus Ppool k}
    (record : IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1)) : Finset (IntVector 12) :=
  (isolatedVertexQuotientDenominatorCompatibleEdgeCell
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hP hqpos hqsf hqlower q r).filter fun w =>
    (integralResidueVector w : Fin 12 → ZMod (Nat.lcm q.1 r.1)) =
        record.residue ∧
    geometricQuotientRationalHomogeneousAffinePoint w ∈
      affineIdealZeroLocus
        (record.leftComponent ⊔ record.rightComponent)

/-- Every point of the unequal-label edge cell belongs to one occupied
lcm-residue/component-pair record cell. -/
theorem isolatedVertexQuotientDenominatorCompatibleEdgeCell_subset_recordUnion
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
      (occupiedIsolatedVertexQuotientStaticEdgeRecords
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r).biUnion fun record =>
        isolatedVertexQuotientStaticEdgeRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower record := by
  classical
  intro w hw
  obtain ⟨hwRegular, _hqSurvives, _hrSurvives, _hadj,
      hlabelsNe, hqNonempty, hrNonempty⟩ := Finset.mem_filter.mp hw
  obtain ⟨Qq, hQqLabel⟩ := Option.ne_none_iff_exists'.1 hqNonempty
  obtain ⟨Qr, hQrLabel⟩ := Option.ne_none_iff_exists'.1 hrNonempty
  have hQqSpec :=
    isolatedVertexQuotientStaticComponentLabel_eq_some_staticNode_spec
      U p sourceEquations CF x₀ lowerEquations hquotient
        hqpos hqsf hqlower w q Qq hQqLabel
  have hQrSpec :=
    isolatedVertexQuotientStaticComponentLabel_eq_some_staticNode_spec
      U p sourceEquations CF x₀ lowerEquations hquotient
        hqpos hqsf hqlower w r Qr hQrLabel
  have hne : Qq ≠ Qr := by
    intro hEq
    apply hlabelsNe
    rw [hQqLabel, hQrLabel, hEq]
  let rho : Fin 12 → ZMod (Nat.lcm q.1 r.1) := integralResidueVector w
  let record : IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1) :=
    { residue := rho, leftComponent := Qq, rightComponent := Qr }
  have hoccupied : rho ∈ occupiedIntegralResidues (Nat.lcm q.1 r.1)
      (isolatedVertexQuotientDenominatorCompatibleEdgeCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r) := by
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hpair : record ∈
      isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q r rho := by
    apply (mem_isolatedVertexQuotientStaticEdgeRecordPairsAtResidue_iff
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q r rho record).2
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [rho, reduceResidueVector_integralResidueVector] using
        hQqSpec.1
    · simpa only [rho, reduceResidueVector_integralResidueVector] using
        hQrSpec.1
  have hrecord : record ∈ occupiedIsolatedVertexQuotientStaticEdgeRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r := by
    apply Finset.mem_biUnion.mpr
    refine ⟨rho, hoccupied, Finset.mem_filter.mpr ?_⟩
    exact ⟨hpair, hne, hQqSpec.2.2, hQrSpec.2.2⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨record, hrecord, Finset.mem_filter.mpr ⟨hw, rfl, ?_⟩⟩
  rw [mem_affineIdealZeroLocus_iff]
  have hqle : Qq ≤ RingHom.ker
      (MvPolynomial.eval
        (geometricQuotientRationalHomogeneousAffinePoint w)) := by
    intro f hf
    exact RingHom.mem_ker.mpr (hQqSpec.2.1 f hf)
  have hrle : Qr ≤ RingHom.ker
      (MvPolynomial.eval
        (geometricQuotientRationalHomogeneousAffinePoint w)) := by
    intro f hf
    exact RingHom.mem_ker.mpr (hQrSpec.2.1 f hf)
  exact sup_le hqle hrle

/-- Cardinal form of the literal edge-record cover. -/
theorem card_isolatedVertexQuotientDenominatorCompatibleEdgeCell_le_sum_recordCells
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    (isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r).card ≤
      ∑ record ∈ occupiedIsolatedVertexQuotientStaticEdgeRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r,
        (isolatedVertexQuotientStaticEdgeRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower record).card := by
  calc
    _ ≤ ((occupiedIsolatedVertexQuotientStaticEdgeRecords
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r).biUnion fun record =>
          isolatedVertexQuotientStaticEdgeRecordPointCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower record).card :=
      Finset.card_le_card
        (isolatedVertexQuotientDenominatorCompatibleEdgeCell_subset_recordUnion
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r)
    _ ≤ _ := Finset.card_biUnion_le

/-- Each literal edge record contains at most `degree²` normalized points.
The finite bound is obtained from the chart-coordinate-algebra Bezout rank,
not from a point-count hypothesis. -/
theorem card_isolatedVertexQuotientStaticEdgeRecordPointCell_le_degree_sq
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    {q r : ReservoirModulus Ppool k}
    (record : IsolatedVertexQuotientStaticEdgeRecord
      (Nat.lcm q.1 r.1))
    (hrecord : record ∈ occupiedIsolatedVertexQuotientStaticEdgeRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r) :
    (isolatedVertexQuotientStaticEdgeRecordPointCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower record).card ≤ degree * degree := by
  classical
  obtain ⟨rho, _hrho, hfiltered⟩ := Finset.mem_biUnion.mp hrecord
  obtain ⟨hpair, hne, hleftRetained, hrightRetained⟩ :=
    Finset.mem_filter.mp hfiltered
  obtain ⟨hrecordResidue, hleftMem, hrightMem⟩ :=
    (mem_isolatedVertexQuotientStaticEdgeRecordPairsAtResidue_iff
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q r rho record).1 hpair
  obtain ⟨dleft, hleftDegree, hdleft⟩ :=
    isolatedVertexQuotientStaticNodeComponent_retained_degree_le
      hMass U p sourceEquations CF x₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
        q (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)
        record.leftComponent hleftMem hleftRetained
  obtain ⟨dright, hrightDegree, hdright⟩ :=
    isolatedVertexQuotientStaticNodeComponent_retained_degree_le
      hMass U p sourceEquations CF x₀ lowerEquations hJprime
        hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
        r (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)
        record.rightComponent hrightMem hrightRetained
  obtain ⟨sleft, eleft, hleftCurve⟩ := hleftRetained
  obtain ⟨sright, eright, hrightCurve⟩ := hrightRetained
  have hcard :=
    card_geometricQuotientPoints_on_distinct_curves_le_degree_mul
      hBezout record.leftComponent record.rightComponent
        hleftCurve.1.1 hrightCurve.1.1 hleftCurve.1.2 hrightCurve.1.2
        hleftDegree hrightDegree hne
        (isolatedVertexQuotientStaticEdgeRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower record) (by
          intro w hw
          exact (Finset.mem_filter.mp hw).2.2)
  exact hcard.trans (Nat.mul_le_mul hdleft hdright)

/-- The full component-pair envelope over one lcm residue has cardinality
at most the product of the two static node-component cardinalities. -/
theorem card_isolatedVertexQuotientStaticEdgeRecordPairsAtResidue_le
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
    (q r : ReservoirModulus Ppool k)
    (rho : Fin 12 → ZMod (Nat.lcm q.1 r.1)) :
    (isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
      U p x₀ sourceEquations CF lowerEquations hquotient
        hqpos hqsf hqlower q r rho).card ≤
      (isolatedVertexQuotientStaticNodeComponentsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower q
          (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)).card *
      (isolatedVertexQuotientStaticNodeComponentsAtResidue
        U p x₀ sourceEquations CF lowerEquations hquotient
          hqpos hqsf hqlower r
          (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)).card := by
  classical
  let left := isolatedVertexQuotientStaticNodeComponentsAtResidue
    U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower q
      (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho)
  let right := isolatedVertexQuotientStaticNodeComponentsAtResidue
    U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower r
      (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho)
  change (left.biUnion fun Qq => right.image fun Qr =>
      IsolatedVertexQuotientStaticEdgeRecord.mk rho Qq Qr).card ≤
    left.card * right.card
  calc
    _ ≤ ∑ Qq ∈ left,
        (right.image fun Qr =>
          IsolatedVertexQuotientStaticEdgeRecord.mk rho Qq Qr).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _Qq ∈ left, right.card := by
      apply Finset.sum_le_sum
      intro Qq _hQq
      exact Finset.card_image_le
    _ = left.card * right.card := by simp

/-- The number of occupied distinct retained curve-pair records over one
directed edge is at most `degree²` times its number of occupied lcm
residues. -/
theorem card_occupiedIsolatedVertexQuotientStaticEdgeRecords_le
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    (occupiedIsolatedVertexQuotientStaticEdgeRecords
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r).card ≤
      (occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (isolatedVertexQuotientDenominatorCompatibleEdgeCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r)).card * (degree * degree) := by
  classical
  let residues := occupiedIntegralResidues (Nat.lcm q.1 r.1)
    (isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r)
  calc
    _ ≤ ∑ rho ∈ residues,
        ((isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q r rho).filter fun record =>
          record.leftComponent ≠ record.rightComponent ∧
          IsRetainedNonradialQuotientNodeComponent
            (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
            (algebraMap ℚ Qbar (p.m : ℚ)) record.leftComponent ∧
          IsRetainedNonradialQuotientNodeComponent
            (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
            (algebraMap ℚ Qbar (p.m : ℚ)) record.rightComponent).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _rho ∈ residues, degree * degree := by
      apply Finset.sum_le_sum
      intro rho _hrho
      calc
        _ ≤ (isolatedVertexQuotientStaticEdgeRecordPairsAtResidue
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q r rho).card := Finset.card_filter_le _ _
        _ ≤ _ := card_isolatedVertexQuotientStaticEdgeRecordPairsAtResidue_le
          U p x₀ sourceEquations CF lowerEquations hquotient
            hqpos hqsf hqlower q r rho
        _ ≤ degree * degree := Nat.mul_le_mul
          (card_isolatedVertexQuotientStaticNodeComponentsAtResidue_le_degree
            hMass U p sourceEquations CF x₀ lowerEquations hJprime
              hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
              q (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) rho))
          (card_isolatedVertexQuotientStaticNodeComponentsAtResidue_le_degree
            hMass U p sourceEquations CF x₀ lowerEquations hJprime
              hJhomogeneous degree hJHilbert hquotient hqpos hqsf hqlower
              r (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) rho))
    _ = residues.card * (degree * degree) := by simp

/-- One denominator-compatible directed edge cell is bounded by its number
of occupied lcm packets times `degree⁴`.  The extra square is the finite
number of possible component pairs; each fixed pair costs at most
`degree²` by Bezout. -/
theorem card_isolatedVertexQuotientDenominatorCompatibleEdgeCell_le_occupied_mul_degree_four
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
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
    (hP : ∀ s ∈ Ppool, s.Prime)
    (hqpos : ∀ q : ReservoirModulus Ppool k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus Ppool k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus Ppool k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (q r : ReservoirModulus Ppool k) :
    (isolatedVertexQuotientDenominatorCompatibleEdgeCell
      U p sourceEquations CF hx₀ lowerEquations model hquotient
        hP hqpos hqsf hqlower q r).card ≤
      (occupiedIntegralResidues (Nat.lcm q.1 r.1)
        (isolatedVertexQuotientDenominatorCompatibleEdgeCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower q r)).card *
        ((degree * degree) * (degree * degree)) := by
  let records := occupiedIsolatedVertexQuotientStaticEdgeRecords
    U p sourceEquations CF hx₀ lowerEquations model hquotient
      hP hqpos hqsf hqlower q r
  calc
    _ ≤ ∑ record ∈ records,
        (isolatedVertexQuotientStaticEdgeRecordPointCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower record).card :=
      card_isolatedVertexQuotientDenominatorCompatibleEdgeCell_le_sum_recordCells
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower q r
    _ ≤ ∑ _record ∈ records, degree * degree := by
      apply Finset.sum_le_sum
      intro record hrecord
      exact card_isolatedVertexQuotientStaticEdgeRecordPointCell_le_degree_sq
        hMass hBezout U p sourceEquations CF hx₀ lowerEquations hJprime
          hJhomogeneous degree hJHilbert model hquotient
          hP hqpos hqsf hqlower record hrecord
    _ = records.card * (degree * degree) := by simp
    _ ≤ (occupiedIntegralResidues (Nat.lcm q.1 r.1)
          (isolatedVertexQuotientDenominatorCompatibleEdgeCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower q r)).card *
        (degree * degree) * (degree * degree) :=
      Nat.mul_le_mul_right (degree * degree)
        (card_occupiedIsolatedVertexQuotientStaticEdgeRecords_le
          hMass U p sourceEquations CF hx₀ lowerEquations hJprime
            hJhomogeneous degree hJHilbert model hquotient
            hP hqpos hqsf hqlower q r)
    _ = _ := by ring

/-- The complete directed-edge contribution satisfies the occurrence-scale
bound with the explicit Bezout factor `degree⁴`. -/
theorem isolatedVertexQuotient_denominatorCompatible_directedEdge_card_cast_le_scale
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hBezout : StandardAG.QbarDistinctProjectiveCurveFirstChartBezout)
    {M₀ δ C₀ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ) (hC₀ : 0 ≤ C₀)
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
    (∑ qr : ↑(modulusReservoirDirectedEdges Ppool k hP),
      ((isolatedVertexQuotientDenominatorCompatibleEdgeCell
        U p sourceEquations CF hx₀ lowerEquations model hquotient
          hP hqpos hqsf hqlower qr.1.1 qr.1.2).card : ℝ)) ≤
      (degree : ℝ) ^ 4 *
        (2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ)) := by
  let edgeOccurrence : ℝ :=
    ∑ qr : ↑(modulusReservoirDirectedEdges Ppool k hP),
      ((occupiedIntegralResidues
        (Nat.lcm qr.1.1.1 qr.1.2.1)
        (isolatedVertexQuotientDenominatorCompatibleEdgeCell
          U p sourceEquations CF hx₀ lowerEquations model hquotient
            hP hqpos hqsf hqlower qr.1.1 qr.1.2)).card : ℝ)
  have hoccurrence :=
    isolatedVertexQuotient_denominatorCompatible_static_node_edge_occupiedResidues_cast_le_scale
      hM₀ hδ hC₀ U p sourceEquations CF hx₀ lowerEquations model
        hquotient Ppool k hP hqpos hqsf hqlower hk h2k hH hfamily
        hupperNode hupperEdge
  have hedgeOccurrence : edgeOccurrence ≤
      2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ) := by
    apply le_trans _ hoccurrence
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => by positivity)
  calc
    _ ≤ ∑ qr : ↑(modulusReservoirDirectedEdges Ppool k hP),
        ((occupiedIntegralResidues
          (Nat.lcm qr.1.1.1 qr.1.2.1)
          (isolatedVertexQuotientDenominatorCompatibleEdgeCell
            U p sourceEquations CF hx₀ lowerEquations model hquotient
              hP hqpos hqsf hqlower qr.1.1 qr.1.2)).card : ℝ) *
          (degree : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro qr _hqr
      have hlocal :=
        card_isolatedVertexQuotientDenominatorCompatibleEdgeCell_le_occupied_mul_degree_four
          hMass hBezout U p sourceEquations CF hx₀ lowerEquations
            hJprime hJhomogeneous degree hJHilbert model hquotient
            hP hqpos hqsf hqlower qr.1.1 qr.1.2
      have hfactor :
          (degree * degree) * (degree * degree) = degree ^ 4 := by ring
      rw [hfactor] at hlocal
      exact_mod_cast hlocal
    _ = (degree : ℝ) ^ 4 * edgeOccurrence := by
      simp only [edgeOccurrence]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro qr _hqr
      ring
    _ ≤ (degree : ℝ) ^ 4 *
        (2 * C₀ ^ 5 * p.T ^ (45 / 13 : ℝ) * p.H ^ (7 * δ)) :=
      mul_le_mul_of_nonneg_left hedgeOccurrence (by positivity)

end

end TranslatedDepthSeven
