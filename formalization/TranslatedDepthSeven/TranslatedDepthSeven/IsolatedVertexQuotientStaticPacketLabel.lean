import TranslatedDepthSeven.IsolatedVertexQuotientStaticCertificate
import TranslatedDepthSeven.IsolatedVertexQuotientFourClassAggregation

/-!
# Static quotient packet planes and component labels

For each eligible occupied pair `(q, rho)` this file chooses one integral
four-plane from the actual residue packet.  The choice is made from the pair,
not from a later point in the packet.  On the resulting quotient node the
label first tests whether the point lies on a zero-dimensional or radial
component; only if it does not does it retain one actual nonradial component.
Thus the nonempty labels are literal geometric component ideals, while the
empty label keeps the elementary zero/radial alternatives ahead of them.

No component count or rational-point estimate is used.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

local instance isolatedVertexQuotientStaticPacketPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The exact condition on an occupied pair needed by the tangent-packet
lemma. -/
def IsEligibleIsolatedVertexQuotientPacket
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (q : ℕ) (rho : Fin 12 → ZMod q) : Prop :=
  ∃ hrho : rho ∈ occupiedIntegralResidues q
      (isolatedVertexQuotientPointFinset U p x₀ sourceEquations CF),
    ∀ l, l.Prime → l ∣ q →
      7 ≤ (jacobianMatrix
        (indexedFinsetFamily
          (isolatedVertexQuotientAffineEquationFinset
            U p x₀ lowerEquations))
        (integralResiduePacketBase
          (isolatedVertexQuotientPointFinset
            U p x₀ sourceEquations CF) rho
          hrho) l).rank

/-- One literal integral four-plane selected from an eligible occupied pair.
All mathematical data depend only on `(q,rho)` and the fixed ambient data;
proof irrelevance removes any dependence on the eligibility witness. -/
def selectedIntegralIsolatedVertexQuotientPacketPlane
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    (q : ℕ) (hqpos : 0 < q) (hqsf : Squarefree q)
    (hqlower : manuscriptReservoirTarget
      (isolatedVertexQuotientReservoirConstant U : ℝ)
      p.T (9 / 13) ≤ q)
    (rho : Fin 12 → ZMod q)
    (heligible : IsEligibleIsolatedVertexQuotientPacket
      U p x₀ sourceEquations CF lowerEquations q rho) :
    IntegralIsolatedVertexQuotientPacketPlane
      (isolatedVertexQuotientPointFinset
        U p x₀ sourceEquations CF)
      q (isolatedVertexTransformedNaturalSide U p) rho :=
  Classical.choice
    (nonempty_integralIsolatedVertexQuotientPacketPlane_for_occupied_packet
      U p x₀ sourceEquations CF
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations)
      hquotient q hqpos hqsf hqlower rho
      heligible.choose heligible.choose_spec)

/-- Avoiding the selected point certificate makes the residue packet of
that point eligible.  This is the precise point-to-pair bridge. -/
theorem isEligibleIsolatedVertexQuotientPacket_of_survives
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    {P : Finset ℕ} {k : ℕ}
    (q : ReservoirModulus P k)
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations)
    (hsurvives : survivesTwoCertificates q (p.m : ℤ)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w)) :
    IsEligibleIsolatedVertexQuotientPacket
      U p x₀ sourceEquations CF lowerEquations q.1
        (integralResidueVector w) := by
  let Z := isolatedVertexQuotientPointFinset
    U p x₀ sourceEquations CF
  let equationsT := isolatedVertexQuotientAffineEquationFinset
    U p x₀ lowerEquations
  let C := selectedIsolatedVertexQuotientJacobianCertificate
    U p sourceEquations CF hx₀ lowerEquations w hw
  have hwPoint : w ∈ Z := by
    exact (mem_isolatedVertexRegularQuotientPointFinset_iff
      U p x₀ sourceEquations CF lowerEquations w).1 hw |>.1
  have hrho : (integralResidueVector w : Fin 12 → ZMod q.1) ∈
      occupiedIntegralResidues q.1 Z := by
    exact mem_occupiedIntegralResidues_iff.mpr ⟨w, hwPoint, rfl⟩
  refine ⟨hrho, ?_⟩
  have hwPacket : w ∈ integralResiduePacket Z
      (integralResidueVector w : Fin 12 → ZMod q.1) :=
    mem_integralResiduePacket_iff.mpr ⟨hwPoint, rfl⟩
  have hbasePacket : integralResiduePacketBase Z
      (integralResidueVector w : Fin 12 → ZMod q.1) hrho ∈
        integralResiduePacket Z
          (integralResidueVector w : Fin 12 → ZMod q.1) :=
    integralResiduePacketBase_mem Z _ hrho
  have hcongr : IntVectorCongruent q.1 w
      (integralResiduePacketBase Z
        (integralResidueVector w : Fin 12 → ZMod q.1) hrho) :=
    intVectorCongruent_of_mem_same_integralResiduePacket
      hwPacket hbasePacket
  have hcopAtW : Nat.Coprime q.1
      (MvPolynomial.eval w
        (integralJacobianMinorPolynomial
          (indexedFinsetFamily equationsT) C.rows C.cols)).natAbs := by
    have hcopValue : Nat.Coprime q.1 C.value.natAbs := by
      have h := hsurvives.2
      rw [isolatedVertexQuotientSelectedCertificateValue_eq
        U p sourceEquations CF hx₀ lowerEquations hw] at h
      exact h
    simpa only [C, equationsT,
      IsolatedVertexQuotientJacobianCertificate.value,
      eval_integralJacobianMinorPolynomial] using hcopValue
  have hcopBase : Nat.Coprime q.1
      (integralJacobianMinor
        (indexedFinsetFamily equationsT)
        (integralResiduePacketBase Z
          (integralResidueVector w : Fin 12 → ZMod q.1) hrho)
        C.rows C.cols).natAbs := by
    have hcopEval := coprime_eval_natAbs_of_coordinate_cast_eq
      (integralJacobianMinorPolynomial
        (indexedFinsetFamily equationsT) C.rows C.cols)
      w (integralResiduePacketBase Z
        (integralResidueVector w : Fin 12 → ZMod q.1) hrho)
      hcongr hcopAtW
    simpa only [eval_integralJacobianMinorPolynomial] using hcopEval
  intro l hl hldvd
  exact jacobian_rank_ge_for_prime_divisors_of_coprime_minor
    (indexedFinsetFamily equationsT)
    (integralResiduePacketBase Z
      (integralResidueVector w : Fin 12 → ZMod q.1) hrho)
    C.rows C.cols hcopBase l hl hldvd

/-- An integral quotient point satisfying the displayed transformed lower
equations satisfies the original lower equations at `b + m w`. -/
theorem integralCommonZero_lower_of_mem_regularQuotient
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations) :
    IntegralCommonZero lowerEquations
      (integralQuotientAffinePoint
        (dropFirstIntVector (U.pointEquiv x₀)) w (p.m : ℤ)) := by
  have hwPoint := (mem_isolatedVertexRegularQuotientPointFinset_iff
    U p x₀ sourceEquations CF lowerEquations w).1 hw |>.1
  have hwZero : IntegralCommonZero
      (isolatedVertexQuotientAffineEquationFinset
        U p x₀ lowerEquations) w :=
    (mem_integralCommonZeroInBox_iff _ w).1 (hquotient hwPoint) |>.2
  exact (integralCommonZero_transform_iff
    (dropFirstIntVector (U.pointEquiv x₀)) w p.m lowerEquations).1 hwZero

/-- A component through a point is elementary if it is zero-dimensional or
the radial line, with literal Hilbert data. -/
def IsElementaryQuotientNodeComponent
    (b : Fin 12 → Qbar) (m : Qbar)
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) : Prop :=
  ∃ s e : ℕ,
    IsZeroDimensionalQuotientNodeComponent P s e ∨
      IsRadialQuotientNodeLine b m P s e

/-- A literal nonradial curve component, with its dimension and degree
witnesses retained existentially. -/
def IsRetainedNonradialQuotientNodeComponent
    (b : Fin 12 → Qbar) (m : Qbar)
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) : Prop :=
  ∃ s e : ℕ, IsNonradialIntegralQuotientNodeCurve b m P s e

/-- Actual node components through one displayed quotient point. -/
def integralQuotientNodeComponentsThroughPoint
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12) :
    Finset (Ideal (MvPolynomial (Fin 13) Qbar)) := by
  classical
  exact (integralIsolatedVertexQuotientNodeComponents
    lowerEquations b m hm plane.matrix).filter fun P ↦
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P

/-- The subset of the through-point list consisting of retained nonradial
curves. -/
def retainedNonradialQuotientNodeComponentsThroughPoint
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12) :
    Finset (Ideal (MvPolynomial (Fin 13) Qbar)) := by
  classical
  exact (integralQuotientNodeComponentsThroughPoint
    lowerEquations b m hm plane w).filter fun P ↦
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P

/-- The static priority label on one chosen packet plane.  Any elementary
component through the point forces `none`; otherwise one actual nonradial
curve through the point is retained when such a curve exists. -/
def integralQuotientPacketPriorityLabel
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12) :
    Option (Ideal (MvPolynomial (Fin 13) Qbar)) :=
  if helementary : ∃ P ∈ integralQuotientNodeComponentsThroughPoint
      lowerEquations b m hm plane w,
      IsElementaryQuotientNodeComponent
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P then
    none
  else
    let candidates := retainedNonradialQuotientNodeComponentsThroughPoint
      lowerEquations b m hm plane w
    if hnonradial : candidates.Nonempty then some hnonradial.choose else none

/-- A nonempty priority label is an actual node component through the point,
is a nonradial curve, and occurs only after the elementary alternatives have
been excluded. -/
theorem integralQuotientPacketPriorityLabel_eq_some_spec
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    {Z : Finset (IntVector 12)} {q R : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q R rho)
    (w : IntVector 12)
    {P : Ideal (MvPolynomial (Fin 13) Qbar)}
    (hlabel : integralQuotientPacketPriorityLabel
      lowerEquations b m hm plane w = some P) :
    P ∈ integralIsolatedVertexQuotientNodeComponents
        lowerEquations b m hm plane.matrix ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P ∧
      ¬ ∃ Q ∈ integralQuotientNodeComponentsThroughPoint
          lowerEquations b m hm plane w,
        IsElementaryQuotientNodeComponent
          (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) Q := by
  classical
  unfold integralQuotientPacketPriorityLabel at hlabel
  split at hlabel
  next helementary => simp at hlabel
  next helementary =>
    dsimp only at hlabel
    split at hlabel
    next hnonradial =>
      have hEq := Option.some.inj hlabel
      have hmem := hnonradial.choose_spec
      rw [hEq] at hmem
      have hspec := Finset.mem_filter.1 hmem
      have hthrough := Finset.mem_filter.1 hspec.1
      exact ⟨hthrough.1, hthrough.2, hspec.2, helementary⟩
    next hnonradial => simp at hlabel

/-- If the priority label on an actual packet point is empty, then either an
actual zero-dimensional or radial component passes through the point, or the
corresponding original projective point already lies in the literal
bounded-height exceptional locus.  Thus `none` hides no unclassified
nonradial curve.

The only geometric inputs are the three narrow textbook propositions already
used by the four-class component decomposition. -/
theorem integralQuotientPacketPriorityLabel_eq_none_implies_elementary_or_exceptional
    (hMass : StandardAG.GeometricFourPlaneSectionComponentDegreeMass)
    (hProjection :
      StandardAG.IntegralQuotientNodeOriginalSourceComponentProjection)
    (hRadial :
      StandardAG.IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne)
    (p : Parameters)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (U : IntegralUnimodularChange 13)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hfamily : U.transformEquationFinset equations =
      liftEquationFinsetAfterFirst lowerEquations)
    (CF : ℕ) (x₀ : IntVector 13)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hJprime : (geometricIsolatedVertexLowerIdeal lowerEquations).IsPrime)
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (degree : ℕ)
    (hJHilbert : Published.HasProjectiveDimensionDegree (N := 11)
      (geometricIsolatedVertexLowerIdeal lowerEquations) 4 degree)
    (hm : (p.m : ℤ) ≠ 0)
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q
      (isolatedVertexTransformedNaturalSide U p) rho)
    (w : IntVector 12) (hw : w ∈ integralResiduePacket Z rho)
    (hy : IntegralCommonZero lowerEquations
      (integralQuotientAffinePoint
        (dropFirstIntVector (U.pointEquiv x₀)) w (p.m : ℤ)))
    (x : IntVector 13) (hx : x ≠ 0)
    (hspatial : dropFirstIntVector (U.pointEquiv x) =
      integralQuotientAffinePoint
        (dropFirstIntVector (U.pointEquiv x₀)) w (p.m : ℤ))
    (hlabel : integralQuotientPacketPriorityLabel lowerEquations
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm plane w = none) :
    (∃ P ∈ integralQuotientNodeComponentsThroughPoint lowerEquations
          (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm plane w,
        IsElementaryQuotientNodeComponent
          (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
          (algebraMap ℚ Qbar (((p.m : ℤ) : ℚ))) P) ∨
      MemDepthSevenExceptionalLocus equations
        ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊
        (integralProjectiveClass x hx) := by
  classical
  by_cases helementary : ∃ P ∈ integralQuotientNodeComponentsThroughPoint
      lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
        (p.m : ℤ) hm plane w,
      IsElementaryQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (((p.m : ℤ) : ℚ))) P
  · exact Or.inl helementary
  · have hDisposition := integralQuotientPacketPointDispositionAtHeight
      hMass hProjection hRadial p equations U lowerEquations hfamily
        CF x₀ hx₀ hJprime hJhomogeneous degree hJHilbert hm
        plane w hw hy x hx hspatial
    rcases hDisposition with hzero | hradial | hnonradial | hexceptional
    · obtain ⟨P, s, e, hP, hPw, hzero⟩ := hzero
      exfalso
      apply helementary
      exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPw⟩,
        s, e, Or.inl hzero⟩
    · obtain ⟨P, s, e, hP, hPw, hradial⟩ := hradial
      exfalso
      apply helementary
      exact ⟨P, Finset.mem_filter.mpr ⟨hP, hPw⟩,
        s, e, Or.inr hradial⟩
    · obtain ⟨P, s, e, hP, hPw, hnonradial⟩ := hnonradial
      have hcandidate : P ∈
          retainedNonradialQuotientNodeComponentsThroughPoint
            lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
              (p.m : ℤ) hm plane w := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hP, hPw⟩,
            ⟨s, e, hnonradial⟩⟩
      have hcandidates :
          (retainedNonradialQuotientNodeComponentsThroughPoint
            lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
              (p.m : ℤ) hm plane w).Nonempty := ⟨P, hcandidate⟩
      unfold integralQuotientPacketPriorityLabel at hlabel
      rw [dif_neg helementary] at hlabel
      dsimp only at hlabel
      rw [dif_pos hcandidates] at hlabel
      simp at hlabel
    · exact Or.inr hexceptional

/-- The final static label at `(w,q)`.  Whenever the point certificate makes
the pair eligible, this uses the unique selected plane attached to the
occupied pair `(q, residue(w))`. -/
def isolatedVertexQuotientStaticComponentLabel
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (x₀ : IntVector 13)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (hquotient : isolatedVertexQuotientPointFinset U p x₀
      sourceEquations CF ⊆ integralCommonZeroInBox
        (M := isolatedVertexTransformedNaturalSide U p)
        (isolatedVertexQuotientAffineEquationFinset
          U p x₀ lowerEquations))
    {P : Finset ℕ} {k : ℕ}
    (hqpos : ∀ q : ReservoirModulus P k, 0 < q.1)
    (hqsf : ∀ q : ReservoirModulus P k, Squarefree q.1)
    (hqlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget
        (isolatedVertexQuotientReservoirConstant U : ℝ)
        p.T (9 / 13) ≤ q.1)
    (w : IntVector 12) (q : ReservoirModulus P k) :
    Option (Ideal (MvPolynomial (Fin 13) Qbar)) :=
  let rho : Fin 12 → ZMod q.1 := integralResidueVector w
  if heligible : IsEligibleIsolatedVertexQuotientPacket
      U p x₀ sourceEquations CF lowerEquations q.1 rho then
    integralQuotientPacketPriorityLabel lowerEquations
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ)
      (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
      (selectedIntegralIsolatedVertexQuotientPacketPlane
        U p x₀ sourceEquations CF lowerEquations hquotient
        q.1 (hqpos q) (hqsf q) (hqlower q) rho heligible) w
  else none

/-- Specification of every nonempty static label at a surviving modulus.
In particular, its packet plane is the one fixed by `(q,residue(w))`. -/
theorem isolatedVertexQuotientStaticComponentLabel_eq_some_spec
    (U : IntegralUnimodularChange 13) (p : Parameters)
    (sourceEquations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    {x₀ : IntVector 13}
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset
      p sourceEquations CF)
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
    {w : IntVector 12}
    (hw : w ∈ isolatedVertexRegularQuotientPointFinset
      U p x₀ sourceEquations CF lowerEquations)
    (q : ReservoirModulus Ppool k)
    (hsurvives : survivesTwoCertificates q (p.m : ℤ)
      (isolatedVertexQuotientSelectedCertificateValue
        U p sourceEquations CF hx₀ lowerEquations w))
    {P : Ideal (MvPolynomial (Fin 13) Qbar)}
    (hlabel : isolatedVertexQuotientStaticComponentLabel
      U p x₀ sourceEquations CF lowerEquations hquotient
      hqpos hqsf hqlower w q = some P) :
    let heligible :=
      isEligibleIsolatedVertexQuotientPacket_of_survives
        U p sourceEquations CF hx₀ lowerEquations q hw hsurvives
    let plane := selectedIntegralIsolatedVertexQuotientPacketPlane
      U p x₀ sourceEquations CF lowerEquations hquotient
      q.1 (hqpos q) (hqsf q) (hqlower q)
      (integralResidueVector w) heligible
    P ∈ integralIsolatedVertexQuotientNodeComponents lowerEquations
        (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ)
        (by exact_mod_cast (Nat.ne_of_gt p.one_le_m)) plane.matrix ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P ∧
      IsRetainedNonradialQuotientNodeComponent
        (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
        (algebraMap ℚ Qbar (p.m : ℚ)) P ∧
      ¬ ∃ Q ∈ integralQuotientNodeComponentsThroughPoint
          lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
          (p.m : ℤ) (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
          plane w,
        IsElementaryQuotientNodeComponent
          (qbarIntVector (dropFirstIntVector (U.pointEquiv x₀)))
          (algebraMap ℚ Qbar (p.m : ℚ)) Q := by
  dsimp only
  let heligible :=
    isEligibleIsolatedVertexQuotientPacket_of_survives
      U p sourceEquations CF hx₀ lowerEquations q hw hsurvives
  unfold isolatedVertexQuotientStaticComponentLabel at hlabel
  dsimp only at hlabel
  rw [dif_pos heligible] at hlabel
  exact integralQuotientPacketPriorityLabel_eq_some_spec
    lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
      (p.m : ℤ) (by exact_mod_cast (Nat.ne_of_gt p.one_le_m))
      (selectedIntegralIsolatedVertexQuotientPacketPlane
        U p x₀ sourceEquations CF lowerEquations hquotient
        q.1 (hqpos q) (hqsf q) (hqlower q)
        (integralResidueVector w) heligible) w hlabel

end

end TranslatedDepthSeven
