import TranslatedDepthSeven.IsolatedVertexQuotientSourceSectionHeightDomination
import TranslatedDepthSeven.ProjectiveConeMinimalPrimeStructure

/-!
# Literal four-class aggregation for the isolated-vertex quotient

This file combines the actual integral packet plane, its actual geometric
minimal primes, the literal original-coordinate exceptional lift, and the
fixed height cutoff.  The four alternatives remain literal: a
zero-dimensional component, a radial line, a nonradial integral curve, or
membership in the bounded-height exceptional locus of the source.

The only new projective-geometric input is the narrow degree assertion that
a one-dimensional component of a cone section whose plane contains the cone
vertex has degree one.  Containment of the component in the translated
vertex is proved from the literal cone equations and minimal-prime algebra;
it is not part of the outside input.  No point count or aggregate estimate
is included here.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000

/-- Scalar extension from `ℚ` to `Qbar` preserves the rank of the literal
integral quotient plane. -/
theorem qbarIntMatrix_rank
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℤ) :
    (qbarIntMatrix A).rank =
      (A.map (Int.castRingHom ℚ)).rank := by
  unfold qbarIntMatrix
  exact TangentBaseChange.rank_map_algebraMap
    (A.map (Int.castRingHom ℚ))

@[simp]
theorem isolatedVertexQuotientProjectiveVertexVector_zero
    {K : Type*} [Field K] (b : Fin 12 → K) (m : K) :
    isolatedVertexQuotientProjectiveVertexVector b m 0 = m := by
  unfold isolatedVertexQuotientProjectiveVertexVector
  rw [_root_.finSuccEquiv_zero]

@[simp]
theorem isolatedVertexQuotientProjectiveVertexVector_succ
    {K : Type*} [Field K] (b : Fin 12 → K) (m : K) (j : Fin 12) :
    isolatedVertexQuotientProjectiveVertexVector b m j.succ = -b j := by
  unfold isolatedVertexQuotientProjectiveVertexVector
  rw [_root_.finSuccEquiv_succ]

private theorem matrix_mulVec_integralQuotientVertex
    (A : Matrix (Fin 4) (Fin 13) ℤ) (b : IntVector 12) (m : ℤ) :
    Matrix.mulVec A (Fin.cases m (fun j ↦ -b j)) =
      integralQuotientSourceVertexEvaluation A b m := by
  funext i
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ,
    integralQuotientSourceVertexEvaluation,
    integralQuotientSourceSpatialMatrix, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

/-- The geometric four-plane evaluated at the translated quotient vertex is
the coefficient extension of the literal integral vertex evaluation. -/
theorem qbarIntMatrix_mulVec_quotientVertex
    (A : Matrix (Fin 4) (Fin 13) ℤ) (b : IntVector 12) (m : ℤ) :
    Matrix.mulVec (qbarIntMatrix A)
        (isolatedVertexQuotientProjectiveVertexVector
          (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))) =
      fun i ↦ algebraMap ℚ Qbar
        (integralQuotientSourceVertexEvaluation A b m i : ℚ) := by
  let φ : ℤ →+* Qbar :=
    (algebraMap ℚ Qbar).comp (Int.castRingHom ℚ)
  let v : Fin 13 → ℤ := Fin.cases m (fun j ↦ -b j)
  have hv : isolatedVertexQuotientProjectiveVertexVector
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) =
      fun j ↦ φ (v j) := by
    funext j
    cases j using Fin.cases with
    | zero => simp [v, φ]
    | succ j => simp [v, φ, qbarIntVector]
  rw [hv]
  funext i
  calc
    Matrix.mulVec (qbarIntMatrix A) (fun j ↦ φ (v j)) i =
        φ (Matrix.mulVec A v i) := by
          simpa [qbarIntMatrix, φ] using
            (RingHom.map_mulVec φ A v i).symm
    _ = φ (integralQuotientSourceVertexEvaluation A b m i) := by
      rw [matrix_mulVec_integralQuotientVertex]
    _ = algebraMap ℚ Qbar
        (integralQuotientSourceVertexEvaluation A b m i : ℚ) := rfl

/-- Vanishing of the integral vertex evaluation is equivalent to vanishing
after coefficient extension on the geometric translated vertex. -/
theorem qbarIntMatrix_mulVec_quotientVertex_eq_zero_iff
    (A : Matrix (Fin 4) (Fin 13) ℤ) (b : IntVector 12) (m : ℤ) :
    Matrix.mulVec (qbarIntMatrix A)
        (isolatedVertexQuotientProjectiveVertexVector
          (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ))) = 0 ↔
      integralQuotientSourceVertexEvaluation A b m = 0 := by
  rw [qbarIntMatrix_mulVec_quotientVertex]
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    have hiQ : (integralQuotientSourceVertexEvaluation A b m i : ℚ) = 0 :=
      (map_eq_zero_iff (algebraMap ℚ Qbar)
        (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp hi
    exact_mod_cast hiQ
  · intro h
    funext i
    rw [congrFun h i]
    simp

namespace StandardAG

/-- Narrow textbook degree input: a one-dimensional component of the
displayed homogeneous quotient-node section has degree one when the
four-plane contains the translated cone vertex.  The hypothesis on the
base ideal is explicit.  Vertex containment is intentionally absent from
the conclusion, since it is proved in the kernel from the cone equations. -/
def IntegralQuotientNodeOneDimensionalContainedComponentDegreeOne : Prop :=
  ∀ (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (P : Ideal (MvPolynomial (Fin 13) Qbar)) (e : ℕ),
    (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar) →
    (A.map (Int.castRingHom ℚ)).rank = 4 →
    integralQuotientSourceVertexEvaluation A b m = 0 →
    P ∈ integralIsolatedVertexQuotientNodeComponents
      lowerEquations b m hm A →
    HasGeometricProjectiveDimensionDegree P 1 e →
      e = 1

end StandardAG

/-- A quotient component has a literal exceptional lift whose source
section height is bounded by the displayed common cutoff. -/
def HasLiteralOriginalSourceExceptionalLiftAtHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (U : IntegralUnimodularChange 13)
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (s e heightBound : ℕ) : Prop :=
  ∃ sourceHeight : ℕ,
    sourceHeight ≤ heightBound ∧
    Nonempty (LiteralOriginalSourceExceptionalLift
      equations lowerEquations U b m hm A P s e sourceHeight)

/-- The literal four alternatives for one actual integral quotient-node
component, with the exceptional alternative already expressed at a common
source height cutoff. -/
def IntegralQuotientNodeComponentDispositionAtHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (U : IntegralUnimodularChange 13)
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (s e heightBound : ℕ) : Prop :=
  IsZeroDimensionalQuotientNodeComponent P s e ∨
    IsRadialQuotientNodeLine
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e ∨
    IsNonradialIntegralQuotientNodeCurve
      (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e ∨
    HasLiteralOriginalSourceExceptionalLiftAtHeight
      equations lowerEquations U b m hm A P s e heightBound

/-- Every positive-dimensional component of the actual integral quotient
node belongs to one of the four literal classes, and every exceptional lift
already satisfies the single fixed source-height cutoff. -/
theorem integralQuotientNodeComponentDispositionAtHeight
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
    (hJhomogeneous :
      (geometricIsolatedVertexLowerIdeal lowerEquations).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 12) Qbar))
    (hm : (p.m : ℤ) ≠ 0)
    {Z : Finset (IntVector 12)} {q : ℕ} {rho : Fin 12 → ZMod q}
    (plane : IntegralIsolatedVertexQuotientPacketPlane Z q
      (isolatedVertexTransformedNaturalSide U p) rho)
    (P : Ideal (MvPolynomial (Fin 13) Qbar))
    (hP : P ∈ integralIsolatedVertexQuotientNodeComponents
      lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
      (p.m : ℤ) hm plane.matrix)
    (s e : ℕ)
    (hHilbert : HasGeometricProjectiveDimensionDegree P s e)
    (hs : 1 ≤ s) :
    IntegralQuotientNodeComponentDispositionAtHeight
      equations lowerEquations U
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm
      plane.matrix P s e
      ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
  let b := dropFirstIntVector (U.pointEquiv x₀)
  let HA := (12 * isolatedVertexTransformedNaturalSide U p + 1) *
    (plane.spanRank.factorial *
      (2 * isolatedVertexTransformedNaturalSide U p) ^ plane.spanRank)
  let X := integralMatrixL1Norm U.forward *
    depthSevenProjectionBaseHeight x₀
  have hA : (plane.matrix.map (Int.castRingHom ℚ)).rank = 4 :=
    plane.rank_matrix
  have hAq : (qbarIntMatrix plane.matrix).rank = 4 :=
    (qbarIntMatrix_rank plane.matrix).trans hA
  have hPprime : P.IsPrime := isPrime_of_mem_finiteMinimalPrimes hP
  have hPhomogeneous : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 13) Qbar) := by
    exact isolatedVertexQuotientNodeComponent_isHomogeneous
      (geometricIsolatedVertexLowerIdeal lowerEquations) hJhomogeneous
      (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ))
      (qbarIntCast_ne_zero hm) (qbarIntMatrix plane.matrix) P hP
  have hb : ∀ j, (b j).natAbs ≤ X := by
    intro j
    exact dropFirst_pointEquiv_coordinate_natAbs_le U x₀ j
  have hmBound : ((p.m : ℤ).natAbs) ≤ p.m := by simp
  have hfourHeight :
      integralQuotientOriginalSourceFourSectionHeightBound U HA ≤
        ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
    exact integralQuotientPacketPlane_sourceFourHeight_le_ceil_heightPower
      U p plane
  have hthreeHeight :
      integralQuotientOriginalSourceThreeSectionHeightBound U HA X p.m ≤
        ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
    exact integralQuotientPacketPlane_sourceThreeHeight_le_ceil_heightPower
      U p equations CF hx₀ plane
  by_cases hvertex :
      integralQuotientSourceVertexEvaluation plane.matrix b (p.m : ℤ) = 0
  · by_cases hs1 : s = 1
    · have hHilbertOne : HasGeometricProjectiveDimensionDegree P 1 e := by
        simpa only [hs1] using hHilbert
      have he := hRadial lowerEquations b (p.m : ℤ) hm
        plane.matrix P e hJhomogeneous hA hvertex hP hHilbertOne
      have hvertexQ : Matrix.mulVec (qbarIntMatrix plane.matrix)
          (isolatedVertexQuotientProjectiveVertexVector
            (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ))) = 0 := by
        exact (qbarIntMatrix_mulVec_quotientVertex_eq_zero_iff
          plane.matrix b (p.m : ℤ)).2 hvertex
      have hcontains : QuotientComponentContainsVertex
          (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ)) P := by
        exact quotientNodeComponent_containsVertex_of_plane_contains
          (geometricIsolatedVertexLowerIdeal lowerEquations)
          hJhomogeneous (qbarIntVector b)
          (algebraMap ℚ Qbar (p.m : ℚ)) (qbarIntCast_ne_zero hm)
          (qbarIntMatrix plane.matrix) hvertexQ P hP
      exact Or.inr (Or.inl
        ⟨⟨hPprime, hPhomogeneous⟩, hHilbert, hs1, he, hcontains⟩)
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨L⟩ :=
        exists_literalOriginalSourceExceptionalLift_of_contained_of_two_le_dimension
          hProjection equations U lowerEquations hfamily hJhomogeneous
          b (p.m : ℤ) hm
          plane.matrix hA HA plane.entry_natAbs_le hvertex
          P hP s e hHilbert hs2
      exact Or.inr (Or.inr (Or.inr
        ⟨integralQuotientOriginalSourceFourSectionHeightBound U HA,
          hfourHeight, ⟨L⟩⟩))
  · by_cases hs1 : s = 1
    · by_cases he7 : e ≤ 7
      · obtain ⟨L⟩ :=
          exists_literalOriginalSourceExceptionalLift_of_away_of_curve_degree_le_seven
            hProjection equations U lowerEquations hfamily hJhomogeneous
            b (p.m : ℤ) hm
            plane.matrix hA HA X p.m plane.entry_natAbs_le hb hmBound
            hvertex P hP s e hHilbert hs1 he7
        exact Or.inr (Or.inr (Or.inr
          ⟨integralQuotientOriginalSourceThreeSectionHeightBound
              U HA X p.m,
            hthreeHeight, ⟨L⟩⟩))
      · have he8 : 8 ≤ e := by omega
        have hvertexQ : Matrix.mulVec (qbarIntMatrix plane.matrix)
            (isolatedVertexQuotientProjectiveVertexVector
              (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ))) ≠ 0 := by
          intro hzero
          exact hvertex
            ((qbarIntMatrix_mulVec_quotientVertex_eq_zero_iff
              plane.matrix b (p.m : ℤ)).mp hzero)
        have hnotcontains : ¬ QuotientComponentContainsVertex
            (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ)) P :=
          quotientNodeComponent_not_containsVertex_of_plane_avoids
            (geometricIsolatedVertexLowerIdeal lowerEquations)
            (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ))
            (qbarIntCast_ne_zero hm) (qbarIntMatrix plane.matrix)
            hvertexQ P hP
        exact Or.inr (Or.inr (Or.inl
          ⟨⟨hPprime, hPhomogeneous⟩, hHilbert, hs1,
            (by omega), hnotcontains⟩))
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨L⟩ :=
        exists_literalOriginalSourceExceptionalLift_of_away_of_two_le_dimension
          hProjection equations U lowerEquations hfamily hJhomogeneous
          b (p.m : ℤ) hm
          plane.matrix hA HA X p.m plane.entry_natAbs_le hb hmBound
          hvertex P hP s e hHilbert hs2
      exact Or.inr (Or.inr (Or.inr
        ⟨integralQuotientOriginalSourceThreeSectionHeightBound
            U HA X p.m,
          hthreeHeight, ⟨L⟩⟩))

/-- The actual minimal-prime list of one integral packet plane admits a
four-class decomposition with literal Hilbert data and the original total
degree mass.  No anonymous component labels replace the ideals. -/
theorem exists_integralQuotientNodeFourClassDecompositionAtHeight
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
      (isolatedVertexTransformedNaturalSide U p) rho) :
    ∃ componentDimension componentDegree :
        Ideal (MvPolynomial (Fin 13) Qbar) → ℕ,
      (∀ P ∈ integralIsolatedVertexQuotientNodeComponents
          lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
          (p.m : ℤ) hm plane.matrix,
        1 ≤ componentDimension P ∧
        HasGeometricProjectiveDimensionDegree P
          (componentDimension P) (componentDegree P) ∧
        IntegralQuotientNodeComponentDispositionAtHeight
          equations lowerEquations U
          (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm
          plane.matrix P (componentDimension P) (componentDegree P)
          ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊) ∧
      ∑ P ∈ integralIsolatedVertexQuotientNodeComponents
          lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
          (p.m : ℤ) hm plane.matrix,
        componentDegree P ≤ degree := by
  let J := geometricIsolatedVertexLowerIdeal lowerEquations
  let b := dropFirstIntVector (U.pointEquiv x₀)
  have hAq : (qbarIntMatrix plane.matrix).rank = 4 :=
    (qbarIntMatrix_rank plane.matrix).trans plane.rank_matrix
  obtain ⟨componentDimension, componentDegree, hcomponents, hdegree⟩ :=
    hMass J (qbarIntVector b) (algebraMap ℚ Qbar (p.m : ℚ))
      (qbarIntCast_ne_zero hm) (qbarIntMatrix plane.matrix) degree
      hJprime hJhomogeneous hJHilbert hAq
  refine ⟨componentDimension, componentDegree, ?_, hdegree⟩
  intro P hP
  obtain ⟨hs, hHilbert⟩ := hcomponents P hP
  exact ⟨hs, hHilbert,
    integralQuotientNodeComponentDispositionAtHeight
      hProjection hRadial p equations U lowerEquations hfamily CF x₀ hx₀
      hJhomogeneous hm plane P hP
      (componentDimension P) (componentDegree P) hHilbert hs⟩

/-- Pointwise form of the four classes.  In the first three alternatives the
actual minimal-prime ideal containing the quotient point is retained.  The
fourth alternative is already literal membership in the bounded-height
exceptional locus of the original source. -/
def IntegralQuotientPacketPointDispositionAtHeight
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (lowerEquations : Finset (MvPolynomial (Fin 12) ℤ))
    (b : IntVector 12) (m : ℤ) (hm : m ≠ 0)
    (A : Matrix (Fin 4) (Fin 13) ℤ)
    (w : IntVector 12) (x : IntVector 13) (hx : x ≠ 0)
    (heightBound : ℕ) : Prop :=
  (∃ (P : Ideal (MvPolynomial (Fin 13) Qbar)) (s e : ℕ),
      P ∈ integralIsolatedVertexQuotientNodeComponents
        lowerEquations b m hm A ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P ∧
      IsZeroDimensionalQuotientNodeComponent P s e) ∨
    (∃ (P : Ideal (MvPolynomial (Fin 13) Qbar)) (s e : ℕ),
      P ∈ integralIsolatedVertexQuotientNodeComponents
        lowerEquations b m hm A ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P ∧
      IsRadialQuotientNodeLine
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e) ∨
    (∃ (P : Ideal (MvPolynomial (Fin 13) Qbar)) (s e : ℕ),
      P ∈ integralIsolatedVertexQuotientNodeComponents
        lowerEquations b m hm A ∧
      geometricQuotientRationalHomogeneousAffinePoint w ∈
        affineIdealZeroLocus P ∧
      IsNonradialIntegralQuotientNodeCurve
        (qbarIntVector b) (algebraMap ℚ Qbar (m : ℚ)) P s e) ∨
    MemDepthSevenExceptionalLocus equations heightBound
      (integralProjectiveClass x hx)

/-- Every actual point of an occupied quotient packet is assigned to one of
the three retained quotient component classes or to the literal
bounded-height exceptional locus of the source.  This theorem is a finite
component aggregation only; it contains no estimate for any class. -/
theorem integralQuotientPacketPointDispositionAtHeight
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
        (dropFirstIntVector (U.pointEquiv x₀)) w (p.m : ℤ)) :
    IntegralQuotientPacketPointDispositionAtHeight
      equations lowerEquations
      (dropFirstIntVector (U.pointEquiv x₀)) (p.m : ℤ) hm
      plane.matrix w x hx
      ⌈p.H ^ isolatedVertexQuotientSourceSectionHeightExponent U⌉₊ := by
  obtain ⟨componentDimension, componentDegree, hcomponents, _hdegree⟩ :=
    exists_integralQuotientNodeFourClassDecompositionAtHeight
      hMass hProjection hRadial p equations U lowerEquations hfamily
      CF x₀ hx₀ hJprime hJhomogeneous degree hJHilbert hm plane
  obtain ⟨P, hP, hPw⟩ :=
    exists_integralQuotientNodeComponent_through_packetPoint
      lowerEquations (dropFirstIntVector (U.pointEquiv x₀))
      (p.m : ℤ) hm plane w hw hy
  obtain ⟨_hs, _hHilbert, hDisposition⟩ := hcomponents P hP
  rcases hDisposition with hzero | hradial | hnonradial | hexceptional
  · exact Or.inl ⟨P, componentDimension P, componentDegree P,
      hP, hPw, hzero⟩
  · exact Or.inr (Or.inl ⟨P, componentDimension P, componentDegree P,
      hP, hPw, hradial⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨P, componentDimension P, componentDegree P,
        hP, hPw, hnonradial⟩))
  · obtain ⟨sourceHeight, hheight, ⟨L⟩⟩ := hexceptional
    exact Or.inr (Or.inr (Or.inr
      (L.memDepthSevenExceptionalLocus_of_quotientPoint_of_height_le
        hheight x hx w hspatial hPw)))

end

end TranslatedDepthSeven
