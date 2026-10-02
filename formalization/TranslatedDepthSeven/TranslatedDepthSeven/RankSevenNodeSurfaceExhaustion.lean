import TranslatedDepthSeven.RankSevenNodeAggregateSum
import TranslatedDepthSeven.StrictProjectiveInputBridge
import TranslatedDepthSeven.RankSevenEdgeFrontierGeometry

/-!
# Every surviving rank-seven node component is a surface

The source section is a projective sixfold cone cut by four independent
hyperplanes.  Hence each of its nonempty irreducible components has
projective dimension at least two, and the sum of their degrees is bounded
by the degree of the original fivefold.  Projection away from the cone
vertex has one-dimensional fibres when the vertex lies in the four-plane,
and is an isomorphism on the four-plane otherwise.  The two image sections
therefore have codimension four and three respectively.  At a point outside
the already defined exceptional locus, their components have dimension at
most one and two respectively.  Thus every source component containing a
surviving point has projective dimension exactly two.

The two geometric facts in the preceding paragraph are isolated below as
ordinary textbook propositions.  They contain no point-counting assertion.
All residue, height, exceptional-locus, and record bookkeeping is proved in
this file for the literal objects used downstream.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization
open Matrix MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6000000

namespace StandardAG

/-- Four (possibly dependent or zero) hyperplanes cut the translated
projective cone over an integral projective fivefold in components of
projective dimension at least two, and projective Bezout bounds their total
degree by the degree of the fivefold.

This is Krull's height theorem plus projective Bezout, after the displayed
homogeneous affine coordinate change identifying the translated cone with
the polynomial extension of the original homogeneous coordinate ring.
References: Hartshorne, Chapter I, Sections 7.1 and 7.7; the Stacks Project,
Tags `00KD`, `00KP`, and `0B04`. -/
def RankFourSectionOfTranslatedConeDegreeMass : Prop :=
  ∀ (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ) (degree : ℕ),
    IsIntegralProjectiveVariety
        (finiteEquationIdeal (rationalizedEquationFinset equations))
        5 degree →
      ∃ componentDimension componentDegree :
          Ideal (MvPolynomial (Fin 14) ℚ) → ℕ,
        (∀ I ∈ finiteMinimalPrimes
            (rankSevenSourceSectionIdeal x₀ m hm equations A),
          2 ≤ componentDimension I ∧
          HasProjectiveDimensionDegree I
            (componentDimension I) (componentDegree I)) ∧
        ∑ I ∈ finiteMinimalPrimes
            (rankSevenSourceSectionIdeal x₀ m hm equations A),
          componentDegree I ≤ degree

/-- Component correspondence for a four-plane section of a translated
projective cone under the literal projection
`[s:y] ↦ [s*x₀+m*y]`.

If the cone vertex lies in the four-plane, a source component through an
affine-chart point is the join of the vertex with a component of the
codimension-four image section, so its projective dimension is one larger.
If the vertex does not lie in the four-plane, restriction of the projection
is a linear isomorphism onto the displayed codimension-three image, so the
dimensions agree.  Coefficient extension to `Qbar` is included because the
exceptional locus is defined using geometric components.

This is the standard correspondence of irreducible components under a
linear projection restricted either to a projective bundle of relative
dimension one or to a linear isomorphism.  See Hartshorne, Chapter I,
Sections 3--4, or the Stacks Project, Tags `01UA`, `01W0`, and `02R1`.
The homogeneous-base condition is essential and is supplied by the
original projective-variety hypothesis at every application. The statement
is proved in `RankFourTranslatedConeProjectionInternal` from the two
ordinary Hilbert--Serre certificates, rather than assumed at the root. -/
def RankFourTranslatedConeComponentProjection : Prop :=
  ∀ (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (_hhomogeneous :
      (finiteEquationIdeal (rationalizedEquationFinset equations)).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 13) ℚ))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (z : IntVector 13) (s d : ℕ),
    A.rank = 4 →
    I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A) →
    HasProjectiveDimensionDegree I s d →
    (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I →
    ∀ hx : integralAffineMap x₀ z m ≠ 0,
      ((Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) = 0) →
        ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
          ∃ r e : ℕ,
            IsProjectiveSectionComponent equations
              (translatedJoinImageFourEquationMatrixFin A) Q ∧
            ProjectivePointVanishesOnGeometricIdeal Q
              (integralProjectiveClass (integralAffineMap x₀ z m) hx) ∧
            HasGeometricProjectiveDimensionDegree Q r e ∧
            s = r + 1) ∧
      (∀ i₀ : Fin 4,
        Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) i₀ ≠ 0 →
        ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
          ∃ r e : ℕ,
            IsProjectiveSectionComponent equations
              (translatedJoinImageThreeEquationMatrixFin A
                (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i₀) Q ∧
            ProjectivePointVanishesOnGeometricIdeal Q
              (integralProjectiveClass (integralAffineMap x₀ z m) hx) ∧
            HasGeometricProjectiveDimensionDegree Q r e ∧
            s = r)

end StandardAG

/-- The selected integral four-plane retains the entry bound of the Cramer
datum from which it was chosen. -/
theorem selectedRankSevenPacketSectionMatrix_entry_le
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    ∀ i j,
      ((selectedRankSevenPacketSectionMatrix
        p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1)) i j).natAbs ≤
        depthSevenPacketSectionEntryBound p := by
  let hdata := exists_rankSevenPacketSectionData_of_mem_reservoirCell
    p x₀ equations CF C denominator P k hP hlower q z hz
  rw [selectedRankSevenPacketSectionMatrix]
  simp only [dif_pos hdata]
  exact (selectedRankSevenPacketSectionData
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) hdata).entry_le

/-- For the selected literal four-plane, the two projection alternatives
have the exact ranks used in the exceptional locus and height at most
`ceil(H^CF)`. -/
theorem selectedRankSevenPacketSection_projected_dichotomy
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    let Aint := selectedRankSevenPacketSectionMatrix
      p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1)
    let A := Aint.map ((↑) : ℤ → ℚ)
    (Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ)) = 0 ∧
      (translatedJoinImageFourEquationMatrixFin A).rank = 4 ∧
      rationalProjectiveLinearHeight
          (translatedJoinImageFourEquationMatrixFin A) ≤ ⌈p.H ^ CF⌉₊) ∨
    ∃ i₀ : Fin 4,
      Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ)) i₀ ≠ 0 ∧
      (translatedJoinImageThreeEquationMatrixFin A
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀).rank = 3 ∧
      rationalProjectiveLinearHeight
          (translatedJoinImageThreeEquationMatrixFin A
            (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀) ≤ ⌈p.H ^ CF⌉₊ := by
  dsimp only
  let Aint := selectedRankSevenPacketSectionMatrix
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)
  let A := Aint.map ((↑) : ℤ → ℚ)
  have hA : A.rank = 4 := by
    exact selectedRankSevenPacketSectionMatrix_rank
      p x₀ equations CF C denominator P k hP hlower q z hz
  have hentry : ∀ i j, (Aint i j).natAbs ≤
      depthSevenPacketSectionEntryBound p :=
    selectedRankSevenPacketSectionMatrix_entry_le
      p x₀ equations CF C denominator P k hP hlower q z hz
  have hmQ : (p.m : ℚ) ≠ 0 := by exact_mod_cast p.hm.ne'
  rcases translatedJoinImage_rank_dichotomyFin A hA
      (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) hmQ with hfour | hthree
  · left
    refine ⟨hfour.1, hfour.2, ?_⟩
    have hraw : rationalProjectiveLinearHeight
        (translatedJoinImageFourEquationMatrixFin A) ≤
          Nat.factorial 4 * (depthSevenPacketSectionEntryBound p) ^ 4 := by
      simpa [A, Aint,
        integralTranslatedJoinImageFourEquationMatrix_map_intCast] using
        (integralTranslatedJoinImageFourEquationMatrix_height_le Aint hentry)
    have h160 := codimensionFour_packetSectionHeight_le_ceil_heightPower
      p (r := 9) (by omega)
    have h260 : ⌈p.H ^ packetSectionHeightExponent⌉₊ ≤
        ⌈p.H ^ depthSevenProjectedSectionHeightExponent⌉₊ := by
      apply Nat.ceil_mono
      exact pow_le_pow_right₀ (p.one_le_T.trans p.T_le_H) (by
        norm_num [packetSectionHeightExponent,
          depthSevenProjectedSectionHeightExponent])
    exact hraw.trans (h160.trans
      (h260.trans (ceil_projectedSectionHeightPower_le p hCF)))
  · obtain ⟨i₀, hpivot, hrank⟩ := hthree
    right
    refine ⟨i₀, hpivot, hrank, ?_⟩
    have hxbound : ∀ j, (x₀ j).natAbs ≤
        depthSevenProjectionBaseHeight x₀ :=
      coordinate_le_depthSevenProjectionBaseHeight x₀
    have hraw : rationalProjectiveLinearHeight
        (translatedJoinImageThreeEquationMatrixFin A
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀) ≤
        Nat.factorial 3 *
          (2 * ((p.m + 13 * depthSevenProjectionBaseHeight x₀) *
            depthSevenPacketSectionEntryBound p) *
            depthSevenPacketSectionEntryBound p) ^ 3 := by
      simpa [A, Aint,
        integralTranslatedJoinImageThreeEquationMatrix_map_intCast] using
        (integralTranslatedJoinImageThreeEquationMatrix_height_le
          Aint x₀ (p.m : ℤ) i₀ hentry hxbound (by simp))
    exact hraw.trans
      ((depthSeven_threeEquationHeightBound_le_ceil_heightPower
        p equations CF hx₀).trans
        (ceil_projectedSectionHeightPower_le p hCF))

/-- At a surviving occupied node, the ordinary four-plane-section degree
mass is attached to the literal residue-indexed source ideal. -/
theorem rankSevenSurvivingNode_componentDegreeMass
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1) :
    ∃ componentDimension componentDegree :
        Ideal (MvPolynomial (Fin 14) ℚ) → ℕ,
      (∀ I ∈ rankSevenNodeComponents p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1),
        2 ≤ componentDimension I ∧
        HasProjectiveDimensionDegree I
          (componentDimension I) (componentDegree I)) ∧
      ∑ I ∈ rankSevenNodeComponents p x₀ equations CF C q.1
          (integralResidueVector z : Fin 13 → ZMod q.1),
        componentDegree I ≤ degree := by
  let A := (selectedRankSevenPacketSectionMatrix
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)).map
        ((↑) : ℤ → ℚ)
  have hA : A.rank = 4 :=
    selectedRankSevenPacketSectionMatrix_rank
      p x₀ equations CF C denominator P k hP hlower q z hz
  simpa [rankSevenNodeComponents, rankSevenNodeEquationIdeal,
    rankSevenSourceSectionEquationsAtResidue, A] using
    hLinear x₀ p.m p.hm equations A degree hOriginal

/-- The same degree mass bounds the complete residue-indexed node list,
whether or not that residue contributes a surviving point.  This is the
literal source-component bound used in the edge-record occurrence count. -/
theorem rankSevenNodeComponents_card_le_originalDegree
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    (rankSevenNodeComponents p x₀ equations CF C q rho).card ≤ degree := by
  classical
  let A := (selectedRankSevenPacketSectionMatrix
    p x₀ equations CF C q rho).map ((↑) : ℤ → ℚ)
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    hLinear x₀ p.m p.hm equations A degree hOriginal
  have hcard : (finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A)).card ≤
        degree :=
    Finset.card_le_of_sum_positive_mass
      (finiteMinimalPrimes
        (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A))
      componentDegree degree
      (fun I hI ↦ (hcomponents I hI).2.2.1) hmass
  simpa [rankSevenNodeComponents, rankSevenNodeEquationIdeal,
    rankSevenSourceSectionEquationsAtResidue, A] using hcard

/-- In particular the filtered list of surface node components has the
same uniform cardinality bound. -/
theorem rankSevenSurfaceNodeComponents_card_le_originalDegree
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    (rankSevenSurfaceNodeComponents p x₀ equations CF C q rho).card ≤
      degree := by
  classical
  exact (Finset.card_filter_le _ _).trans
    (rankSevenNodeComponents_card_le_originalDegree hLinear
      p x₀ equations CF degree hOriginal C q rho)

/-- A surface component at a surviving node admits a degree certificate
bounded by the original fivefold degree.  No uniqueness theorem for the
degree is needed: the degree-mass certificate itself supplies a projective
dimension, and comparison with the already present surface certificate
forces that dimension to be two. -/
theorem rankSevenSurfaceNodeComponent_degree_le_of_survivingPoint
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) (z : IntVector 13)
    (hz : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ rankSevenSurfaceNodeComponents p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)) :
    ∃ d : ℕ, HasProjectiveDimensionDegree I 2 d ∧ d ≤ degree := by
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    rankSevenSurvivingNode_componentDegreeMass hLinear
      p x₀ equations CF degree hOriginal C denominator P k hP hlower
        q z hz
  have hnode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1) I).1 hI
  obtain ⟨_hsLower, hdegreeMass⟩ := hcomponents I hnode.1
  obtain ⟨dsurface, hsurface⟩ := hnode.2
  have hdim : componentDimension I = 2 := by
    have heq : componentDimension I + 1 = 2 + 1 := by
      exact_mod_cast hdegreeMass.1.symm.trans hsurface.1
    omega
  have hcomponentDegree : componentDegree I ≤ degree :=
    (Finset.single_le_sum
      (fun J _hJ ↦ Nat.zero_le (componentDegree J)) hnode.1).trans hmass
  exact ⟨componentDegree I, hdim ▸ hdegreeMass, hcomponentDegree⟩

/-- The node degree mass supplies the endpoint certificates needed by the
edge-frontier Bezout argument.  Hence the three literal edge-aggregate
geometry premises hold with `F = E = degree^2`, without a degree hypothesis
quantified over irrelevant residue classes. -/
theorem rankSevenSurvivingSurfaceEdge_geometryPremises_of_originalDegree
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤
          degree * degree) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
      ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ degree * degree ∧
          HasAffineHilbertDimensionDegree Q n d) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ degree * degree) := by
  classical
  have hlocal : ∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
      (record : RankSevenEdgeRecord
        (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤
          degree * degree ∧
      (∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
          ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ degree * degree ∧
            HasAffineHilbertDimensionDegree Q n d) ∧
      (∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ degree * degree) := by
    intro qr record hrecord
    have hoccupied : record ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP :=
      (Finset.mem_filter.mp hrecord).1
    obtain ⟨z, hzSurviving⟩ := (Finset.mem_filter.mp hrecord).2
    have hzRecord : z ∈ rankSevenSurfaceEdgeRecordPointCell
        p x₀ equations CF Cchart P k record :=
      (Finset.mem_filter.mp hzSurviving).1
    have hzEdge : z ∈ rankSevenSurfaceEdgeCell
        p x₀ equations CF Cchart denominator P k hP hlower
          qr.1.1 qr.1.2 :=
      (Finset.mem_filter.mp hzSurviving).2
    obtain ⟨hzChart, hqSurvives, hrSurvives, _hqr, _hne,
        _hqne, _hrne⟩ := Finset.mem_filter.mp hzEdge
    have hzq : z ∈ rankSevenChartReservoirCell
        p x₀ equations CF Cchart denominator qr.1.1.1 :=
      Finset.mem_filter.mpr ⟨hzChart, hqSurvives⟩
    have hzr : z ∈ rankSevenChartReservoirCell
        p x₀ equations CF Cchart denominator qr.1.2.1 :=
      Finset.mem_filter.mpr ⟨hzChart, hrSurvives⟩
    have hcoarse : record ∈ rankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart qr.1.1 qr.1.2 hP :=
      (mem_occupiedRankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP record).1
          hoccupied |>.1
    obtain ⟨hleft, hright, _hne'⟩ :=
      (mem_rankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart qr.1.1 qr.1.2 hP record).1 hcoarse
    have hzRecordData := (mem_rankSevenSurfaceEdgeRecordPointCell_iff
      p x₀ equations CF Cchart P k record z).1 hzRecord
    have hleftAtZ : record.leftComponent ∈
        rankSevenSurfaceNodeComponents p x₀ equations CF Cchart qr.1.1.1
          (integralResidueVector z : Fin 13 → ZMod qr.1.1.1) := by
      rw [← hzRecordData.2.1] at hleft
      simpa using hleft
    have hrightAtZ : record.rightComponent ∈
        rankSevenSurfaceNodeComponents p x₀ equations CF Cchart qr.1.2.1
          (integralResidueVector z : Fin 13 → ZMod qr.1.2.1) := by
      rw [← hzRecordData.2.1] at hright
      simpa using hright
    obtain ⟨dleft, hleftProjective, hdleft⟩ :=
      rankSevenSurfaceNodeComponent_degree_le_of_survivingPoint hLinear
        p x₀ equations CF degree hOriginal Cchart denominator P k hP
          hlower qr.1.1 z hzq record.leftComponent hleftAtZ
    obtain ⟨dright, hrightProjective, hdright⟩ :=
      rankSevenSurfaceNodeComponent_degree_le_of_survivingPoint hLinear
        p x₀ equations CF degree hOriginal Cchart denominator P k hP
          hlower qr.1.2 z hzr record.rightComponent hrightAtZ
    exact rankSevenSurfaceEdgeRecord_frontier_geometry_of_endpointData
      hBezout hChart p x₀ equations CF hhomogeneous Cchart
        qr.1.1 qr.1.2 hP record hcoarse hleftProjective
          hrightProjective hdleft hdright
  exact ⟨fun qr record hrecord ↦ (hlocal qr record hrecord).1,
    fun qr record hrecord ↦ (hlocal qr record hrecord).2.1,
    fun qr record hrecord ↦ (hlocal qr record hrecord).2.2⟩

/-- Exact package of the four algebraic-geometric hypotheses occurring in
`exists_uniform_rankSevenSurvivingSurfaceEdgeFrontier_aggregate_constant`.
The source bound is `degree`; all frontier bounds are `degree^2`. -/
theorem rankSevenEdgeAggregate_geometry_of_originalDegree
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1) :
    (∀ (q : ReservoirModulus P k) (rho : Fin 13 → ZMod q.1),
      rho ∈ occupiedIntegralResidues q.1
          (depthSevenNormalizedJacobianChartCell
            p x₀ equations CF Cchart) →
      (rankSevenSurfaceNodeComponents
        p x₀ equations CF Cchart q.1 rho).card ≤ degree) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤
          degree * degree) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
      ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ degree * degree ∧
          HasAffineHilbertDimensionDegree Q n d) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        (nonlinearAffineComponents
          (realProjectiveAffineChartIdeal L)).card ≤ degree * degree) := by
  have hedge :=
    rankSevenSurvivingSurfaceEdge_geometryPremises_of_originalDegree
      hLinear hBezout hChart p x₀ equations CF degree hhomogeneous
        hOriginal Cchart denominator P k hP hlower
  exact ⟨fun q rho _hrho ↦
      rankSevenSurfaceNodeComponents_card_le_originalDegree hLinear
        p x₀ equations CF degree hOriginal Cchart q.1 rho,
    hedge.1, hedge.2.1, hedge.2.2⟩

/-- Every occupied surviving record in the nominal non-surface node family
is impossible.  The conclusion is literal emptiness, not a point-count
estimate. -/
theorem occupiedRankSevenSurvivingNonSurfaceNodeRecords_eq_empty
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (hProjection : StandardAG.RankFourTranslatedConeComponentProjection)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) :
    occupiedRankSevenSurvivingNonSurfaceNodeRecords
      p x₀ equations CF C denominator P k hP hlower q = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro record hrecord
  have hrecordData :=
    (mem_occupiedRankSevenSurvivingNonSurfaceNodeRecords_iff
      p x₀ equations CF C denominator P k hP hlower q record).1 hrecord
  obtain ⟨z, hzSurviving⟩ := hrecordData.2
  have hzData := (mem_rankSevenSurvivingNonSurfaceNodeRecordPointCell_iff
    p x₀ equations CF C denominator P k hP hlower q record z).1
      hzSurviving
  have hzPoint := (mem_rankSevenNonSurfaceNodeRecordPointCell_iff
    p x₀ equations CF C record z).1 hzData.1
  have hzNode := Finset.mem_filter.mp hzData.2
  have hzReservoir : z ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator q.1 :=
    Finset.mem_filter.mpr ⟨hzNode.1, hzNode.2.1⟩
  have hrecordCoarse :=
    (mem_occupiedRankSevenNonSurfaceNodeRecords_iff
      p x₀ equations CF C q record).1 hrecordData.1
  have hnonSurface :=
    (mem_rankSevenNonSurfaceNodeComponents_iff
      p x₀ equations CF C q.1 record.residue record.component).1
      hrecordCoarse.2
  have hresidue : (integralResidueVector z : Fin 13 → ZMod q.1) =
      record.residue := hzPoint.2.1
  have hcomponent : record.component ∈ rankSevenNodeComponents
      p x₀ equations CF C q.1
        (integralResidueVector z : Fin 13 → ZMod q.1) := by
    rw [hresidue]
    exact hnonSurface.1
  obtain ⟨componentDimension, componentDegree, hcomponents, _hmass⟩ :=
    rankSevenSurvivingNode_componentDegreeMass hLinear
      p x₀ equations CF degree hOriginal C denominator P k hP hlower
        q z hzReservoir
  obtain ⟨hsLower, hsDegree⟩ := hcomponents record.component hcomponent
  let Aint := selectedRankSevenPacketSectionMatrix
    p x₀ equations CF C q.1
      (integralResidueVector z : Fin 13 → ZMod q.1)
  let A := Aint.map ((↑) : ℤ → ℚ)
  have hA : A.rank = 4 :=
    selectedRankSevenPacketSectionMatrix_rank
      p x₀ equations CF C denominator P k hP hlower q z hzReservoir
  have hcomponentSource : record.component ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A) := by
    simpa [rankSevenNodeComponents, rankSevenNodeEquationIdeal,
      rankSevenSourceSectionEquationsAtResidue, A, Aint] using hcomponent
  have hzNormalized : z ∈ depthSevenNormalizedDisplacementFinset
      p x₀ equations CF :=
    (mem_depthSevenNormalizedJacobianChartCell_iff
      p x₀ equations CF C z).1 hzPoint.1 |>.1
  have hzNormalizedData := Finset.mem_filter.mp hzNormalized |>.2
  obtain ⟨_hbox, _hzero, hx, _hlinear, hnotExceptional⟩ :=
    hzNormalizedData
  have hproject := hProjection x₀ p.m p.hm equations hOriginal.1 A
    record.component z (componentDimension record.component)
      (componentDegree record.component) hA hcomponentSource hsDegree
        hzPoint.2.2 hx
  have hdichotomy := selectedRankSevenPacketSection_projected_dichotomy
    p x₀ equations CF hCF hx₀ C denominator P k hP hlower
      q z hzReservoir
  dsimp only at hdichotomy
  change
    ((Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ)) = 0 ∧
      (translatedJoinImageFourEquationMatrixFin A).rank = 4 ∧
      rationalProjectiveLinearHeight
          (translatedJoinImageFourEquationMatrixFin A) ≤ ⌈p.H ^ CF⌉₊) ∨
    ∃ i₀ : Fin 4,
      Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ)) i₀ ≠ 0 ∧
      (translatedJoinImageThreeEquationMatrixFin A
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀).rank = 3 ∧
      rationalProjectiveLinearHeight
          (translatedJoinImageThreeEquationMatrixFin A
            (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀) ≤ ⌈p.H ^ CF⌉₊)
      at hdichotomy
  have hsUpper : componentDimension record.component ≤ 2 := by
    rcases hdichotomy with hfour | hthree
    · obtain ⟨Q, r, e, hQcomponent, hxQ, hQdegree, hs⟩ :=
        hproject.1 hfour.1
      have hr := codimensionFour_component_dimension_le_one_of_not_exceptional
        equations ⌈p.H ^ CF⌉₊
          (translatedJoinImageFourEquationMatrixFin A) hfour.2.1
          hfour.2.2 Q hQcomponent
          (integralProjectiveClass (integralAffineMap x₀ z p.m) hx)
          hxQ hnotExceptional hQdegree
      omega
    · obtain ⟨i₀, hpivot, hrank, hheight⟩ := hthree
      obtain ⟨Q, r, e, hQcomponent, hxQ, hQdegree, hs⟩ :=
        hproject.2 i₀ hpivot
      have hr :=
        (codimensionThree_component_dimension_degree_of_not_exceptional
          equations ⌈p.H ^ CF⌉₊
            (translatedJoinImageThreeEquationMatrixFin A
              (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀)
            hrank hheight Q hQcomponent
            (integralProjectiveClass (integralAffineMap x₀ z p.m) hx)
            hxQ hnotExceptional hQdegree).1
      omega
  have hsEq : componentDimension record.component = 2 := by omega
  apply hnonSurface.2
  exact ⟨componentDegree record.component, hsEq ▸ hsDegree⟩

/-- Consequently the complete surviving non-surface node point cell is
empty at every reservoir modulus. -/
theorem rankSevenNonSurfaceNodeCell_eq_empty
    (hLinear : StandardAG.RankFourSectionOfTranslatedConeDegreeMass)
    (hProjection : StandardAG.RankFourTranslatedConeComponentProjection)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF degree : ℕ)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (hOriginal : IsIntegralProjectiveVariety
      (finiteEquationIdeal (rationalizedEquationFinset equations))
      5 degree)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (q : ReservoirModulus P k) :
    rankSevenNonSurfaceNodeCell
      p x₀ equations CF C denominator P k hP hlower q = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  have hcover := rankSevenNonSurfaceNodeCell_subset_survivingRecordUnion
    p x₀ equations CF hhomogeneous C denominator P k hP hlower q hz
  rw [occupiedRankSevenSurvivingNonSurfaceNodeRecords_eq_empty
    hLinear hProjection p x₀ equations CF degree hCF hx₀ hOriginal C
      denominator P k hP hlower q] at hcover
  simpa using hcover

end

end TranslatedDepthSeven
