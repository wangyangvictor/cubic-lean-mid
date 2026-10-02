import TranslatedDepthSeven.RankSevenEdgeAggregatePila
import TranslatedDepthSeven.RankSevenRecordCardinality
import TranslatedDepthSeven.HomogeneousMinimalComponents

/-!
# Degree and dimension data for the rank-seven edge frontiers

This file removes the three geometric premises which occur in the aggregate
Pila estimate for unequal surface labels.  The only external inputs are two
ordinary statements about degrees:

* affine Bezout for the reduced components of the intersection of two
  homogeneous prime cones; and
* invariance of dimension and total component degree after extending the
  ground field and passing to the standard affine chart.

Both inputs are stated for arbitrary homogeneous prime ideals.  They contain
no residue class, point count, determinant-method branch, or rank-seven
object.  The strict dimension drop for two distinct surface components is
already kernel-proved in `FiniteComponentFrontier.lean` and specialized to
the literal edge records in `RankSevenNodeRecords.lean`.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 4000000

namespace StandardAG

/-- The reduced-component degree inequality for the intersection of two
affine varieties, in the homogeneous-cone case.

The displayed degree is the ordinary affine degree.  No proper-intersection
hypothesis is required for this set-theoretic form: intersect successively
with hypersurfaces defining one factor and discard multiplicities and
embedded components.  This is the affine Bezout inequality, equivalently
the projective degree inequality for the closures of the two cones.

References: Heintz, *Definability and fast quantifier elimination in
algebraically closed fields*, Theorem 1; Fulton, *Intersection Theory*,
Section 8.4; or the Stacks Project, Section 43.16, after the usual diagonal
construction. -/
def HomogeneousPrimeIntersectionAffineDegreeMass : Prop :=
  ∀ (N s t d e : ℕ)
    (I J : Ideal (MvPolynomial (Fin N) ℚ)),
    I.IsPrime →
    J.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
    J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin N) ℚ) →
    HasAffineDimensionDegree I s d →
    HasAffineDimensionDegree J t e →
      ∃ componentDimension componentDegree :
          Ideal (MvPolynomial (Fin N) ℚ) → ℕ,
        (∀ L ∈ finiteMinimalPrimes (I ⊔ J),
          HasAffineDimensionDegree L
            (componentDimension L) (componentDegree L)) ∧
        ∑ L ∈ finiteMinimalPrimes (I ⊔ J),
          componentDegree L ≤ d * e

/-- Extension from `ℚ` to `ℝ` followed by the standard dehomogenized
chart preserves the dimension of every nonempty projective component and
splits its degree additively among the actual real minimal components.

The premise is written for the affine cone: if its dimension is `s`, every
nonempty chart component has dimension `s-1`, expressed without truncated
subtraction by `chartDimension Q + 1 = s`.  If the homogeneous prime is
contained in the hyperplane `X₀=0`, its standard chart is empty and the
component clauses are vacuous.

References: Hartshorne, Chapter I, Sections 2 and 7; the Stacks Project,
Tags `01M3` and `00P0`; and flat invariance/additivity of Hilbert
polynomials under a field extension. -/
def HomogeneousPrimeRealAffineChartDegreeMass : Prop :=
  ∀ (N s d : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasAffineDimensionDegree I s d →
      ∃ chartDimension chartDegree :
          Ideal (MvPolynomial (Fin N) ℝ) → ℕ,
        (∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I),
          chartDimension Q + 1 = s ∧
          HasAffineDimensionDegree Q
            (chartDimension Q) (chartDegree Q)) ∧
        ∑ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal I),
          chartDegree Q ≤ d

end StandardAG

/-- The literal node equation ideal is homogeneous. -/
theorem rankSevenNodeEquationIdeal_isHomogeneous
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q) :
    (rankSevenNodeEquationIdeal p x₀ equations CF C q rho).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
  simpa [rankSevenNodeEquationIdeal,
    rankSevenSourceSectionEquationsAtResidue,
    rankSevenSourceSectionIdeal] using
    rankSevenSourceSectionIdeal_isHomogeneous x₀ p.hm equations
      hhomogeneous
      ((selectedRankSevenPacketSectionMatrix
        p x₀ equations CF C q rho).map ((↑) : ℤ → ℚ))

/-- Every actual node component is homogeneous. -/
theorem rankSevenNodeComponent_isHomogeneous
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ rankSevenNodeComponents p x₀ equations CF C q rho) :
    I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
  apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    (rankSevenNodeEquationIdeal_isHomogeneous
      p x₀ equations CF hhomogeneous C q rho)
  simpa [rankSevenNodeComponents] using hI

/-- Every actual node component is prime. -/
theorem rankSevenNodeComponent_isPrime
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (hI : I ∈ rankSevenNodeComponents p x₀ equations CF C q rho) :
    I.IsPrime := by
  apply isPrime_of_mem_finiteMinimalPrimes
  simpa [rankSevenNodeComponents] using hI

/-- Endpoint-local form of the edge Bezout argument.  Unlike the uniform
wrapper below, this theorem asks only for degree certificates for the two
components which actually occur in the displayed edge record. -/
theorem rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass_of_endpointData
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    {dleft dright D : ℕ}
    (hleftProjective : HasProjectiveDimensionDegree
      record.leftComponent 2 dleft)
    (hrightProjective : HasProjectiveDimensionDegree
      record.rightComponent 2 dright)
    (hdleft : dleft ≤ D) (hdright : dright ≤ D) :
    ∃ componentDimension componentDegree :
        Ideal (MvPolynomial (Fin 14) ℚ) → ℕ,
      (∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        componentDimension L ≤ 2 ∧
        1 ≤ componentDegree L ∧
        HasAffineDimensionDegree L
          (componentDimension L) (componentDegree L)) ∧
      ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        componentDegree L ≤ D * D := by
  obtain ⟨hleft, hright, _hne⟩ :=
    (mem_rankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C q r hP record).1 hrecord
  have hleftNode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C q.1
      (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) record.residue)
      record.leftComponent).1 hleft |>.1
  have hrightNode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C r.1
      (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) record.residue)
      record.rightComponent).1 hright |>.1
  have hleftPrime : record.leftComponent.IsPrime :=
    rankSevenNodeComponent_isPrime p x₀ equations CF C q.1 _ _ hleftNode
  have hrightPrime : record.rightComponent.IsPrime :=
    rankSevenNodeComponent_isPrime p x₀ equations CF C r.1 _ _ hrightNode
  have hleftHomogeneous : record.leftComponent.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    rankSevenNodeComponent_isHomogeneous
      p x₀ equations CF hhomogeneous C q.1 _ _ hleftNode
  have hrightHomogeneous : record.rightComponent.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    rankSevenNodeComponent_isHomogeneous
      p x₀ equations CF hhomogeneous C r.1 _ _ hrightNode
  have hleftAffine : HasAffineDimensionDegree
      record.leftComponent 3 dleft := by
    simpa using
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        record.leftComponent hleftHomogeneous hleftPrime 2 dleft
          hleftProjective
  have hrightAffine : HasAffineDimensionDegree
      record.rightComponent 3 dright := by
    simpa using
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        record.rightComponent hrightHomogeneous hrightPrime 2 dright
          hrightProjective
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    hBezout 14 3 3 dleft dright record.leftComponent record.rightComponent
      hleftPrime hrightPrime hleftHomogeneous hrightHomogeneous
      hleftAffine hrightAffine
  refine ⟨componentDimension, componentDegree, ?_, hmass.trans ?_⟩
  · intro L hL
    have hdimensionDrop : ringKrullDim
        (MvPolynomial (Fin 14) ℚ ⧸ L) < 3 :=
      rankSevenSurfaceEdgeRecord_frontier_dimension_lt_three
        p x₀ equations CF C q r hP record hrecord L hL
    have hLdata := hcomponents L hL
    have hdimension : componentDimension L < 3 := by
      rw [hLdata.2.1] at hdimensionDrop
      exact_mod_cast hdimensionDrop
    exact ⟨by omega, hLdata.2.2.1, hLdata⟩
  · exact Nat.mul_le_mul hdleft hdright

/-- Endpoint-local form of all three geometric premises needed by the edge
aggregate: number of projective frontier components, geometry of every real
affine component, and number of nonlinear affine components. -/
theorem rankSevenSurfaceEdgeRecord_frontier_geometry_of_endpointData
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    {dleft dright D : ℕ}
    (hleftProjective : HasProjectiveDimensionDegree
      record.leftComponent 2 dleft)
    (hrightProjective : HasProjectiveDimensionDegree
      record.rightComponent 2 dright)
    (hdleft : dleft ≤ D) (hdright : dright ≤ D) :
    (finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent)).card ≤ D * D ∧
    (∀ L ∈ finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent),
      ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D * D ∧
          HasAffineHilbertDimensionDegree Q n d) ∧
    (∀ L ∈ finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent),
      (nonlinearAffineComponents
        (realProjectiveAffineChartIdeal L)).card ≤ D * D) := by
  classical
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass_of_endpointData
      hBezout p x₀ equations CF hhomogeneous C q r hP record hrecord
        hleftProjective hrightProjective hdleft hdright
  have hcard : (finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent)).card ≤ D * D :=
    Finset.card_le_of_sum_positive_mass
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent))
      componentDegree (D * D) (fun L hL ↦ (hcomponents L hL).2.1)
        hmass
  have hsupHomogeneous :
      (record.leftComponent ⊔ record.rightComponent).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
    obtain ⟨hleft, hright, _hne⟩ :=
      (mem_rankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF C q r hP record).1 hrecord
    exact
      (rankSevenNodeComponent_isHomogeneous
        p x₀ equations CF hhomogeneous C q.1 _ record.leftComponent
          ((mem_rankSevenSurfaceNodeComponents_iff
            p x₀ equations CF C q.1 _ record.leftComponent).1 hleft).1).sup
      (rankSevenNodeComponent_isHomogeneous
        p x₀ equations CF hhomogeneous C r.1 _ record.rightComponent
          ((mem_rankSevenSurfaceNodeComponents_iff
            p x₀ equations CF C r.1 _ record.rightComponent).1 hright).1)
  refine ⟨hcard, ?_, ?_⟩
  · intro L hL Q hQ
    have hLdata := hcomponents L hL
    have hLhomogeneous : L.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
      apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
        hsupHomogeneous
      exact (mem_finiteMinimalPrimes_iff _ _).mp hL
    obtain ⟨chartDimension, chartDegree, hchart, hchartMass⟩ :=
      hChart 13 (componentDimension L) (componentDegree L) L
        hLdata.2.2.1 hLhomogeneous hLdata.2.2
    have hQdata := hchart Q hQ
    have hn : chartDimension Q ≤ 1 := by
      have hu := hLdata.1
      omega
    have hdegreeL : componentDegree L ≤ D * D :=
      (Finset.single_le_sum
        (fun R _hR ↦ Nat.zero_le (componentDegree R)) hL).trans hmass
    have hdegreeQ : chartDegree Q ≤ D * D :=
      ((Finset.single_le_sum
        (fun R _hR ↦ Nat.zero_le (chartDegree R)) hQ).trans
          hchartMass).trans hdegreeL
    exact ⟨chartDimension Q, chartDegree Q, hn,
      hQdata.2.2.2.1, hdegreeQ, hQdata.2.toHilbert⟩
  · intro L hL
    have hLdata := hcomponents L hL
    have hLhomogeneous : L.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
      apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
        hsupHomogeneous
      exact (mem_finiteMinimalPrimes_iff _ _).mp hL
    obtain ⟨chartDimension, chartDegree, hchart, hchartMass⟩ :=
      hChart 13 (componentDimension L) (componentDegree L) L
        hLdata.2.2.1 hLhomogeneous hLdata.2.2
    have hall : (finiteMinimalPrimes
        (realProjectiveAffineChartIdeal L)).card ≤ componentDegree L :=
      Finset.card_le_of_sum_positive_mass
        (finiteMinimalPrimes (realProjectiveAffineChartIdeal L))
        chartDegree (componentDegree L)
        (fun Q hQ ↦ (hchart Q hQ).2.2.2.1) hchartMass
    have hdegreeL : componentDegree L ≤ D * D :=
      (Finset.single_le_sum
        (fun R _hR ↦ Nat.zero_le (componentDegree R)) hL).trans hmass
    exact (Finset.card_filter_le _ _).trans (hall.trans hdegreeL)

/-- Affine Bezout supplies a positive degree mass for the literal frontier
of one unequal pair of surface components.  If the two endpoint degrees are
at most `D`, the complete frontier mass is at most `D²`.

The dimensions in the returned affine-cone certificates are not assumed:
the already proved strict inclusion of frontier primes forces them to be at
most two. -/
theorem rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    (D : ℕ)
    (hdegree : ∀ (u : ℕ) (rho : Fin 13 → ZMod u)
      (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ),
      I ∈ rankSevenSurfaceNodeComponents
          p x₀ equations CF C u rho →
      HasProjectiveDimensionDegree I 2 d → d ≤ D) :
    ∃ componentDimension componentDegree :
        Ideal (MvPolynomial (Fin 14) ℚ) → ℕ,
      (∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        componentDimension L ≤ 2 ∧
        1 ≤ componentDegree L ∧
        HasAffineDimensionDegree L
          (componentDimension L) (componentDegree L)) ∧
      ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
        componentDegree L ≤ D * D := by
  obtain ⟨hleft, hright, _hne⟩ :=
    (mem_rankSevenSurfaceEdgeRecords_iff
      p x₀ equations CF C q r hP record).1 hrecord
  obtain ⟨hleftNode, dleft, hleftProjective⟩ :=
    (mem_rankSevenSurfaceNodeComponents_iff
      p x₀ equations CF C q.1
        (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) record.residue)
        record.leftComponent).1 hleft
  obtain ⟨hrightNode, dright, hrightProjective⟩ :=
    (mem_rankSevenSurfaceNodeComponents_iff
      p x₀ equations CF C r.1
        (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) record.residue)
        record.rightComponent).1 hright
  have hleftPrime : record.leftComponent.IsPrime :=
    rankSevenNodeComponent_isPrime p x₀ equations CF C q.1 _ _ hleftNode
  have hrightPrime : record.rightComponent.IsPrime :=
    rankSevenNodeComponent_isPrime p x₀ equations CF C r.1 _ _ hrightNode
  have hleftHomogeneous : record.leftComponent.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    rankSevenNodeComponent_isHomogeneous
      p x₀ equations CF hhomogeneous C q.1 _ _ hleftNode
  have hrightHomogeneous : record.rightComponent.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    rankSevenNodeComponent_isHomogeneous
      p x₀ equations CF hhomogeneous C r.1 _ _ hrightNode
  have hleftAffine : HasAffineDimensionDegree
      record.leftComponent 3 dleft := by
    simpa using
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        record.leftComponent hleftHomogeneous hleftPrime 2 dleft
          hleftProjective
  have hrightAffine : HasAffineDimensionDegree
      record.rightComponent 3 dright := by
    simpa using
      hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
        record.rightComponent hrightHomogeneous hrightPrime 2 dright
          hrightProjective
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    hBezout 14 3 3 dleft dright record.leftComponent record.rightComponent
      hleftPrime hrightPrime hleftHomogeneous hrightHomogeneous
      hleftAffine hrightAffine
  refine ⟨componentDimension, componentDegree, ?_, ?_⟩
  · intro L hL
    have hdimensionDrop : ringKrullDim
        (MvPolynomial (Fin 14) ℚ ⧸ L) < 3 :=
      rankSevenSurfaceEdgeRecord_frontier_dimension_lt_three
        p x₀ equations CF C q r hP record hrecord L hL
    have hLdata := hcomponents L hL
    have hdimension : componentDimension L < 3 := by
      rw [hLdata.2.1] at hdimensionDrop
      exact_mod_cast hdimensionDrop
    exact ⟨by omega, hLdata.2.2.1, hLdata⟩
  · calc
      ∑ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
          componentDegree L ≤ dleft * dright := hmass
      _ ≤ D * D := by
        apply Nat.mul_le_mul
        · exact hdegree q.1 _ record.leftComponent dleft hleft
            hleftProjective
        · exact hdegree r.1 _ record.rightComponent dright hright
            hrightProjective

/-- The same mass bounds the number of literal projective frontier primes. -/
theorem rankSevenSurfaceEdgeRecord_frontier_card_le
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    (D : ℕ)
    (hdegree : ∀ (u : ℕ) (rho : Fin 13 → ZMod u)
      (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ),
      I ∈ rankSevenSurfaceNodeComponents
          p x₀ equations CF C u rho →
      HasProjectiveDimensionDegree I 2 d → d ≤ D) :
    (finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent)).card ≤ D * D := by
  classical
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass
      hBezout p x₀ equations CF hhomogeneous C q r hP record hrecord D
        hdegree
  exact Finset.card_le_of_sum_positive_mass
    (finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent))
    componentDegree (D * D) (fun L hL ↦ (hcomponents L hL).2.1) hmass

/-- Each real affine component of one literal frontier has dimension at most
one and degree at most `D²`. -/
theorem rankSevenSurfaceEdgeRecord_frontier_affineComponent_geometry
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    (D : ℕ)
    (hdegree : ∀ (u : ℕ) (rho : Fin 13 → ZMod u)
      (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ),
      I ∈ rankSevenSurfaceNodeComponents
          p x₀ equations CF C u rho →
      HasProjectiveDimensionDegree I 2 d → d ≤ D)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    (hL : L ∈ finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent))
    (Q : Ideal (MvPolynomial (Fin 13) ℝ))
    (hQ : Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L)) :
    ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D * D ∧
      HasAffineHilbertDimensionDegree Q n d := by
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass
      hBezout p x₀ equations CF hhomogeneous C q r hP record hrecord D
        hdegree
  have hLdata := hcomponents L hL
  have hLprime : L.IsPrime := hLdata.2.2.1
  have hedge := (mem_rankSevenSurfaceEdgeRecords_iff
    p x₀ equations CF C q r hP record).1 hrecord
  have hleftNode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C q.1
      (reduceResidueVector (Nat.dvd_lcm_left q.1 r.1) record.residue)
      record.leftComponent).1 hedge.1 |>.1
  have hrightNode := (mem_rankSevenSurfaceNodeComponents_iff
    p x₀ equations CF C r.1
      (reduceResidueVector (Nat.dvd_lcm_right q.1 r.1) record.residue)
      record.rightComponent).1 hedge.2.1 |>.1
  have hsupHomogeneous :
      (record.leftComponent ⊔ record.rightComponent).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) :=
    (rankSevenNodeComponent_isHomogeneous
      p x₀ equations CF hhomogeneous C q.1 _ record.leftComponent
        hleftNode).sup
      (rankSevenNodeComponent_isHomogeneous
        p x₀ equations CF hhomogeneous C r.1 _ record.rightComponent
          hrightNode)
  have hLhomogeneous : L.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
    apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
      hsupHomogeneous
    exact (mem_finiteMinimalPrimes_iff _ _).mp hL
  obtain ⟨chartDimension, chartDegree, hchart, hchartMass⟩ :=
    hChart 13 (componentDimension L) (componentDegree L) L hLprime
      hLhomogeneous hLdata.2.2
  have hQdata := hchart Q hQ
  have hn : chartDimension Q ≤ 1 := by
    have hu := hLdata.1
    omega
  have hdegreeL : componentDegree L ≤ D * D := by
    exact (Finset.single_le_sum
      (fun R _hR ↦ Nat.zero_le (componentDegree R)) hL).trans hmass
  have hdegreeQ : chartDegree Q ≤ D * D := by
    exact ((Finset.single_le_sum
      (fun R _hR ↦ Nat.zero_le (chartDegree R)) hQ).trans
        hchartMass).trans hdegreeL
  exact ⟨chartDimension Q, chartDegree Q, hn,
    hQdata.2.2.2.1, hdegreeQ, hQdata.2.toHilbert⟩

/-- The nonlinear real affine components of one frontier are also bounded
by the same degree mass `D²`. -/
theorem rankSevenSurfaceEdgeRecord_frontier_nonlinear_card_le
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {P : Finset ℕ} {k : ℕ}
    (q r : ReservoirModulus P k) (hP : ∀ s ∈ P, s.Prime)
    (record : RankSevenEdgeRecord (Nat.lcm q.1 r.1))
    (hrecord : record ∈
      rankSevenSurfaceEdgeRecords p x₀ equations CF C q r hP)
    (D : ℕ)
    (hdegree : ∀ (u : ℕ) (rho : Fin 13 → ZMod u)
      (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ),
      I ∈ rankSevenSurfaceNodeComponents
          p x₀ equations CF C u rho →
      HasProjectiveDimensionDegree I 2 d → d ≤ D)
    (L : Ideal (MvPolynomial (Fin 14) ℚ))
    (hL : L ∈ finiteMinimalPrimes
      (record.leftComponent ⊔ record.rightComponent)) :
    (nonlinearAffineComponents
      (realProjectiveAffineChartIdeal L)).card ≤ D * D := by
  classical
  obtain ⟨componentDimension, componentDegree, hcomponents, hmass⟩ :=
    rankSevenSurfaceEdgeRecord_frontier_affineDegreeMass
      hBezout p x₀ equations CF hhomogeneous C q r hP record hrecord D
        hdegree
  have hLdata := hcomponents L hL
  have hLprime : L.IsPrime := hLdata.2.2.1
  have hsupHomogeneous :
      (record.leftComponent ⊔ record.rightComponent).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
    obtain ⟨hleft, hright, _hne⟩ :=
      (mem_rankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF C q r hP record).1 hrecord
    exact
      (rankSevenNodeComponent_isHomogeneous
        p x₀ equations CF hhomogeneous C q.1 _ record.leftComponent
          ((mem_rankSevenSurfaceNodeComponents_iff
            p x₀ equations CF C q.1 _ record.leftComponent).1 hleft).1).sup
      (rankSevenNodeComponent_isHomogeneous
        p x₀ equations CF hhomogeneous C r.1 _ record.rightComponent
          ((mem_rankSevenSurfaceNodeComponents_iff
            p x₀ equations CF C r.1 _ record.rightComponent).1 hright).1)
  have hLhomogeneous : L.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 14) ℚ) := by
    apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hsupHomogeneous
    exact (mem_finiteMinimalPrimes_iff _ _).mp hL
  obtain ⟨chartDimension, chartDegree, hchart, hchartMass⟩ :=
    hChart 13 (componentDimension L) (componentDegree L) L hLprime
      hLhomogeneous hLdata.2.2
  have hall : (finiteMinimalPrimes
      (realProjectiveAffineChartIdeal L)).card ≤ componentDegree L :=
    Finset.card_le_of_sum_positive_mass
      (finiteMinimalPrimes (realProjectiveAffineChartIdeal L))
      chartDegree (componentDegree L)
      (fun Q hQ ↦ (hchart Q hQ).2.2.2.1) hchartMass
  have hdegreeL : componentDegree L ≤ D * D :=
    (Finset.single_le_sum
      (fun R _hR ↦ Nat.zero_le (componentDegree R)) hL).trans hmass
  exact (Finset.card_filter_le _ _).trans (hall.trans hdegreeL)

/-- All three geometric hypotheses of the directed-edge aggregate theorem
follow uniformly from bounded endpoint degrees and the two textbook degree
statements.  The record premise is the surviving record set used in the
aggregate theorem; it is reduced immediately to its literal coarse edge
record. -/
theorem rankSevenSurvivingSurfaceEdge_geometryPremises
    (hBezout : StandardAG.HomogeneousPrimeIntersectionAffineDegreeMass)
    (hChart : StandardAG.HomogeneousPrimeRealAffineChartDegreeMass)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
    (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (D : ℕ)
    (hdegree : ∀ (u : ℕ) (rho : Fin 13 → ZMod u)
      (I : Ideal (MvPolynomial (Fin 14) ℚ)) (d : ℕ),
      I ∈ rankSevenSurfaceNodeComponents
          p x₀ equations CF Cchart u rho →
      HasProjectiveDimensionDegree I 2 d → d ≤ D) :
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      (finiteMinimalPrimes
        (record.leftComponent ⊔ record.rightComponent)).card ≤ D * D) ∧
    (∀ (qr : ↑(modulusReservoirDirectedEdges P k hP))
        (record : RankSevenEdgeRecord
          (Nat.lcm qr.1.1.1 qr.1.2.1)),
      record ∈ occupiedRankSevenSurvivingSurfaceEdgeRecords
          p x₀ equations CF Cchart denominator P k hP hlower
            qr.1.1 qr.1.2 →
      ∀ L ∈ finiteMinimalPrimes
          (record.leftComponent ⊔ record.rightComponent),
      ∀ Q ∈ finiteMinimalPrimes (realProjectiveAffineChartIdeal L),
        ∃ n d : ℕ, n ≤ 1 ∧ 1 ≤ d ∧ d ≤ D * D ∧
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
          (realProjectiveAffineChartIdeal L)).card ≤ D * D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro qr record hrecord
    have hoccupied : record ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP :=
      (Finset.mem_filter.mp hrecord).1
    have hcoarse : record ∈ rankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart qr.1.1 qr.1.2 hP :=
      (mem_occupiedRankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP record).1
          hoccupied |>.1
    exact rankSevenSurfaceEdgeRecord_frontier_card_le
      hBezout p x₀ equations CF hhomogeneous Cchart
        qr.1.1 qr.1.2 hP record hcoarse D hdegree
  · intro qr record hrecord L hL Q hQ
    have hoccupied : record ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP :=
      (Finset.mem_filter.mp hrecord).1
    have hcoarse : record ∈ rankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart qr.1.1 qr.1.2 hP :=
      (mem_occupiedRankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP record).1
          hoccupied |>.1
    exact rankSevenSurfaceEdgeRecord_frontier_affineComponent_geometry
      hBezout hChart p x₀ equations CF hhomogeneous Cchart
        qr.1.1 qr.1.2 hP record hcoarse D hdegree L hL Q hQ
  · intro qr record hrecord L hL
    have hoccupied : record ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP :=
      (Finset.mem_filter.mp hrecord).1
    have hcoarse : record ∈ rankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart qr.1.1 qr.1.2 hP :=
      (mem_occupiedRankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart P k qr.1.1 qr.1.2 hP record).1
          hoccupied |>.1
    exact rankSevenSurfaceEdgeRecord_frontier_nonlinear_card_le
      hBezout hChart p x₀ equations CF hhomogeneous Cchart
        qr.1.1 qr.1.2 hP record hcoarse D hdegree L hL

end

end TranslatedDepthSeven
