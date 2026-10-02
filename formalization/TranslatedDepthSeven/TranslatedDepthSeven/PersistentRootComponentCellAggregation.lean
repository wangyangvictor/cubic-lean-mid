import TranslatedDepthSeven.RootedGeometricComponentPersistence
import TranslatedDepthSeven.SurfaceProperCutPila
import TranslatedDepthSeven.GlobalDistinguishedUnionAggregation
import TranslatedDepthSeven.DegreeOneComponentSetCover
import TranslatedDepthSeven.RankSevenDegreeOneLineIncidence

/-!
# Aggregating the actual persistent root-component cells

The common-root partition indexes persistent cells by the literal minimal
prime components of one fixed root cut.  For every nonempty cell we retain
one actual terminal cut reached by that same component.  The terminal cut
vanishes on the whole root-component cell, so the existing proper-cut Pila
theorem applies.  Its degree-one contribution is united as one finite set
before the nonlinear errors are summed.

No cardinal estimate for an abstract persistent family is assumed.  The
number of nonempty cells is bounded by the actual root Bezout certificate.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000

local instance persistentRootAggregationPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual root-component options whose displayed persistent cell is
nonempty. -/
def activePersistentRootComponentOptions
    {N : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (G₀ : MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      Finset (IntVector N)) :
    Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))) :=
  (finiteEquationComponentOptions
    (finiteEquationFamilyUnion sourceEquations {G₀})).filter
      fun o => (cell o).Nonempty

@[simp]
theorem mem_activePersistentRootComponentOptions_iff
    {N : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (G₀ : MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      Finset (IntVector N))
    (o : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))) :
    o ∈ activePersistentRootComponentOptions sourceEquations G₀ cell ↔
      o ∈ finiteEquationComponentOptions
        (finiteEquationFamilyUnion sourceEquations {G₀}) ∧
      (cell o).Nonempty := by
  simp [activePersistentRootComponentOptions]

/-- The one multiplicity-free union of all affine degree-one components
left by the terminal proper cuts attached to the active root cells. -/
def persistentRootComponentLinearPointUnion
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      Finset (IntVector N)) : Finset (IntVector N) :=
  active.biUnion fun o =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (terminalCut o)) (cell o)

/-- The preceding literal union is exactly the standard untagged line union
for the finite subtype of active root components.  Thus all existing tagged
line and full-line incidence APIs apply without introducing a new catalogue. -/
theorem persistentRootComponentLinearPointUnion_eq_underlying
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      Finset (IntVector N)) :
    persistentRootComponentLinearPointUnion I active terminalCut cell =
      underlyingLinearContributionPoints
        (fun o : {o // o ∈ active} =>
          realAffineChartIntersectionIdeal I (terminalCut o.1))
        (fun o : {o // o ∈ active} => cell o.1) := by
  classical
  rw [underlyingLinearContributionPoints_eq_biUnion]
  ext z
  simp [persistentRootComponentLinearPointUnion]

/-- One persistent root label and one terminal witness determine the same
literal prime curve `Q`.  The terminal Bezout argument transfers its degree,
and containment of both equation ideals in `Q` proves that every point of
the root cell vanishes on both the source surface and the chosen terminal
cut. -/
theorem persistentRootCell_terminalData_and_vanishing
    {Point Vertex : Type*} [DecidableEq Vertex]
    {N d e : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : (finiteEquationIdeal sourceEquations).IsPrime)
    (hhom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    (G₀ G : MvPolynomial (Fin (N + 1)) ℚ)
    (equations : Point → Vertex →
      Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (coordinate : Point → Fin (N + 1) → ℚ)
    (vertices : Point → Finset Vertex)
    (cell : Finset Point)
    (x : Point) (v : Vertex)
    (o : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)))
    (hx : x ∈ cell)
    (hv : v ∈ vertices x)
    (ho : o ≠ none)
    (hpersistent : ∀ w ∈ vertices x,
      selectedFiniteEquationComponent (equations x w) (coordinate x) = o)
    (hequations : equations x v =
      finiteEquationFamilyUnion sourceEquations {G})
    (hGhom : G.IsHomogeneous e)
    (hGnot : G ∉ finiteEquationIdeal sourceEquations)
    (hrootSelected : ∀ z ∈ cell,
      selectedFiniteEquationComponent
        (finiteEquationFamilyUnion sourceEquations {G₀})
        (coordinate z) = o) :
    ∃ Q degreeQ,
      o = some Q ∧
      Q ∈ finiteEquationMinimalPrimes
        (finiteEquationFamilyUnion sourceEquations {G₀}) ∧
      Q ∈ finiteEquationMinimalPrimes
        (finiteEquationFamilyUnion sourceEquations {G}) ∧
      HasProjectiveDimensionDegree Q 1 degreeQ ∧
      degreeQ ≤ d * e ∧
      ∀ z ∈ cell,
        (∀ f ∈ finiteEquationIdeal sourceEquations,
          MvPolynomial.eval (coordinate z) f = 0) ∧
        MvPolynomial.eval (coordinate z) G = 0 := by
  classical
  obtain ⟨Q, degreeQ, hQo, hQterminal, hQdegree, hQdegreeBound⟩ :=
    persistentSelectedComponent_terminalDegree_le
      sourceEquations hprime hhom hdegree equations coordinate vertices
        x v o G hv ho hpersistent hequations hGhom hGnot
  have hrootWitnessSome : selectedFiniteEquationComponent
      (finiteEquationFamilyUnion sourceEquations {G₀})
      (coordinate x) = some Q :=
    (hrootSelected x hx).trans hQo
  have hQroot := (selectedFiniteEquationComponent_spec
    (finiteEquationFamilyUnion sourceEquations {G₀})
      (coordinate x) hrootWitnessSome).1
  have hrootIdeal : finiteEquationIdeal sourceEquations ≤ Q := by
    have hcontain := le_of_mem_finiteMinimalPrimes hQroot
    rw [finiteEquationIdeal_union] at hcontain
    exact le_sup_left.trans hcontain
  refine ⟨Q, degreeQ, hQo, hQroot, hQterminal,
    hQdegree, hQdegreeBound, ?_⟩
  intro z hz
  have hrootSome : selectedFiniteEquationComponent
      (finiteEquationFamilyUnion sourceEquations {G₀})
      (coordinate z) = some Q :=
    (hrootSelected z hz).trans hQo
  have hQkernel := (selectedFiniteEquationComponent_spec
    (finiteEquationFamilyUnion sourceEquations {G₀})
      (coordinate z) hrootSome).2
  have hterminalIdeal := le_of_mem_finiteMinimalPrimes hQterminal
  have hGfamily : G ∈ finiteEquationFamilyUnion sourceEquations {G} :=
    (mem_finiteEquationFamilyUnion sourceEquations {G} G).mpr
      (Or.inr (by simp))
  have hGideal : G ∈ finiteEquationIdeal
      (finiteEquationFamilyUnion sourceEquations {G}) :=
    Ideal.subset_span hGfamily
  refine ⟨?_, RingHom.mem_ker.mp (hQkernel (hterminalIdeal hGideal))⟩
  intro f hf
  exact RingHom.mem_ker.mp (hQkernel (hrootIdeal hf))

/-- Uniform aggregation over the actual nonempty root-component cells.
The root component count and degree mass are produced by the internal
Hilbert--Bezout theorem.  Each local nonlinear error comes from the existing
proper-cut Pila theorem.  Degree-one points from all cells occur once in the
literal global union. -/
theorem exists_uniform_persistentRootComponentCells_pila
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (N D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ)),
        d ≤ D →
        (finiteEquationIdeal sourceEquations).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin (N + 1)) ℚ) →
        X (0 : Fin (N + 1)) ∉ finiteEquationIdeal sourceEquations →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (G₀ : MvPolynomial (Fin (N + 1)) ℚ),
        G₀.IsHomogeneous e₀ →
        G₀ ∉ finiteEquationIdeal sourceEquations →
      ∀ {Vertex : Type*} [DecidableEq Vertex]
        (vertices : IntVector N → Finset Vertex)
        (equations : IntVector N → Vertex →
          Finset (MvPolynomial (Fin (N + 1)) ℚ))
        (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
          Finset (IntVector N))
        (representative : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
          IntVector N)
        (terminalVertex : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
          Vertex)
        (terminalDegree : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
          ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
          MvPolynomial (Fin (N + 1)) ℚ)
        (points : Finset (IntVector N)) (B : ℝ),
      let active := activePersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, representative o ∈ cell o) →
      (∀ o ∈ active, terminalVertex o ∈ vertices (representative o)) →
      (∀ o ∈ active, o ≠ none ∧
        ∀ w ∈ vertices (representative o),
          selectedFiniteEquationComponent
            (equations (representative o) w)
            (fun i => (integralAffineChartVector (representative o) i : ℚ)) = o) →
      (∀ o ∈ active,
        equations (representative o) (terminalVertex o) =
          finiteEquationFamilyUnion sourceEquations {terminalCut o}) →
      (∀ o ∈ active,
        (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ finiteEquationIdeal sourceEquations ∧
        terminalDegree o ≤ K) →
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (finiteEquationFamilyUnion sourceEquations {G₀})
          (fun i => (integralAffineChartVector z i : ℚ)) = o) →
      1 ≤ B →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i, |(z i : ℝ)| ≤ B) →
      points ⊆ active.biUnion cell →
      ∃ rootDegree : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (finiteEquationFamilyUnion sourceEquations {G₀}),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
          finiteEquationIdeal sourceEquations ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (rootDegree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
          (finiteEquationFamilyUnion sourceEquations {G₀}), rootDegree Q) ≤
            d * e₀ ∧
        active.card ≤ d * e₀ ∧
        (∀ o ∈ active, ∃ Q degreeQ,
          o = some Q ∧
          Q ∈ finiteEquationMinimalPrimes
            (finiteEquationFamilyUnion sourceEquations {G₀}) ∧
          HasProjectiveDimensionDegree Q 1 (rootDegree Q) ∧
          Q ∈ finiteEquationMinimalPrimes
            (finiteEquationFamilyUnion sourceEquations {terminalCut o}) ∧
          HasProjectiveDimensionDegree Q 1 degreeQ ∧
          degreeQ ≤ d * terminalDegree o) ∧
        (points.card : ℝ) ≤
          ((persistentRootComponentLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut cell).card : ℝ) +
          ((d * e₀ : ℕ) : ℝ) * C *
            (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hProperCut⟩ :=
    exists_uniform_surfaceProperCut_pila hPila hBezout N D K ε hε
  refine ⟨C, hC, ?_⟩
  intro d e₀ sourceEquations hd hprime hhom hchart hdegree
    G₀ hG₀hom hG₀not Vertex _ vertices equations cell representative
    terminalVertex terminalDegree terminalCut points B
  dsimp only
  intro hrepresentative hterminalVertex hpersistent hequations
    hterminalData hrootSelected hB hbox hcover
  let active := activePersistentRootComponentOptions sourceEquations G₀ cell
  let I := finiteEquationIdeal sourceEquations
  let linePoints := fun o : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (terminalCut o)) (cell o)
  let error := fun _o : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) =>
    C * (B + 1) ^ ((1 / 2 : ℝ) + ε)
  obtain ⟨rootDegree, hrootData, hrootMass, _hrootCard, hrootOptionsCard⟩ :=
    exists_geometricSurfaceRootComponentData sourceEquations
      hprime hhom hdegree G₀ hG₀hom hG₀not
  have hactiveSubset : active ⊆ finiteEquationComponentOptions
      (finiteEquationFamilyUnion sourceEquations {G₀}) := by
    intro o ho
    exact (mem_activePersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hactiveCard : active.card ≤ d * e₀ :=
    (Finset.card_le_card hactiveSubset).trans hrootOptionsCard
  have hcellData : ∀ o ∈ active, ∃ Q degreeQ,
      o = some Q ∧
      Q ∈ finiteEquationMinimalPrimes
        (finiteEquationFamilyUnion sourceEquations {G₀}) ∧
      Q ∈ finiteEquationMinimalPrimes
        (finiteEquationFamilyUnion sourceEquations {terminalCut o}) ∧
      HasProjectiveDimensionDegree Q 1 degreeQ ∧
      degreeQ ≤ d * terminalDegree o ∧
      ∀ z ∈ cell o,
        (∀ f ∈ I, MvPolynomial.eval
          (fun i => (integralAffineChartVector z i : ℚ)) f = 0) ∧
        MvPolynomial.eval
          (fun i => (integralAffineChartVector z i : ℚ))
          (terminalCut o) = 0 := by
    intro o ho
    exact persistentRootCell_terminalData_and_vanishing
      sourceEquations hprime hhom hdegree G₀ (terminalCut o)
      equations (fun z i => (integralAffineChartVector z i : ℚ))
      vertices (cell o) (representative o) (terminalVertex o) o
      (hrepresentative o ho) (hterminalVertex o ho)
      (hpersistent o ho).1 (hpersistent o ho).2
      (hequations o ho) (hterminalData o ho).1
      (hterminalData o ho).2.1 (hrootSelected o ho)
  have hlineSubset : ∀ o ∈ active, linePoints o ⊆ cell o := by
    intro o _ho
    exact finitePointsOnLinearCurveComponents_subset _ _
  have hlocal : ∀ o ∈ active,
      ((cell o).card : ℝ) ≤ ((linePoints o).card : ℝ) + error o := by
    intro o ho
    obtain ⟨Q, degreeQ, hQo, hQroot, hQterminal, hQdegree,
      hQdegreeBound, hvanish⟩ := hcellData o ho
    exact hProperCut d (terminalDegree o) hd (hterminalData o ho).2.2
      I (terminalCut o) hprime hhom hchart hdegree
      (hterminalData o ho).1 (hterminalData o ho).2.1
      (cell o) B hB (hbox o ho)
      (fun z hz => (hvanish z hz).1)
      (fun z hz => (hvanish z hz).2)
  have htotal := card_le_globalDistinguished_add_sum_errors
    points active cell linePoints error hcover hlineSubset hlocal
  have hsum : (∑ o ∈ active, error o) =
      (active.card : ℝ) *
        (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) := by
    simp [error]
  rw [hsum] at htotal
  have herrorNonneg : 0 ≤ C *
      (B + 1) ^ ((1 / 2 : ℝ) + ε) :=
    mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hactiveCast : (active.card : ℝ) ≤ ((d * e₀ : ℕ) : ℝ) := by
    exact_mod_cast hactiveCard
  have herrorBound : (active.card : ℝ) *
      (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) ≤
      ((d * e₀ : ℕ) : ℝ) * C *
        (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
    calc
      (active.card : ℝ) *
          (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) ≤
        ((d * e₀ : ℕ) : ℝ) *
          (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) :=
            mul_le_mul_of_nonneg_right hactiveCast herrorNonneg
      _ = ((d * e₀ : ℕ) : ℝ) * C *
          (B + 1) ^ ((1 / 2 : ℝ) + ε) := by ring
  refine ⟨rootDegree, hrootData, hrootMass, hactiveCard, ?_, ?_⟩
  · intro o ho
    obtain ⟨Q, degreeQ, hQo, hQroot, hQterminal, hQdegree,
      hQdegreeBound, _hvanish⟩ := hcellData o ho
    exact ⟨Q, degreeQ, hQo, hQroot, (hrootData Q hQroot).2.2.2,
      hQterminal, hQdegree, hQdegreeBound⟩
  · have hlineEq : active.biUnion linePoints =
        persistentRootComponentLinearPointUnion I active terminalCut cell := by
      rfl
    rw [← hlineEq]
    exact htotal.trans (add_le_add (le_refl _) herrorBound)

/-- Bezout bounds the number of actual tagged degree-one occurrences in the
terminal cuts, one cut for each active root cell.  This is derived from the
literal component lists; no persistent-family cardinality is assumed. -/
theorem card_persistentRootComponent_taggedLines_le
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {N d K : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hchart : X (0 : Fin (N + 1)) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ I ∧ terminalDegree o ≤ K) :
    Fintype.card (TaggedLinearComponent
      (fun o : {o // o ∈ active} =>
        realAffineChartIntersectionIdeal I (terminalCut o.1))) ≤
      active.card * (d * K) := by
  classical
  rw [card_taggedLinearComponent]
  calc
    (∑ o : {o // o ∈ active},
        (linearAffineComponents
          (realAffineChartIntersectionIdeal I (terminalCut o.1))).card) ≤
      ∑ _o : {o // o ∈ active}, d * K := by
        apply Finset.sum_le_sum
        intro o _ho
        have hdata := hterminal o.1 o.2
        exact (Finset.card_filter_le _ _).trans
          ((projectiveSurfaceAffineHypersurface_componentCount_le
            hBezout I (terminalCut o.1) hprime hhom hchart hdegree
              hdata.1 hdata.2.1).trans
            (Nat.mul_le_mul_left d hdata.2.2))
    _ = active.card * (d * K) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        smul_eq_mul]

/-- Combining the proved root-cell count with the preceding literal Bezout
count gives the line-occurrence budget used by a later global line ledger. -/
theorem card_persistentRootComponent_taggedLines_le_rootMass
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    {N d e₀ K : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hchart : X (0 : Fin (N + 1)) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I 2 d)
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))))
    (terminalDegree : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) → ℕ)
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (hactive : active.card ≤ d * e₀)
    (hterminal : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ I ∧ terminalDegree o ≤ K) :
    Fintype.card (TaggedLinearComponent
      (fun o : {o // o ∈ active} =>
        realAffineChartIntersectionIdeal I (terminalCut o.1))) ≤
      (d * e₀) * (d * K) := by
  exact (card_persistentRootComponent_taggedLines_le hBezout I hprime
    hhom hchart hdegree active terminalDegree terminalCut hterminal).trans
      (Nat.mul_le_mul_right (d * K) hactive)

/-- Every active degree-one occurrence in the literal persistent-root union
has the existing full integral-line parametrization.  Moreover, that entire
line lies in the corresponding terminal intersection, not merely the sampled
finite point set. -/
theorem exists_persistentRootComponent_fullIntegralLines
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) ℚ)) →
      Finset (IntVector N)) :
    let J := fun o : {o // o ∈ active} =>
      realAffineChartIntersectionIdeal I (terminalCut o.1)
    let Y := fun o : {o // o ∈ active} => cell o.1
    ∃ (base direction : TaggedLinearComponent J → IntVector N)
      (parameter : TaggedLinearComponent J → IntVector N → ℤ),
      ∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1)) : Set (IntVector N)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x => x.2.1),
          z = fun i => base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ =>
            fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        Set.range (fun t : ℝ =>
          fun i => (base o i : ℝ) + t * (direction o i : ℝ)) ⊆
          affineIdealZeroLocus (J o.1) := by
  classical
  dsimp only
  let J := fun o : {o // o ∈ active} =>
    realAffineChartIntersectionIdeal I (terminalCut o.1)
  let Y := fun o : {o // o ∈ active} => cell o.1
  obtain ⟨base, direction, parameter, hdata⟩ :=
    exists_activeTaggedLinearComponent_fullIntegralLines hline J Y
  refine ⟨base, direction, parameter, ?_⟩
  intro o ho
  have hoData := hdata o ho
  refine ⟨hoData.1, hoData.2.1, hoData.2.2.1,
    hoData.2.2.2, ?_⟩
  intro y hy
  have hyQ : y ∈ affineIdealZeroLocus o.2.1 := by
    rw [hoData.2.2.2]
    exact hy
  have hQmin : o.2.1 ∈ finiteMinimalPrimes (J o.1) :=
    ((mem_linearAffineComponents_iff (J o.1) o.2.1).mp o.2.2).1
  have hJQ : J o.1 ≤ o.2.1 := le_of_mem_finiteMinimalPrimes hQmin
  intro f hf
  exact hyQ f (hJQ hf)

end

end TranslatedDepthSeven
