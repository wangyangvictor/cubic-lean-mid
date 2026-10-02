import TranslatedDepthSeven.QbarPersistentRootCellVanishing
import TranslatedDepthSeven.SurfaceProperCutPila
import TranslatedDepthSeven.GlobalDistinguishedUnionAggregation

/-!
# Aggregating persistent geometric root cells over rational cuts

The component labels live over `Qbar`, but every terminal auxiliary is a
rational form.  The preceding descent lemma supplies the rational vanishing
needed by the proper-cut Pila theorem.  Nonlinear errors are summed over the
actual nonempty geometric root cells, while all degree-one points are retained
in one literal global union.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 400000

local instance qbarPersistentAggregationPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The nonempty persistent cells indexed by actual geometric components of
the fixed rational root cut after extension to `Qbar`. -/
def activeQbarPersistentRootComponentOptions
    {N : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (G₀ : MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
      Finset (IntVector N)) :
    Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar))) :=
  (finiteEquationComponentOptions
    (qbarSurfaceCutEquationFamily sourceEquations G₀)).filter
      fun o => (cell o).Nonempty

@[simp]
theorem mem_activeQbarPersistentRootComponentOptions_iff
    {N : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (G₀ : MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
      Finset (IntVector N))
    (o : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar))) :
    o ∈ activeQbarPersistentRootComponentOptions sourceEquations G₀ cell ↔
      o ∈ finiteEquationComponentOptions
        (qbarSurfaceCutEquationFamily sourceEquations G₀) ∧
      (cell o).Nonempty := by
  simp [activeQbarPersistentRootComponentOptions]

/-- One multiplicity-free union of the rational degree-one components from
all terminal cuts attached to active geometric root cells. -/
def qbarPersistentRootComponentLinearPointUnion
    {N : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
      MvPolynomial (Fin (N + 1)) ℚ)
    (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
      Finset (IntVector N)) : Finset (IntVector N) :=
  active.biUnion fun o =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (terminalCut o)) (cell o)

/-- Uniform Pila aggregation for cells indexed by geometric components.
The only count of cells is the literal root Bezout count over `Qbar`; no
catalogue or aggregate-family premise is assumed. -/
theorem exists_uniform_qbarPersistentRootComponentCells_pila
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (N D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin (N + 1)) ℚ)),
        d ≤ D →
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
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
          Finset (MvPolynomial (Fin (N + 1)) Qbar))
        (cell : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
          Finset (IntVector N))
        (representative : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
          IntVector N)
        (terminalVertex : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
          Vertex)
        (terminalDegree : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
          ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) →
          MvPolynomial (Fin (N + 1)) ℚ)
        (points : Finset (IntVector N)) (B : ℝ),
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, representative o ∈ cell o) →
      (∀ o ∈ active, terminalVertex o ∈ vertices (representative o)) →
      (∀ o ∈ active, o ≠ none ∧
        ∀ w ∈ vertices (representative o),
          selectedFiniteEquationComponent
            (equations (representative o) w)
            (fun i => ((integralAffineChartVector (representative o) i : ℚ) : Qbar)) = o) →
      (∀ o ∈ active,
        equations (representative o) (terminalVertex o) =
          qbarSurfaceCutEquationFamily sourceEquations (terminalCut o)) →
      (∀ o ∈ active,
        (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ finiteEquationIdeal sourceEquations ∧
        terminalDegree o ≤ K) →
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i => ((integralAffineChartVector z i : ℚ) : Qbar)) = o) →
      1 ≤ B →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i, |(z i : ℝ)| ≤ B) →
      points ⊆ active.biUnion cell →
      active.card ≤ d * e₀ ∧
        (points.card : ℝ) ≤
          ((qbarPersistentRootComponentLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut cell).card : ℝ) +
          ((d * e₀ : ℕ) : ℝ) * C *
            (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hProperCut⟩ :=
    exists_uniform_surfaceProperCut_pila hPila hBezout N D K ε hε
  refine ⟨C, hC, ?_⟩
  intro d e₀ sourceEquations hd hprime hgeometricPrime hhom hchart hdegree
    G₀ hG₀hom hG₀not Vertex _ vertices equations cell representative
    terminalVertex terminalDegree terminalCut points B
  dsimp only
  intro hrepresentative hterminalVertex hpersistent hequations
    hterminalData hrootSelected hB hbox hcover
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let I := finiteEquationIdeal sourceEquations
  let linePoints := fun o : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (terminalCut o)) (cell o)
  let error := fun _o : Option (Ideal (MvPolynomial (Fin (N + 1)) Qbar)) =>
    C * (B + 1) ^ ((1 / 2 : ℝ) + ε)
  let E := qbarSurfaceEquationFamily sourceEquations
  let G₀bar := MvPolynomial.map (algebraMap ℚ Qbar) G₀
  have hprimeE : (finiteEquationIdeal E).IsPrime := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hhomE : (finiteEquationIdeal E).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) Qbar) := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) _ hhom
  have hdegreeE : HasProjectiveDimensionDegree (finiteEquationIdeal E) 2 d := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hG₀barHom : G₀bar.IsHomogeneous e₀ := hG₀hom.map _
  have hG₀barNot : G₀bar ∉ finiteEquationIdeal E := by
    dsimp [E, G₀bar]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hG₀not
  obtain ⟨_rootDegree, _hrootData, _hrootMass, _hrootCard,
      hrootOptionsCard⟩ :=
    exists_geometricSurfaceRootComponentData E hprimeE hhomE hdegreeE
      G₀bar hG₀barHom hG₀barNot
  have hrootFamily : finiteEquationFamilyUnion E {G₀bar} =
      qbarSurfaceCutEquationFamily sourceEquations G₀ := by
    rfl
  have hactiveSubset : active ⊆ finiteEquationComponentOptions
      (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hactiveCard : active.card ≤ d * e₀ := by
    apply (Finset.card_le_card hactiveSubset).trans
    rw [← hrootFamily]
    exact hrootOptionsCard
  have hcellVanishing : ∀ o ∈ active, ∀ z ∈ cell o,
      (∀ f ∈ I, MvPolynomial.eval
        (fun i => (integralAffineChartVector z i : ℚ)) f = 0) ∧
      MvPolynomial.eval
        (fun i => (integralAffineChartVector z i : ℚ))
        (terminalCut o) = 0 := by
    intro o ho
    obtain ⟨_Q, _hQo, _hQroot, _hQterminal, hvanish⟩ :=
      qbarPersistentRootCell_rationalVanishing
        sourceEquations G₀ (terminalCut o) equations
        (fun z i => (integralAffineChartVector z i : ℚ)) vertices
        (cell o) (representative o) (terminalVertex o) o
        (hrepresentative o ho) (hterminalVertex o ho)
        (hpersistent o ho).1 (hpersistent o ho).2
        (hequations o ho) (hrootSelected o ho)
    exact hvanish
  have hlineSubset : ∀ o ∈ active, linePoints o ⊆ cell o := by
    intro o _ho
    exact finitePointsOnLinearCurveComponents_subset _ _
  have hlocal : ∀ o ∈ active,
      ((cell o).card : ℝ) ≤ ((linePoints o).card : ℝ) + error o := by
    intro o ho
    exact hProperCut d (terminalDegree o) hd (hterminalData o ho).2.2
      I (terminalCut o) hprime hhom hchart hdegree
      (hterminalData o ho).1 (hterminalData o ho).2.1
      (cell o) B hB (hbox o ho)
      (fun z hz => (hcellVanishing o ho z hz).1)
      (fun z hz => (hcellVanishing o ho z hz).2)
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
  refine ⟨hactiveCard, ?_⟩
  have hlineEq : active.biUnion linePoints =
      qbarPersistentRootComponentLinearPointUnion I active terminalCut cell := by
    rfl
  rw [← hlineEq]
  exact htotal.trans (add_le_add (le_refl _) herrorBound)

end

end TranslatedDepthSeven
