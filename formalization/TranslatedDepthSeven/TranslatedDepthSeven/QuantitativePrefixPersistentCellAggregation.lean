import TranslatedDepthSeven.QbarPersistentRootCellVanishing
import TranslatedDepthSeven.QbarPersistentRootComponentCellAggregation
import TranslatedDepthSeven.PersistentRootComponentCellAggregation
import TranslatedDepthSeven.GlobalDistinguishedUnionAggregation
import TranslatedDepthSeven.SurfaceProperCutPila

/-!
# Persistent prefix cells in the actual affine progression

The rooted partition is a partition of displacement vectors `z`, while the
rational surface and its auxiliary cuts contain the affine points `u + m z`.
For positive `m` this affine map is injective.  We choose one full-depth
surviving prefix for each nonempty persistent root cell, apply the proper-cut
Pila theorem to the image cell, and retain all degree-one points in one
literal global union.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 500000

local instance quantitativePrefixPersistentPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

/-- The persistent cell with geometric root label `o`. -/
def quantitativePrefixPersistentCell
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ)
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) :
    Finset (IntVector 3) :=
  X.filter fun z =>
    o ≠ none ∧ ∀ v ∈
      PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      selectedFiniteEquationComponent
        (quantitativePrefixCutEquations sourceEquations auxiliary z v)
        (quantitativePrefixCoordinate u m z) = o

/-- The image of one displacement cell in the actual affine progression. -/
def quantitativePrefixPersistentAffineCell
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3))
    (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) :
    Finset (IntVector 3) :=
  (cell o).image fun z => integralAffineMap u z m

/-- All rational degree-one points from the selected terminal cuts, united
once in the actual affine `u + m z` coordinates. -/
def quantitativePrefixPersistentLinearPointUnion
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
    (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ)
    (u : IntVector 3) (m : ℕ)
    (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      Finset (IntVector 3)) : Finset (IntVector 3) :=
  active.biUnion fun o =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal I (terminalCut o))
      (quantitativePrefixPersistentAffineCell u m cell o)

/-- Distinct persistent labels give disjoint displacement cells because the
modulus-one root survives for every point. -/
theorem quantitativePrefixPersistentCells_pairwiseDisjoint
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ)
    (labels : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar)))) :
    (↑labels : Set (Option (Ideal (MvPolynomial (Fin 4) Qbar)))).PairwiseDisjoint
      (quantitativePrefixPersistentCell sourceEquations auxiliary
        u m X allowed) := by
  classical
  intro o _ho r _hr hor
  change Disjoint
    (quantitativePrefixPersistentCell sourceEquations auxiliary u m X allowed o)
    (quantitativePrefixPersistentCell sourceEquations auxiliary u m X allowed r)
  rw [Finset.disjoint_left]
  intro z hzo hzr
  have hzoData := (Finset.mem_filter.mp hzo).2
  have hzrData := (Finset.mem_filter.mp hzr).2
  let root := PrimeSubsetPrefix.root P depth
  have hoRoot := hzoData.2 root
    (PrimeSubsetPrefix.root_mem_surviving P (allowed z) depth)
  have hrRoot := hzrData.2 root
    (PrimeSubsetPrefix.root_mem_surviving P (allowed z) depth)
  exact hor (hoRoot.symm.trans hrRoot)

/-- The persistent sum in the rooted partition is exactly the cardinality
of the union of the nonempty root-option cells. -/
theorem sum_quantitativePrefixPersistentCells_card_eq_activeUnion
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    {P : Finset ℕ} {depth : ℕ}
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (u : Fin 3 → ℤ) (m : ℕ) (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ) (z₀ : IntVector 3) :
    let root := PrimeSubsetPrefix.root P depth
    let G₀ := auxiliary root (integralResidueVector z₀)
    let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
      u m X allowed
    let labels := finiteEquationComponentOptions
      (qbarSurfaceCutEquationFamily sourceEquations G₀)
    let active := activeQbarPersistentRootComponentOptions
      sourceEquations G₀ cell
    (∑ o ∈ labels, (cell o).card) = (active.biUnion cell).card := by
  classical
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let labels := finiteEquationComponentOptions
    (qbarSurfaceCutEquationFamily sourceEquations G₀)
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  have hactiveSubset : active ⊆ labels := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hsum : (∑ o ∈ active, (cell o).card) =
      ∑ o ∈ labels, (cell o).card := by
    apply Finset.sum_subset hactiveSubset
    intro o hoLabels hnotActive
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    exact hnotActive
      ((mem_activeQbarPersistentRootComponentOptions_iff
        sourceEquations G₀ cell o).mpr ⟨hoLabels, hnonempty⟩)
  have hpairs := quantitativePrefixPersistentCells_pairwiseDisjoint
    sourceEquations auxiliary u m X allowed active
  have hunion : (active.biUnion cell).card =
      ∑ o ∈ active, (cell o).card := Finset.card_biUnion hpairs
  rw [← hsum, ← hunion]

/-- Uniform persistent-cell estimate for one actual quantitative prefix
family.  A full-depth surviving vertex is selected in each nonempty root
cell.  The natural bound `K` is deliberately explicit: later numerical work
must supply a uniform terminal-degree bound appropriate for the chosen Pila
input. -/
theorem exists_uniform_quantitativePrefixPersistentCells_pila
    (hPila : Pila1995TheoremA)
    (hBezout : StandardAG.ProjectiveSurfaceAffineHypersurfaceBezout)
    (D K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        d ≤ D →
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        MvPolynomial.X 0 ∉ finiteEquationIdeal sourceEquations →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (hm : 0 < m)
        (X : Finset (IntVector 3))
        (allowed : IntVector 3 → Finset ℕ)
        (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
        (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
          (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
            MvPolynomial (Fin 4) ℚ)
        (z₀ : IntVector 3),
      z₀ ∈ X →
      (∀ z ∈ X, allowed z ⊆ P) →
      (∀ z ∈ X, depth ≤ (allowed z).card) →
      (∀ v : PrimeSubsetPrefix.Vertex P depth,
        ∀ ρ ∈ occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus v) X,
          (auxiliary v ρ).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v ρ ∉ finiteEquationIdeal sourceEquations) →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        v.1.card = depth → b + blockDegree v ≤ K) →
      ∀ B : ℝ, 1 ≤ B →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ)| ≤ B) →
      let root := PrimeSubsetPrefix.root P depth
      let G₀ := auxiliary root (integralResidueVector z₀)
      let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
        u m X allowed
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      ∃ (representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          IntVector 3)
        (terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          PrimeSubsetPrefix.Vertex P depth)
        (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          MvPolynomial (Fin 4) ℚ),
        (∀ o ∈ active, representative o ∈ cell o) ∧
        (∀ o ∈ active,
          terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
            (allowed (representative o)) depth ∧
          (terminalVertex o).1.card = depth) ∧
        (∀ o,
          terminalDegree o = b + blockDegree (terminalVertex o) ∧
          terminalCut o = auxiliary (terminalVertex o)
            (integralResidueVector (representative o))) ∧
        active.card ≤ d * (b + blockDegree root) ∧
        (((active.biUnion cell).card : ℕ) : ℝ) ≤
          ((quantitativePrefixPersistentLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut
              u m cell).card : ℝ) +
          ((d * (b + blockDegree root) : ℕ) : ℝ) * C *
            (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
  classical
  obtain ⟨C, hC, hProperCut⟩ :=
    exists_uniform_surfaceProperCut_pila hPila hBezout 3 D K ε hε
  refine ⟨C, hC, ?_⟩
  intro d b sourceEquations hd hprime hgeometricPrime hhom hchart hdegree
    P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hterminalBound B hB hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let representative : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      IntVector 3 := fun o =>
    dite (cell o).Nonempty (fun h => Classical.choose h) (fun _ => 0)
  have hrepresentative : ∀ o ∈ active, representative o ∈ cell o := by
    intro o ho
    have hnonempty : (cell o).Nonempty :=
      (mem_activeQbarPersistentRootComponentOptions_iff
        sourceEquations G₀ cell o).mp ho |>.2
    dsimp only [representative]
    rw [dif_pos hnonempty]
    exact Classical.choose_spec hnonempty
  have hrepresentativeX : ∀ o ∈ active, representative o ∈ X := by
    intro o ho
    exact Finset.filter_subset _ _ (hrepresentative o ho)
  have hterminalExists : ∀ o ∈ active,
      ∃ v ∈ PrimeSubsetPrefix.survivingVertices P
          (allowed (representative o)) depth,
        v.1.card = depth := by
    intro o ho
    exact exists_fullDepth_survivingPrefix P (allowed (representative o)) depth
      (hallowed _ (hrepresentativeX o ho))
      (hroom _ (hrepresentativeX o ho))
  let terminalVertex : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      PrimeSubsetPrefix.Vertex P depth := fun o =>
    dite (o ∈ active)
      (fun ho => Classical.choose (hterminalExists o ho))
      (fun _ => root)
  have hterminalVertex : ∀ o ∈ active,
      terminalVertex o ∈ PrimeSubsetPrefix.survivingVertices P
          (allowed (representative o)) depth ∧
        (terminalVertex o).1.card = depth := by
    intro o ho
    dsimp only [terminalVertex]
    rw [dif_pos ho]
    exact Classical.choose_spec (hterminalExists o ho)
  let terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ :=
    fun o => b + blockDegree (terminalVertex o)
  let terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
      MvPolynomial (Fin 4) ℚ := fun o =>
    auxiliary (terminalVertex o)
      (integralResidueVector (representative o))
  have hrootOccupied : integralResidueVector z₀ ∈
      occupiedIntegralResidues (PrimeSubsetPrefix.modulus root) X :=
    mem_occupiedIntegralResidues_iff.mpr ⟨z₀, hz₀, rfl⟩
  have hG₀data := hauxiliary root _ hrootOccupied
  have hrootEquation : ∀ z ∈ X,
      quantitativePrefixCutEquations sourceEquations auxiliary z root =
        qbarSurfaceCutEquationFamily sourceEquations G₀ := by
    intro z _hz
    have hresidue :
        (integralResidueVector z :
          Fin 3 → ZMod (PrimeSubsetPrefix.modulus root)) =
        integralResidueVector z₀ := by
      rw [show PrimeSubsetPrefix.modulus root = 1 by
        exact PrimeSubsetPrefix.modulus_root P depth]
      exact Subsingleton.elim _ _
    simp only [quantitativePrefixCutEquations, G₀]
    rw [hresidue]
  have hrootSelected : ∀ o ∈ active, ∀ z ∈ cell o,
      selectedFiniteEquationComponent
        (qbarSurfaceCutEquationFamily sourceEquations G₀)
        (quantitativePrefixCoordinate u m z) = o := by
    intro o ho z hz
    have hzData := (Finset.mem_filter.mp hz).2
    have hlabel := hzData.2 root
      (PrimeSubsetPrefix.root_mem_surviving P (allowed z) depth)
    rw [hrootEquation z (Finset.filter_subset _ _ hz)] at hlabel
    exact hlabel
  have hpersistent : ∀ o ∈ active,
      o ≠ none ∧ ∀ w ∈ PrimeSubsetPrefix.survivingVertices P
          (allowed (representative o)) depth,
        selectedFiniteEquationComponent
          (quantitativePrefixCutEquations sourceEquations auxiliary
            (representative o) w)
          (quantitativePrefixCoordinate u m (representative o)) = o := by
    intro o ho
    exact (Finset.mem_filter.mp (hrepresentative o ho)).2
  have hterminalData : ∀ o ∈ active,
      (terminalCut o).IsHomogeneous (terminalDegree o) ∧
      terminalCut o ∉ finiteEquationIdeal sourceEquations ∧
      terminalDegree o ≤ K := by
    intro o ho
    have hrepX := hrepresentativeX o ho
    have hocc : integralResidueVector (representative o) ∈
        occupiedIntegralResidues
          (PrimeSubsetPrefix.modulus (terminalVertex o)) X :=
      mem_occupiedIntegralResidues_iff.mpr
        ⟨representative o, hrepX, rfl⟩
    have hdata := hauxiliary (terminalVertex o) _ hocc
    exact ⟨by simpa only [terminalCut, terminalDegree] using hdata.1,
      by simpa only [terminalCut] using hdata.2,
      by
        simpa only [terminalDegree] using
          hterminalBound (representative o) hrepX (terminalVertex o)
            (hterminalVertex o ho).1 (hterminalVertex o ho).2⟩
  have hcellVanishing : ∀ o ∈ active, ∀ z ∈ cell o,
      (∀ f ∈ finiteEquationIdeal sourceEquations,
        MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ)) f = 0) ∧
      MvPolynomial.eval
        (fun i => (progressionHomogeneousPoint u m z i : ℚ))
        (terminalCut o) = 0 := by
    intro o ho
    obtain ⟨_Q, _hQo, _hQroot, _hQterminal, hvanish⟩ :=
      qbarPersistentRootCell_rationalVanishing
        sourceEquations G₀ (terminalCut o)
        (quantitativePrefixCutEquations sourceEquations auxiliary)
        (fun z i => (progressionHomogeneousPoint u m z i : ℚ))
        (fun z => PrimeSubsetPrefix.survivingVertices P (allowed z) depth)
        (cell o) (representative o) (terminalVertex o) o
        (hrepresentative o ho) (hterminalVertex o ho).1
        (hpersistent o ho).1 (hpersistent o ho).2 (by rfl)
        (by
          intro z hz
          simpa only [quantitativePrefixCoordinate] using
            hrootSelected o ho z hz)
    exact hvanish
  let affineMap : IntVector 3 → IntVector 3 := fun z => integralAffineMap u z m
  let affineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) =>
    (cell o).image affineMap
  let linePoints := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) =>
    finitePointsOnLinearCurveComponents
      (realAffineChartIntersectionIdeal
        (finiteEquationIdeal sourceEquations) (terminalCut o))
      (affineCell o)
  let error := fun _o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) =>
    C * (B + 1) ^ ((1 / 2 : ℝ) + ε)
  have haffineInjective : Function.Injective affineMap := by
    exact integralAffineMap_injective hm u
  have hchartEq (z : IntVector 3) :
      (fun i => (integralAffineChartVector (affineMap z) i : ℚ)) =
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [affineMap, integralAffineMap, integralAffineChartVector,
        progressionHomogeneousPoint]
  have hlineSubset : ∀ o ∈ active, linePoints o ⊆ affineCell o := by
    intro o _ho
    exact finitePointsOnLinearCurveComponents_subset _ _
  have hlocal : ∀ o ∈ active,
      ((affineCell o).card : ℝ) ≤ ((linePoints o).card : ℝ) + error o := by
    intro o ho
    apply hProperCut d (terminalDegree o) hd (hterminalData o ho).2.2
      (finiteEquationIdeal sourceEquations) (terminalCut o)
      hprime hhom hchart hdegree
      (hterminalData o ho).1 (hterminalData o ho).2.1
      (affineCell o) B hB
    · intro x hx i
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      exact hbox z (Finset.filter_subset _ _ hz) i
    · intro x hx f hf
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rw [hchartEq]
      exact (hcellVanishing o ho z hz).1 f hf
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      rw [hchartEq]
      exact (hcellVanishing o ho z hz).2
  let persistentPoints := active.biUnion cell
  let affinePoints := persistentPoints.image affineMap
  have hcover : affinePoints ⊆ active.biUnion affineCell := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨o, ho, hzcell⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr
      ⟨o, ho, Finset.mem_image.mpr ⟨z, hzcell, rfl⟩⟩
  have htotal := card_le_globalDistinguished_add_sum_errors
    affinePoints active affineCell linePoints error hcover hlineSubset hlocal
  have hsum : (∑ o ∈ active, error o) =
      (active.card : ℝ) *
        (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) := by
    simp [error]
  rw [hsum] at htotal
  let E := qbarSurfaceEquationFamily sourceEquations
  let G₀bar := MvPolynomial.map (algebraMap ℚ Qbar) G₀
  have hprimeE : (finiteEquationIdeal E).IsPrime := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hhomE : (finiteEquationIdeal E).IsHomogeneous
      (homogeneousSubmodule (Fin 4) Qbar) := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) _ hhom
  have hdegreeE : HasProjectiveDimensionDegree (finiteEquationIdeal E) 2 d := by
    dsimp [E]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hG₀barHom : G₀bar.IsHomogeneous (b + blockDegree root) :=
    hG₀data.1.map _
  have hG₀barNot : G₀bar ∉ finiteEquationIdeal E := by
    dsimp [E, G₀bar]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hG₀data.2
  obtain ⟨_rootDegree, _hrootData, _hrootMass, _hrootCard,
      hrootOptionsCard⟩ :=
    exists_geometricSurfaceRootComponentData E hprimeE hhomE hdegreeE
      G₀bar hG₀barHom hG₀barNot
  have hrootFamily : finiteEquationFamilyUnion E {G₀bar} =
      qbarSurfaceCutEquationFamily sourceEquations G₀ := by rfl
  have hactiveSubset : active ⊆ finiteEquationComponentOptions
      (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hactiveCard : active.card ≤ d * (b + blockDegree root) := by
    apply (Finset.card_le_card hactiveSubset).trans
    rw [← hrootFamily]
    exact hrootOptionsCard
  have herrorNonneg : 0 ≤ C *
      (B + 1) ^ ((1 / 2 : ℝ) + ε) :=
    mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)
  have hactiveCast : (active.card : ℝ) ≤
      ((d * (b + blockDegree root) : ℕ) : ℝ) := by
    exact_mod_cast hactiveCard
  have herrorBound : (active.card : ℝ) *
      (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) ≤
      ((d * (b + blockDegree root) : ℕ) : ℝ) * C *
        (B + 1) ^ ((1 / 2 : ℝ) + ε) := by
    calc
      (active.card : ℝ) *
          (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) ≤
        ((d * (b + blockDegree root) : ℕ) : ℝ) *
          (C * (B + 1) ^ ((1 / 2 : ℝ) + ε)) :=
            mul_le_mul_of_nonneg_right hactiveCast herrorNonneg
      _ = ((d * (b + blockDegree root) : ℕ) : ℝ) * C *
          (B + 1) ^ ((1 / 2 : ℝ) + ε) := by ring
  have haffineCard : affinePoints.card = persistentPoints.card := by
    exact Finset.card_image_iff.mpr
      (Set.injOn_of_injective haffineInjective)
  have hlineEq : active.biUnion linePoints =
      quantitativePrefixPersistentLinearPointUnion
        (finiteEquationIdeal sourceEquations) active terminalCut u m cell := by
    rfl
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, ?_, hactiveCard, ?_⟩
  · intro o
    exact ⟨rfl, rfl⟩
  · change (persistentPoints.card : ℝ) ≤ _
    rw [← haffineCard, ← hlineEq]
    exact htotal.trans (add_le_add (le_refl _) herrorBound)

end

end TranslatedDepthSeven
