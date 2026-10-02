import CubicTenVariables.FixedLeadingSurfaceSurvivorResidual
import TranslatedDepthSeven.QuantitativePrefixSurfaceCountEffectiveTwoCapCenteredCurve

/-!
# Persistent-cell counting with survivor-only auxiliaries

This adapts the existing two-cap centered proof to the exact output of the
smooth-packet construction. Properness is used at the common root and each
selected surviving terminal vertex. The nonlinear curve input remains
explicit, with its constant chosen before all equations and degree caps.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfaceSurvivorPersistence

open MvPolynomial TranslatedDepthSeven Published
attribute [local instance] MvPolynomial.gradedAlgebra
local instance survivorPersistencePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The actual persistent-cell union is bounded by its actual line union
and the same two-cap nonlinear residual, with survivor-only properness. -/
theorem exists_uniform_persistentCells_twoCap_centered_of_survivor_auxiliaries
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b Lroot Lterminal : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (_hm : 0 < m)
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
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
          (auxiliary v (integralResidueVector z)).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉ finiteEquationIdeal sourceEquations) →
      b + blockDegree (PrimeSubsetPrefix.root P depth) ≤ Lroot →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        v.1.card = depth → b + blockDegree v ≤ Lterminal) →
      ∀ (center : RealVector 3) (R : ℝ), 0 ≤ R →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ R) →
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
          ((quantitativePrefixPersistentRationalLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut
              u m cell).card : ℝ) +
          C * ((d * Lroot : ℕ) : ℝ) *
            ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
            (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (m : ℝ) + 2) +
              ((d * Lterminal : ℕ) : ℝ)) := by
  classical
  obtain ⟨C, hC, hSurfaceCount⟩ :=
    exists_uniform_projectiveSurface_rationalAffineSection_effectiveCount_centered_progression
      hCurve (N := 3) (by omega)
  refine ⟨C, hC, ?_⟩
  intro d b Lroot Lterminal sourceEquations hprime hgeometricPrime hhom hdegree
    P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hterminalCap center R hR hbox
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
  have hG₀data := hauxiliary z₀ hz₀ root
    (PrimeSubsetPrefix.root_mem_surviving P (allowed z₀) depth)
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
      terminalDegree o ≤ Lterminal := by
    intro o ho
    have hrepX := hrepresentativeX o ho
    have hdata := hauxiliary (representative o) hrepX (terminalVertex o)
      (hterminalVertex o ho).1
    exact ⟨by simpa only [terminalCut, terminalDegree] using hdata.1,
      by simpa only [terminalCut] using hdata.2,
      by simpa only [terminalDegree] using
        hterminalCap (representative o) hrepX (terminalVertex o)
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
    finitePointsOnRationalLinearCurveComponents
      (rationalAffineChartIntersectionIdeal
        (finiteEquationIdeal sourceEquations) (terminalCut o))
      (affineCell o)
  let commonError : ℝ :=
    C * ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
      (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
      (Real.log (2 * R / (m : ℝ) + 2) +
        ((d * Lterminal : ℕ) : ℝ))
  let error := fun _o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) =>
    commonError
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
    exact finitePointsOnRationalLinearCurveComponents_subset_twoCap _ _
  have hlocal : ∀ o ∈ active,
      ((affineCell o).card : ℝ) ≤ ((linePoints o).card : ℝ) + error o := by
    intro o ho
    have hraw := hSurfaceCount d (terminalDegree o)
      (finiteEquationIdeal sourceEquations) (terminalCut o)
      hprime hhom hdegree (hterminalData o ho).1 (hterminalData o ho).2.1
      (affineCell o)
    have hrawApplied : ((affineCell o).card : ℝ) ≤
        ((linePoints o).card : ℝ) +
          C * ((d * terminalDegree o : ℕ) : ℝ) ^ (4 : ℕ) *
            (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (m : ℝ) + 2) +
              ((d * terminalDegree o : ℕ) : ℝ)) := by
      refine hraw ?_ ?_ m hm u ?_ center R hR ?_
      · intro x hx f hf
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        change MvPolynomial.eval
          (fun i => (integralAffineChartVector (affineMap z) i : ℚ)) f = 0
        rw [hchartEq]
        exact (hcellVanishing o ho z hz).1 f hf
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        change MvPolynomial.eval
          (fun i => (integralAffineChartVector (affineMap z) i : ℚ))
            (terminalCut o) = 0
        rw [hchartEq]
        exact (hcellVanishing o ho z hz).2
      · intro x hx i
        obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hx
        exact integralAffineMap_congruent u z i
      · intro x hx i
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        exact hbox z (Finset.filter_subset _ _ hz) i
    have hdegreeMul : d * terminalDegree o ≤ d * Lterminal :=
      Nat.mul_le_mul_left d (hterminalData o ho).2.2
    have hdegreeMulReal : ((d * terminalDegree o : ℕ) : ℝ) ≤
        ((d * Lterminal : ℕ) : ℝ) := by exact_mod_cast hdegreeMul
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hdiv : 0 ≤ 2 * R / (m : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) hR) hmReal.le
    have hlogNonneg : 0 ≤ Real.log (2 * R / (m : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    have herrorBound :
        C * ((d * terminalDegree o : ℕ) : ℝ) ^ (4 : ℕ) *
            (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
            (Real.log (2 * R / (m : ℝ) + 2) +
              ((d * terminalDegree o : ℕ) : ℝ)) ≤
          commonError := by
      dsimp only [commonError]
      gcongr
    exact hrawApplied.trans (by
      dsimp only [error]
      exact add_le_add (le_refl _) herrorBound)
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
      (active.card : ℝ) * commonError := by
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
  have hactiveCap : active.card ≤ d * Lroot :=
    hactiveCard.trans (Nat.mul_le_mul_left d hrootCap)
  have hcommonErrorNonneg : 0 ≤ commonError := by
    dsimp only [commonError]
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hdiv : 0 ≤ 2 * R / (m : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) hR) hmReal.le
    have hlog : 0 ≤ Real.log (2 * R / (m : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    positivity
  have hactiveCast : (active.card : ℝ) ≤ ((d * Lroot : ℕ) : ℝ) := by
    exact_mod_cast hactiveCap
  have herrorBound : (active.card : ℝ) * commonError ≤
      C * ((d * Lroot : ℕ) : ℝ) *
        ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
        (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
        (Real.log (2 * R / (m : ℝ) + 2) +
          ((d * Lterminal : ℕ) : ℝ)) := by
    calc
      (active.card : ℝ) * commonError ≤
          ((d * Lroot : ℕ) : ℝ) * commonError :=
        mul_le_mul_of_nonneg_right hactiveCast hcommonErrorNonneg
      _ = C * ((d * Lroot : ℕ) : ℝ) *
          ((d * Lterminal : ℕ) : ℝ) ^ (4 : ℕ) *
          (2 * R / (m : ℝ) + 2) ^ (1 / 2 : ℝ) *
          (Real.log (2 * R / (m : ℝ) + 2) +
            ((d * Lterminal : ℕ) : ℝ)) := by
        dsimp only [commonError]
        ring
  have haffineCard : affinePoints.card = persistentPoints.card := by
    exact Finset.card_image_iff.mpr
      (Set.injOn_of_injective haffineInjective)
  have hlineEq : active.biUnion linePoints =
      quantitativePrefixPersistentRationalLinearPointUnion
        (finiteEquationIdeal sourceEquations) active terminalCut u m cell := by
    rfl
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, ?_, hactiveCard, ?_⟩
  · intro o
    exact ⟨rfl, rfl⟩
  · change (persistentPoints.card : ℝ) ≤ _
    rw [← haffineCard, ← hlineEq]
    exact htotal.trans (add_le_add (le_refl _) herrorBound)


/-- Compose survivor-only persistence with the survivor-only root partition. -/
theorem exists_uniform_surfaceCount_twoCap_centered_of_survivor_auxiliaries
    (hCurve : CDHNV2025Corollary22) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d b Lroot Lterminal : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (P : Finset ℕ) (depth : ℕ)
        (u : IntVector 3) (m : ℕ) (_hm : 0 < m)
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
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
          (auxiliary v (integralResidueVector z)).IsHomogeneous (b + blockDegree v) ∧
            auxiliary v (integralResidueVector z) ∉ finiteEquationIdeal sourceEquations) →
      b + blockDegree (PrimeSubsetPrefix.root P depth) ≤ Lroot →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        v.1.card = depth → b + blockDegree v ≤ Lterminal) →
      (∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
        MvPolynomial.eval
          (fun i => (progressionHomogeneousPoint u m z i : ℚ))
            (auxiliary v (integralResidueVector z)) = 0) →
      (∀ z ∈ X,
        (fun i => (progressionHomogeneousPoint u m z i : ℚ)) ∈
          finiteAffineCommonZeroLocus sourceEquations) →
      ∀ (center : RealVector 3) (Rbox : ℝ), 0 ≤ Rbox →
      (∀ z ∈ X, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ Rbox) →
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
        (X.card : ℝ) ≤
          ((∑ v : PrimeSubsetPrefix.Vertex P depth,
            ∑ w : PrimeSubsetPrefix.Vertex P depth,
              (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
                u m X allowed v w).card : ℕ) : ℝ) +
          ((quantitativePrefixPersistentRationalLinearPointUnion
            (finiteEquationIdeal sourceEquations) active terminalCut
              u m cell).card : ℝ) +
          quantitativePrefixEffectiveCurveResidualTwoCapCentered
            C d Lroot Lterminal Rbox m := by
  classical
  obtain ⟨C, hC, hpersistent⟩ :=
    exists_uniform_persistentCells_twoCap_centered_of_survivor_auxiliaries
      hCurve
  refine ⟨C, hC, ?_⟩
  intro d b Lroot Lterminal sourceEquations hprime hgeometricPrime hhom
    hdegree P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
    hroom hauxiliary hrootCap hterminalCap hauxZero hsource
      center Rbox hRbox hbox
  dsimp only
  let root := PrimeSubsetPrefix.root P depth
  let G₀ := auxiliary root (integralResidueVector z₀)
  let cell := quantitativePrefixPersistentCell sourceEquations auxiliary
    u m X allowed
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  obtain ⟨representative, terminalVertex, terminalDegree, terminalCut,
      hrepresentative, hterminalVertex, hterminalDefs, hactiveCard,
      hpersistentBound⟩ :=
    hpersistent sourceEquations hprime hgeometricPrime hhom hdegree
      P depth u m hm X allowed blockDegree auxiliary z₀ hz₀ hallowed
      hroom hauxiliary hrootCap hterminalCap center Rbox hRbox hbox
  have hpartition := FixedLeadingSurfaceSurvivorResidual.geometricPartition_of_survivor_auxiliaries
    sourceEquations hgeometricPrime hhom hdegree P depth X allowed u m
    blockDegree auxiliary z₀ hz₀ hallowed hauxiliary hauxZero hsource
  have hpersistentSum :
      (∑ o ∈ finiteEquationComponentOptions
          (finiteEquationFamilyUnion
            (qbarSurfaceEquationFamily sourceEquations)
            {MvPolynomial.map (algebraMap ℚ Qbar) G₀}),
        (X.filter fun z =>
          o ≠ none ∧ ∀ v ∈
            PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
            selectedFiniteEquationComponent
                (quantitativePrefixCutEquations sourceEquations auxiliary z v)
                (quantitativePrefixCoordinate u m z) = o).card) =
        (active.biUnion cell).card := by
    simpa only [qbarSurfaceCutEquationFamily, cell, active, G₀, root,
      quantitativePrefixPersistentCell] using
      (sum_quantitativePrefixPersistentCells_card_eq_activeUnion
        sourceEquations auxiliary u m X allowed z₀)
  have hpartitionNat : X.card ≤
      (∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card) +
        (active.biUnion cell).card := by
    rw [← hpersistentSum]
    exact hpartition.1
  have hpartitionReal : (X.card : ℝ) ≤
      ((∑ v : PrimeSubsetPrefix.Vertex P depth,
        ∑ w : PrimeSubsetPrefix.Vertex P depth,
          (quantitativePrefixChangedEdgeCell sourceEquations auxiliary
            u m X allowed v w).card : ℕ) : ℝ) +
        ((active.biUnion cell).card : ℝ) := by
    exact_mod_cast hpartitionNat
  refine ⟨representative, terminalVertex, terminalDegree, terminalCut,
    hrepresentative, hterminalVertex, hterminalDefs, hactiveCard, ?_⟩
  dsimp only [active, cell, root, G₀,
    quantitativePrefixEffectiveCurveResidualTwoCapCentered]
    at hpersistentBound ⊢
  linarith


end CubicTenVariables.FixedLeadingSurfaceSurvivorPersistence
