import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
import CubicTenVariables.FixedLeadingSurfaceCenteredCurveCountInternal

/-! The persistent root degree split with bounded nonlinear curves counted
internally. The geometric component ledger and conjugate-intersection
argument are reused from the earlier proof; no Pila premise is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplitInternal
open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfacePersistentRootDegreeSplit
open FixedLeadingSurfaceCenteredCurveCountInternal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem exists_uniform_persistentRoot_degreeSplit
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (G₀ : MvPolynomial (Fin 4) ℚ),
        G₀.IsHomogeneous e₀ →
        G₀ ∉ finiteEquationIdeal sourceEquations →
      ∀ (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3))
        (u : IntVector 3) (m : ℕ), 0 < m →
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o) →
      ∀ (center : RealVector 3) (R : ℝ), 0 ≤ R →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ R) →
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ ∧
        active.card ≤ d * e₀ ∧
        ∀ (highConstant : ℕ → ℝ),
          Salberger2023Lemma313PersistentRootCallback sourceEquations G₀
            cell degree cutoff highConstant
              ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) →
          (((active.biUnion cell).card : ℕ) : ℝ) ≤
            ((persistentRootLinePointUnion degree active cell).card : ℝ) +
              ∑ o ∈ active,
                persistentRootDegreeSplitError degree cutoff
                  ((cutoff : ℝ) ^ 2 +
                    C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                  highConstant
                    ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o := by
  classical
  obtain ⟨C, hC, hLow⟩ :=
    exists_uniform_qbarProjectiveCurve_centeredPacket_internal
      3 cutoff (by decide) ε hε
  refine ⟨C, hC, ?_⟩
  intro d e₀ sourceEquations hprime hgeometricPrime hhom hdegree
    G₀ hG₀hom hG₀not cell u m hm
  dsimp only
  intro hrootSelected center R hR hbox
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
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
  have hG₀barHom : G₀bar.IsHomogeneous e₀ := hG₀hom.map _
  have hG₀barNot : G₀bar ∉ finiteEquationIdeal E := by
    dsimp [E, G₀bar]
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ _ hG₀not
  obtain ⟨degree, hrootData, hrootMass, _hrootCard, hrootOptionsCard⟩ :=
    exists_geometricSurfaceRootComponentData E hprimeE hhomE hdegreeE
      G₀bar hG₀barHom hG₀barNot
  have hrootFamily : finiteEquationFamilyUnion E {G₀bar} =
      qbarSurfaceCutEquationFamily sourceEquations G₀ := by rfl
  have hrootData' : ∀ Q ∈ finiteEquationMinimalPrimes
      (qbarSurfaceCutEquationFamily sourceEquations G₀),
      Q.IsPrime ∧ Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
        finiteEquationIdeal E ≤ Q ∧
        HasProjectiveDimensionDegree Q 1 (degree Q) := by
    intro Q hQ
    apply hrootData Q
    rwa [hrootFamily]
  have hrootMass' :
      (∑ Q ∈ finiteEquationMinimalPrimes
        (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ := by
    rwa [hrootFamily] at hrootMass
  have hactiveSubset : active ⊆ finiteEquationComponentOptions
      (qbarSurfaceCutEquationFamily sourceEquations G₀) := by
    intro o ho
    exact (mem_activeQbarPersistentRootComponentOptions_iff
      sourceEquations G₀ cell o).mp ho |>.1
  have hactiveCard : active.card ≤ d * e₀ := by
    apply (Finset.card_le_card hactiveSubset).trans
    rw [← hrootFamily]
    exact hrootOptionsCard
  refine ⟨degree, hrootData', hrootMass', hactiveCard, ?_⟩
  intro highConstant hHigh
  let affineMap : IntVector 3 → IntVector 3 := fun z ↦ integralAffineMap u z m
  let affineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    (cell o).image affineMap
  let lineCell := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    if rootOptionDegree degree o = 1 then cell o else ∅
  let side : ℝ := 2 * R / (m : ℝ) + 2
  let volume : ℝ := side ^ (3 : ℕ)
  let lowError : ℝ :=
    (cutoff : ℝ) ^ 2 + C * side ^ ((1 / 2 : ℝ) + ε)
  let error := fun o : Option (Ideal (MvPolynomial (Fin 4) Qbar)) ↦
    persistentRootDegreeSplitError degree cutoff lowError
      highConstant volume o
  have haffineInjective : Function.Injective affineMap :=
    integralAffineMap_injective hm u
  have hchartEq (z : IntVector 3) :
      (fun i ↦ ((integralAffineChartVector (affineMap z) i : ℤ) : Qbar)) =
        (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp [affineMap, integralAffineMap, integralAffineChartVector,
        progressionHomogeneousPoint]
  have hlineSubset : ∀ o ∈ active, lineCell o ⊆ cell o := by
    intro o _ho
    dsimp only [lineCell]
    split <;> simp
  have hlocal : ∀ o ∈ active,
      ((cell o).card : ℝ) ≤ ((lineCell o).card : ℝ) + error o := by
    intro o ho
    have hcomponent := hactiveSubset ho
    obtain ⟨Q, hQmin, hQo⟩ :=
      (mem_finiteEquationComponentOptions_iff
        (qbarSurfaceCutEquationFamily sourceEquations G₀) o).mp hcomponent
    subst o
    have hQdata := hrootData' Q hQmin
    have hdegreePos : 0 < degree Q := hQdata.2.2.2.2.1
    by_cases hline : degree Q = 1
    · simp [lineCell, error, persistentRootDegreeSplitError,
        rootOptionDegree, hline]
    · have hnonlinear : 2 ≤ degree Q := by omega
      by_cases hbounded : degree Q ≤ cutoff
      · have hcellNonempty : (cell (some Q)).Nonempty :=
          (mem_activeQbarPersistentRootComponentOptions_iff
            sourceEquations G₀ cell (some Q)).mp ho |>.2
        let representative : IntVector 3 := Classical.choose hcellNonempty
        have hrepresentative : representative ∈ cell (some Q) :=
          Classical.choose_spec hcellNonempty
        have hbase : affineMap representative ∈ affineCell (some Q) :=
          Finset.mem_image.mpr ⟨representative, hrepresentative, rfl⟩
        have hzero : ∀ x ∈ affineCell (some Q),
            (fun i ↦ ((integralAffineChartVector x i : ℤ) : Qbar)) ∈
              affineIdealZeroLocus Q := by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          rw [hchartEq]
          have hselected := hrootSelected (some Q) ho z hz
          exact (selectedFiniteEquationComponent_spec
            (qbarSurfaceCutEquationFamily sourceEquations G₀)
            (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
            hselected).2
        have hcong : ∀ x ∈ affineCell (some Q),
            IntVectorCongruent m x (affineMap representative) := by
          intro x hx i
          obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hx
          exact (integralAffineMap_congruent u z i).trans
            (integralAffineMap_congruent u representative i).symm
        have haffineBox : ∀ x ∈ affineCell (some Q), ∀ i,
            |(x i : ℝ) - center i| ≤ R := by
          intro x hx i
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          exact hbox (some Q) ho z hz i
        have hraw := hLow hm (affineMap representative) Q (degree Q)
          hQdata.1 hQdata.2.1 hQdata.2.2.2 hnonlinear hbounded
          (affineCell (some Q)) hbase hzero hcong center R hR haffineBox
        have hcardEq : (affineCell (some Q)).card = (cell (some Q)).card :=
          Finset.card_image_iff.mpr haffineInjective.injOn
        rw [hcardEq] at hraw
        simpa [lineCell, error, persistentRootDegreeSplitError,
          rootOptionDegree, hline, hbounded, lowError, side] using hraw
      · have hhighDegree : cutoff < degree Q := by omega
        rcases conjugateIdeal_fixed_or_exists_distinct Q with
          hstable | ⟨g, hg⟩
        · have hraw := hHigh Q ho hhighDegree hstable
          simpa [lineCell, error, persistentRootDegreeSplitError,
            persistentRootHighDegreeError, rootOptionDegree, hline,
            hbounded, IsQbarIdealGaloisStable, hstable] using hraw
        · have hconjPrime : (conjugateIdeal g Q).IsPrime :=
            conjugateIdeal_isPrime g Q hQdata.1
          have hconjHom : (conjugateIdeal g Q).IsHomogeneous
              (homogeneousSubmodule (Fin 4) Qbar) :=
            conjugateIdeal_isHomogeneous g Q hQdata.2.1
          have hconjDegree : HasProjectiveDimensionDegree
              (conjugateIdeal g Q) 1 (degree Q) :=
            hConjugate 3 1 (degree Q) g Q hQdata.2.2.2
          have hintersection : ∀ z ∈ cell (some Q),
              (fun i ↦
                (progressionHomogeneousPoint u m z i : Qbar)) ∈
                affineIdealZeroLocus (Q ⊔ conjugateIdeal g Q) := by
            intro z hz
            rw [mem_affineIdealZeroLocus_iff_le_ker_aeval]
            have hselected := hrootSelected (some Q) ho z hz
            have hQpoint :
                (fun i ↦
                  (progressionHomogeneousPoint u m z i : Qbar)) ∈
                  affineIdealZeroLocus Q :=
              (selectedFiniteEquationComponent_spec
                (qbarSurfaceCutEquationFamily sourceEquations G₀)
                (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar))
                hselected).2
            have hQzero :=
              (mem_affineIdealZeroLocus_iff_le_ker_aeval Q _).mp hQpoint
            apply sup_le
            · exact hQzero
            · have hconjugate := conjugateIdeal_le_rationalEvaluationKernel
                g Q
                (fun i ↦
                  (progressionHomogeneousPoint u m z i : ℚ)) hQzero
              simpa using hconjugate
          have hcard :=
            card_geometricProgression_on_distinct_curves_le_degree_mul
              (K := Qbar) (N := 3) (d := degree Q) (e := degree Q)
              (m := m) hm Q (conjugateIdeal g Q) hQdata.1 hconjPrime
              hQdata.2.1 hconjHom hQdata.2.2.2 hconjDegree hg.symm u
              (cell (some Q)) hintersection
          have hdegree : ((cell (some Q)).card : ℝ) ≤
              (degree Q : ℝ) ^ 2 := by
            calc
              ((cell (some Q)).card : ℝ) ≤
                  (((degree Q) * (degree Q) : ℕ) : ℝ) := by
                    exact_mod_cast hcard
              _ = (degree Q : ℝ) ^ 2 := by norm_num [pow_two]
          have hnotStable : ¬ IsQbarIdealGaloisStable Q := by
            intro hs
            exact hg (hs g)
          simpa [lineCell, error, persistentRootDegreeSplitError,
            persistentRootHighDegreeError, rootOptionDegree, hline,
            hbounded, hnotStable] using hdegree
  have htotal := card_le_globalDistinguished_add_sum_errors
    (active.biUnion cell) active cell lineCell error (by
      intro z hz
      exact hz)
      hlineSubset hlocal
  simpa [active, persistentRootLinePointUnion, lineCell, error, lowError,
    volume, side]
    using htotal

/-- Uniform-high-degree form of `exists_uniform_persistentRoot_degreeSplit`.

The Salberger constant is quantified before the surface, auxiliary, height,
and active geometric degrees.  Thus this is composable with the genuinely
uniform conclusion of Salberger 2023, Theorem 3.16 / (3.20), whereas an
arbitrary family of constants indexed by a degree which may grow with the
height is not.  The Salberger parameter is the product of the four
projective coordinate bounds; on the chart `[1,z₁,z₂,z₃]` it is represented
here by the cube of the affine side parameter. -/
theorem exists_uniform_persistentRoot_degreeSplit_uniformHigh
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (highConstant : ℝ),
      ∀ {d e₀ : ℕ}
        (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ)),
        (finiteEquationIdeal sourceEquations).IsPrime →
        ((finiteEquationIdeal sourceEquations).map
          (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime →
        (finiteEquationIdeal sourceEquations).IsHomogeneous
          (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree
          (finiteEquationIdeal sourceEquations) 2 d →
      ∀ (G₀ : MvPolynomial (Fin 4) ℚ),
        G₀.IsHomogeneous e₀ →
        G₀ ∉ finiteEquationIdeal sourceEquations →
      ∀ (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3))
        (u : IntVector 3) (m : ℕ), 0 < m →
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i ↦ (progressionHomogeneousPoint u m z i : Qbar)) = o) →
      ∀ (center : RealVector 3) (R : ℝ), 0 ≤ R →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
        |(integralAffineMap u z m i : ℝ) - center i| ≤ R) →
      ∃ degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ,
        (∀ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀),
          Q.IsPrime ∧
          Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
          finiteEquationIdeal (qbarSurfaceEquationFamily sourceEquations) ≤ Q ∧
          HasProjectiveDimensionDegree Q 1 (degree Q)) ∧
        (∑ Q ∈ finiteEquationMinimalPrimes
            (qbarSurfaceCutEquationFamily sourceEquations G₀), degree Q) ≤
          d * e₀ ∧
        active.card ≤ d * e₀ ∧
        (Salberger2023Theorem316PersistentRootCallback sourceEquations G₀
          cell degree cutoff highConstant ε
            ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) →
        (((active.biUnion cell).card : ℕ) : ℝ) ≤
          ((persistentRootLinePointUnion degree active cell).card : ℝ) +
            ∑ o ∈ active,
              persistentRootUniformDegreeSplitError degree cutoff
                ((cutoff : ℝ) ^ 2 +
                  C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
                highConstant ε ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o) := by
  classical
  obtain ⟨C, hC, hpointwise⟩ :=
    exists_uniform_persistentRoot_degreeSplit
      hConjugate cutoff ε hε
  refine ⟨C, hC, ?_⟩
  intro highConstant d e₀ sourceEquations hprime hgeometricPrime hhom hdegree
    G₀ hG₀hom hG₀not cell u m hm
  dsimp only
  intro hrootSelected center R hR hbox
  obtain ⟨degree, hrootData, hrootMass, hactiveCard, hbound⟩ :=
    hpointwise sourceEquations hprime hgeometricPrime hhom hdegree
      G₀ hG₀hom hG₀not cell u m hm hrootSelected center R hR hbox
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  let side : ℝ := 2 * R / (m : ℝ) + 2
  let volume : ℝ := side ^ (3 : ℕ)
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hside : 1 < side := by
    dsimp only [side]
    have hdiv : 0 ≤ 2 * R / (m : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) hR) hmReal.le
    linarith
  have hvolume : 1 < volume := by
    have hfactor : 0 < (side - 1) * (side ^ 2 + side + 1) := by
      apply mul_pos (sub_pos.mpr hside)
      nlinarith [sq_nonneg side]
    dsimp only [volume]
    nlinarith
  let pointConstant : ℕ → ℝ :=
    lemma313ConstantForTheorem316 highConstant ε volume
  refine ⟨degree, hrootData, hrootMass, hactiveCard, ?_⟩
  intro hUniform
  have hPointwise : Salberger2023Lemma313PersistentRootCallback
      sourceEquations G₀ cell degree cutoff pointConstant volume := by
    intro Q hQ hQdegree hstable
    have hraw := hUniform Q hQ hQdegree hstable
    simpa [pointConstant,
      salberger2023Lemma313CurveError_lemma313ConstantForTheorem316
        highConstant ε volume (degree Q) hvolume] using hraw
  have hraw := hbound pointConstant hPointwise
  have herr (o : Option (Ideal (MvPolynomial (Fin 4) Qbar))) :
      persistentRootDegreeSplitError degree cutoff
          ((cutoff : ℝ) ^ 2 +
            C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
          pointConstant ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o =
        persistentRootUniformDegreeSplitError degree cutoff
          ((cutoff : ℝ) ^ 2 +
            C * (2 * R / (m : ℝ) + 2) ^ ((1 / 2 : ℝ) + ε))
          highConstant ε ((2 * R / (m : ℝ) + 2) ^ (3 : ℕ)) o := by
    apply persistentRootDegreeSplitError_lemma313ConstantForTheorem316
    simpa [side, volume] using hvolume
  simpa only [herr] using hraw

end CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplitInternal
