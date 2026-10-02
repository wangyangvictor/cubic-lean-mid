import TranslatedDepthSeven.RankSevenDegreeOneHighLedger
import TranslatedDepthSeven.RankSevenEdgeFrontierGeometry
import TranslatedDepthSeven.ProjectiveStarLocus

/-!
# Literal incidence of the rank-seven degree-one components

This file closes the geometric incidence seam left by the tagged line
ledger.  Its only new standard-algebraic-geometry input is the classical
classification of a prime affine curve of degree one as an affine line.
That input contains no counting assertion.

For every actual node, edge, or persistent degree-one component we retain
the complete affine line, not merely the finite set of points selected from
it.  The component ideal contains the corresponding source-section ideal;
undoing the homogeneous affine change therefore shows that the complete
line maps into the original fixed cone.  Taking the highest line
coefficient then puts its primitive direction on the same fixed cone.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000

namespace StandardAG

/-- A prime affine curve of Hilbert dimension one and degree one is an
affine line.  If it contains two integral points, the line has an integral
base point and a primitive integral direction, and every displayed integral
point has a unique integral line parameter.

This is the ordinary degree-one classification plus the elementary lattice
primitivity statement.  It is deliberately formulated for one ideal and
one finite set and contains no bound for points, components, lines, or
coefficients. -/
def DegreeOneAffinePrimeCurveIsIntegralLine : Prop :=
  ∀ (N : ℕ) (Q : Ideal (MvPolynomial (Fin N) ℝ)),
    HasAffineHilbertDimensionDegree Q 1 1 →
    ∀ (S : Finset (IntVector N)), 2 ≤ S.card →
      (∀ z ∈ S,
        (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus Q) →
      ∃ (y₀ h : IntVector N) (parameter : IntVector N → ℤ),
        PrimitiveDirection h ∧
          Set.InjOn parameter (↑S : Set (IntVector N)) ∧
          (∀ z ∈ S, z = fun i ↦ y₀ i + parameter z * h i) ∧
          affineIdealZeroLocus Q =
            Set.range (fun t : ℝ ↦
              fun i ↦ (y₀ i : ℝ) + t * (h i : ℝ))

/-- Forgetting the full-line equality gives the previously isolated narrow
primitive-parametrization input. -/
theorem DegreeOneAffinePrimeCurveIsIntegralLine.toPrimitiveParametrization
    (hline : DegreeOneAffinePrimeCurveIsIntegralLine) :
    DegreeOneAffineCurvePrimitiveParametrization := by
  intro N Q hQ S hScard hS
  obtain ⟨y₀, h, parameter, hp, hinj, hparam, _hwhole⟩ :=
    hline N Q hQ S hScard hS
  exact ⟨y₀, h, parameter, hp, hinj, hparam⟩

end StandardAG

/-! ## Simultaneous full-line data for an actual tagged family -/

/-- The degree-one classification supplies simultaneous primitive integral
coordinates together with the *entire* real affine line for every active
tagged component.  The proof makes the choices independently over the
literal finite tagged type; it does not identify equal geometric lines
arising from different records. -/
theorem exists_activeTaggedLinearComponent_fullIntegralLines
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    { ι : Type*} [Fintype ι] {N : ℕ}
    (J : ι → Ideal (MvPolynomial (Fin N) ℝ))
    (X : ι → Finset (IntVector N)) :
    ∃ (base direction : TaggedLinearComponent J → IntVector N)
      (parameter : TaggedLinearComponent J → IntVector N → ℤ),
      ∀ o ∈ activeTaggedLinearComponents J X,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J X o).image
            (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J X o).image
            (fun x ↦ x.2.1),
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ ↦
            fun i ↦ (base o i : ℝ) + t * (direction o i : ℝ)) := by
  classical
  have hdata : ∀ o : TaggedLinearComponent J,
      ∃ (y₀ h : IntVector N) (a : IntVector N → ℤ),
        o ∈ activeTaggedLinearComponents J X →
          PrimitiveDirection h ∧
          Set.InjOn a
            (↑((assignedLinearComponentFibre J X o).image
              (fun x ↦ x.2.1)) : Set (IntVector N)) ∧
          (∀ z ∈ (assignedLinearComponentFibre J X o).image
              (fun x ↦ x.2.1),
            z = fun i ↦ y₀ i + a z * h i) ∧
          affineIdealZeroLocus o.2.1 =
            Set.range (fun t : ℝ ↦
              fun i ↦ (y₀ i : ℝ) + t * (h i : ℝ)) := by
    intro o
    by_cases ho : o ∈ activeTaggedLinearComponents J X
    · let S := (assignedLinearComponentFibre J X o).image
          (fun x ↦ x.2.1)
      have hinjective : Set.InjOn
          (fun x : TaggedLinearContributionPoint J X ↦ x.2.1)
          (↑(assignedLinearComponentFibre J X o) :
            Set (TaggedLinearContributionPoint J X)) := by
        intro x hx y hy hxy
        have hxo := (Finset.mem_filter.mp hx).2
        have hyo := (Finset.mem_filter.mp hy).2
        have hi : x.1 = y.1 := congrArg
          (fun z : TaggedLinearComponent J ↦ z.1) (hxo.trans hyo.symm)
        cases x with
        | mk xi xz =>
          cases y with
          | mk yi yz =>
            dsimp only at hi hxy ⊢
            subst yi
            exact Sigma.ext rfl (heq_of_eq (Subtype.ext hxy))
      have hScard : 2 ≤ S.card := by
        rw [Finset.card_image_iff.mpr hinjective]
        exact (Finset.mem_filter.mp ho).2
      have hSzero : ∀ z ∈ S,
          (fun i ↦ (z i : ℝ)) ∈ affineIdealZeroLocus o.2.1 := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact (mem_finitePointsOnAffineIdeal_iff (X o.1) o.2.1 x.2.1).1
          (mem_assignedLinearComponentFibre_ideal J X o x hx).2 |>.2
      have hdegree : HasAffineHilbertDimensionDegree o.2.1 1 1 :=
        ((mem_linearAffineComponents_iff (J o.1) o.2.1).1 o.2.2).2
      obtain ⟨y₀, h, a, hp, ha, hparam, hwhole⟩ :=
        hline N o.2.1 hdegree S hScard hSzero
      exact ⟨y₀, h, a, fun _ ↦ ⟨hp, ha, hparam, hwhole⟩⟩
    · exact ⟨0, 0, 0, fun h ↦ (ho h).elim⟩
  choose base direction parameter hspec using hdata
  exact ⟨base, direction, parameter, hspec⟩

/-! ## Rational projective ideals and their real affine charts -/

/-- The rational projective ideal underlying one actual degree-one index. -/
def rankSevenDegreeOneProjectiveIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ) :
    RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k markCount
      hP hlower X localEquations selectedVar menu markOf →
      Ideal (MvPolynomial (Fin 14) ℚ)
  | Sum.inl (Sum.inl node) => node.2.1.component
  | Sum.inl (Sum.inr edge) => edge.2.2.1
  | Sum.inr persistent => I ⊔ Ideal.span {auxiliaryForm persistent.1}

/-- The affine ideal used in the line ledger is literally the real standard
chart of the preceding projective ideal. -/
theorem rankSevenDegreeOneIdeal_eq_realProjectiveAffineChartIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf) :
    rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k markCount
        hP hlower I X localEquations selectedVar menu markOf auxiliaryForm i =
      realProjectiveAffineChartIdeal
        (rankSevenDegreeOneProjectiveIdeal p x₀ equations CF Cchart model
          P k markCount hP hlower I X localEquations selectedVar menu markOf
            auxiliaryForm i) := by
  rcases i with (node | edge) | persistent
  · rfl
  · rfl
  · rfl

/-- One literal source-section ideal below the projective ideal attached to
an occurrence.  At an edge we use the left endpoint; either endpoint would
give the same conclusion below. -/
def rankSevenDegreeOneSourceIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount) :
    RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k markCount
      hP hlower X localEquations selectedVar menu markOf →
      Ideal (MvPolynomial (Fin 14) ℚ)
  | Sum.inl (Sum.inl node) =>
      rankSevenNodeEquationIdeal p x₀ equations CF Cchart node.1.1
        node.2.1.residue
  | Sum.inl (Sum.inr edge) =>
      rankSevenNodeEquationIdeal p x₀ equations CF Cchart
        edge.1.1.1.1
        (reduceResidueVector
          (Nat.dvd_lcm_left edge.1.1.1.1 edge.1.1.2.1)
          edge.2.1.1.residue)
  | Sum.inr persistent =>
      rankSevenNodeEquationIdeal p x₀ equations CF Cchart
        persistent.1.modulus.1 persistent.1.residue

/-- The selected source-section equations are contained in the projective
ideal which produced the actual affine degree-one component.  This is a
case-by-case statement about the literal record fields: a node component is
a minimal prime of its node ideal; an edge frontier contains its left node
component; and a persistent record stores the fixed surface `I`. -/
theorem rankSevenDegreeOneSourceIdeal_le_projectiveIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF Cchart model.denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf) :
    rankSevenDegreeOneSourceIdeal p x₀ equations CF Cchart model P k
        markCount hP hlower X localEquations selectedVar menu markOf i ≤
      rankSevenDegreeOneProjectiveIdeal p x₀ equations CF Cchart model
        P k markCount hP hlower I X localEquations selectedVar menu markOf
          auxiliaryForm i := by
  rcases i with (node | edge) | persistent
  · have hoccupied :=
      (mem_occupiedRankSevenSurvivingNonSurfaceNodeRecords_iff
        p x₀ equations CF Cchart model.denominator P k hP hlower
          node.1 node.2.1).1 node.2.2 |>.1
    have hnonSurface :=
      (mem_occupiedRankSevenNonSurfaceNodeRecords_iff
        p x₀ equations CF Cchart node.1 node.2.1).1 hoccupied |>.2
    have hcomponent :=
      (mem_rankSevenNonSurfaceNodeComponents_iff
        p x₀ equations CF Cchart node.1.1 node.2.1.residue
          node.2.1.component).1 hnonSurface |>.1
    exact le_of_mem_finiteMinimalPrimes hcomponent
  · have hoccupied : edge.2.1.1 ∈ occupiedRankSevenSurfaceEdgeRecords
        p x₀ equations CF Cchart P k edge.1.1.1 edge.1.1.2 hP :=
      (Finset.mem_filter.mp edge.2.1.2).1
    have hcoarse :=
      (mem_occupiedRankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart P k edge.1.1.1 edge.1.1.2 hP
          edge.2.1.1).1 hoccupied |>.1
    have hleftSurface :=
      (mem_rankSevenSurfaceEdgeRecords_iff
        p x₀ equations CF Cchart edge.1.1.1 edge.1.1.2 hP
          edge.2.1.1).1 hcoarse |>.1
    have hleftNode :=
      (mem_rankSevenSurfaceNodeComponents_iff
        p x₀ equations CF Cchart edge.1.1.1.1
          (reduceResidueVector
            (Nat.dvd_lcm_left edge.1.1.1.1 edge.1.1.2.1)
            edge.2.1.1.residue) edge.2.1.1.leftComponent).1
        hleftSurface |>.1
    exact (le_of_mem_finiteMinimalPrimes hleftNode).trans
      (le_sup_left.trans (le_of_mem_finiteMinimalPrimes edge.2.2.2))
  · have hcoarse :=
      (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
        p x₀ equations CF Cchart model.denominator P k markCount hP hlower
          X localEquations selectedVar menu markOf persistent.1).1
        persistent.2 |>.1
    have hsurface :=
      (mem_occupiedRankSevenPersistentRecords_iff
        p x₀ equations CF Cchart P k markCount persistent.1).1
        hcoarse |>.2
    have hnode :=
      (mem_rankSevenSurfaceNodeComponents_iff
        p x₀ equations CF Cchart persistent.1.modulus.1
          persistent.1.residue persistent.1.component).1 hsurface |>.1
    have hcomponent : persistent.1.component = I :=
      persistentMultiplicityOneRecord_component_eq_fixedSurface
        p x₀ equations CF Cchart model.denominator P k markCount hP hlower
          I X hX localEquations selectedVar menu markOf persistent.1
            persistent.2
    exact (le_of_mem_finiteMinimalPrimes hnode).trans
      (by simpa only [hcomponent] using
        (le_sup_left : I ≤ I ⊔ Ideal.span {auxiliaryForm persistent.1}))

/-- A rational homogeneous point belongs to a rational projective ideal if
its standard affine coordinates belong to the real affine chart.  This is
the converse of `intPoint_mem_realProjectiveAffineChartIdeal`, restricted to
integral coordinates where descent from `ℝ` to `ℚ` is injective. -/
theorem intPoint_mem_projectiveIdeal_of_mem_realProjectiveAffineChartIdeal
    {N : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (z : IntVector N)
    (hz : (fun i ↦ (z i : ℝ)) ∈
      affineIdealZeroLocus (realProjectiveAffineChartIdeal I)) :
    (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I := by
  intro f hf
  have hmember : standardDehomogenizationHom ℝ N
      (MvPolynomial.map (algebraMap ℚ ℝ) f) ∈
        realProjectiveAffineChartIdeal I := by
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hf)
  have hzero := hz _ hmember
  rw [eval_standardDehomogenizationHom] at hzero
  let zQ : Fin (N + 1) → ℚ :=
    fun i ↦ (integralAffineChartVector z i : ℚ)
  have hcoords :
      (Fin.cases (1 : ℝ) (fun i ↦ (z i : ℝ))) =
        fun i ↦ algebraMap ℚ ℝ (zQ i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      simp [zQ, integralAffineChartVector]
  rw [hcoords, ← MvPolynomial.eval₂_eq_eval_map] at hzero
  have hzero' : algebraMap ℚ ℝ (MvPolynomial.eval zQ f) = 0 := by
    have heval :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (fun i ↦ algebraMap ℚ ℝ (zQ i)) f =
          algebraMap ℚ ℝ (MvPolynomial.eval zQ f) := by
      simpa [MvPolynomial.eval₂_id] using
        (MvPolynomial.eval₂_comp_left (algebraMap ℚ ℝ)
          (RingHom.id ℚ) zQ f).symm
    rw [← heval]
    exact hzero
  exact (map_eq_zero_iff (algebraMap ℚ ℝ)
    (FaithfulSMul.algebraMap_injective ℚ ℝ)).mp hzero'

/-! ## Descent from a source section to the fixed cone -/

/-- The translated-cone part of a literal rank-seven node ideal remembers
the original equations in both directions.  Thus an integral standard-chart
point of the node ideal maps, under `z ↦ x₀ + m z`, to a common integral
zero of the original fixed equation family. -/
theorem integralCommonZero_of_intPoint_mem_rankSevenNodeEquationIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (C : IntegralDepthSevenJacobianChartIndex equations)
    (q : ℕ) (rho : Fin 13 → ZMod q)
    (z : IntVector 13)
    (hz : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus
        (rankSevenNodeEquationIdeal p x₀ equations CF C q rho)) :
    IntegralCommonZero equations (integralAffineMap x₀ z p.m) := by
  classical
  let zQ : Fin 13 → ℚ := fun i ↦ (z i : ℚ)
  let yQ : Fin 13 → ℚ := fun i ↦ (x₀ i : ℚ)
  have hmQ : (p.m : ℚ) ≠ 0 := by exact_mod_cast p.hm.ne'
  let degree : MvPolynomial (Fin 13) ℤ → ℕ := fun f ↦
    if hf : f ∈ equations then Classical.choose (hhomogeneous f hf) else 0
  have hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f) := by
    intro f hf
    simp only [degree, dif_pos hf]
    exact Classical.choose_spec (hhomogeneous f hf)
  have hlift : ∀ f ∈ projectiveConeLiftEquationFamily equations,
      ∃ e : ℕ, f.IsHomogeneous e := by
    intro f hf
    obtain ⟨f₀, _hf₀, _heq, he⟩ :=
      projectiveConeLiftEquationFamily_each_isHomogeneous
        equations degree hdegree hf
    exact ⟨degree f₀, he⟩
  have hsource : ∀ g ∈
      rankSevenSourceSectionEquationFinset x₀ p.m p.hm equations
        ((selectedRankSevenPacketSectionMatrix
          p x₀ equations CF C q rho).map ((↑) : ℤ → ℚ)),
      MvPolynomial.eval
        (fun i ↦ (integralAffineChartVector z i : ℚ)) g = 0 := by
    simpa [rankSevenNodeEquationIdeal,
      rankSevenSourceSectionEquationsAtResidue,
      affineIdealZeroLocus_finiteEquationIdeal] using hz
  have htranslated : affineChartPoint zQ ∈
      finiteProjectiveCommonZeroLocus
        (translatedProjectiveConeLiftEquationFamily yQ (p.m : ℚ) hmQ
          equations) := by
    intro g hg
    obtain ⟨e, he⟩ :=
      finiteFamilyHomogeneousAffineChange_each_isHomogeneous
        yQ (p.m : ℚ) hmQ (projectiveConeLiftEquationFamily equations)
          hlift hg
    unfold affineChartPoint
    rw [mk_mem_homogeneousProjectiveHypersurface_iff g e he
      (affineChartVector zQ) (affineChartVector_ne_zero zQ)]
    have hrenamed : MvPolynomial.rename (finSuccEquiv 13).symm g ∈
        rankSevenSourceSectionEquationFinset x₀ p.m p.hm equations
          ((selectedRankSevenPacketSectionMatrix
            p x₀ equations CF C q rho).map ((↑) : ℤ → ℚ)) := by
      rw [rankSevenSourceSectionEquationFinset]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    have hzero := hsource _ hrenamed
    rw [MvPolynomial.eval_rename] at hzero
    have hcoord :
        ((fun i ↦ (integralAffineChartVector z i : ℚ)) ∘
          (finSuccEquiv 13).symm) = affineChartVector zQ := by
      funext j
      cases j <;> simp [integralAffineChartVector, affineChartVector, zQ]
    simpa [hcoord, MvPolynomial.aeval_def, MvPolynomial.eval₂_id] using hzero
  have horiginalProjective :
      projectiveAffineMap yQ (p.m : ℚ) hmQ (affineChartPoint zQ) ∈
        finiteProjectiveCommonZeroLocus
          (projectiveConeLiftEquationFamily equations) :=
    (projectiveAffineMap_mem_finiteProjectiveCommonZeroLocus_iff
      yQ (p.m : ℚ) hmQ (projectiveConeLiftEquationFamily equations)
        hlift (affineChartPoint zQ)).mpr htranslated
  rw [projectiveAffineMap_affineChartPoint,
    finiteProjectiveCommonZeroLocus_projectiveConeLiftEquationFamily
      equations degree hdegree] at horiginalProjective
  have hcone :
      (fun i : Fin 13 ↦
        affineChartVector (fun i ↦ yQ i + (p.m : ℚ) * zQ i) (some i)) ∈
        integralAffineConeZeroSetOver ℚ equations := by
    exact (mk_mem_projectiveConeOverIntegralEquations_iff
      equations degree hdegree _ (affineChartVector_ne_zero _)).mp
        horiginalProjective
  intro f hf
  have hzero := hcone f hf
  have hpoint : (fun i : Fin 13 ↦
      affineChartVector (fun i ↦ yQ i + (p.m : ℚ) * zQ i) (some i)) =
      fun i ↦ (integralAffineMap x₀ z p.m i : ℚ) := by
    funext i
    simp [affineChartVector, yQ, zQ, integralAffineMap]
  change MvPolynomial.eval
    (fun i : Fin 13 ↦
      affineChartVector (fun i ↦ yQ i + (p.m : ℚ) * zQ i) (some i))
      (MvPolynomial.map (Int.castRingHom ℚ) f) = 0 at hzero
  rw [hpoint, eval_map_intCast] at hzero
  exact_mod_cast hzero

/-- Case-free wrapper for the source ideal stored by an actual node, edge,
or persistent degree-one occurrence. -/
theorem integralCommonZero_of_intPoint_mem_rankSevenDegreeOneSourceIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (X : Finset (IntVector 13))
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf)
    (z : IntVector 13)
    (hz : (fun j ↦ (integralAffineChartVector z j : ℚ)) ∈
      affineIdealZeroLocus
        (rankSevenDegreeOneSourceIdeal p x₀ equations CF Cchart model P k
          markCount hP hlower X localEquations selectedVar menu markOf i)) :
    IntegralCommonZero equations (integralAffineMap x₀ z p.m) := by
  rcases i with (node | edge) | persistent
  · exact integralCommonZero_of_intPoint_mem_rankSevenNodeEquationIdeal
      p x₀ equations CF hhomogeneous Cchart node.1.1
        node.2.1.residue z hz
  · exact integralCommonZero_of_intPoint_mem_rankSevenNodeEquationIdeal
      p x₀ equations CF hhomogeneous Cchart edge.1.1.1.1
        (reduceResidueVector
          (Nat.dvd_lcm_left edge.1.1.1.1 edge.1.1.2.1)
          edge.2.1.1.residue) z hz
  · exact integralCommonZero_of_intPoint_mem_rankSevenNodeEquationIdeal
      p x₀ equations CF hhomogeneous Cchart persistent.1.modulus.1
        persistent.1.residue z hz

/-! ## The complete selected lines in the source sections -/

/-- If an actual affine degree-one component is the displayed complete
integral line, every integral point of that line belongs to the literal
source-section ideal below its node, edge, or persistent projective ideal. -/
theorem rankSevenDegreeOne_fullLine_mem_sourceIdeal
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF Cchart model.denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ)
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf)
    (Q : Ideal (MvPolynomial (Fin 13) ℝ))
    (hQ : Q ∈ linearAffineComponents
      (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
        markCount hP hlower I X localEquations selectedVar menu markOf
          auxiliaryForm i))
    (base direction : IntVector 13)
    (hwhole : affineIdealZeroLocus Q =
      Set.range (fun t : ℝ ↦
        fun j ↦ (base j : ℝ) + t * (direction j : ℝ)))
    (t : ℤ) :
    (fun j ↦ (integralAffineChartVector
      (fun u ↦ base u + t * direction u) j : ℚ)) ∈
      affineIdealZeroLocus
        (rankSevenDegreeOneSourceIdeal p x₀ equations CF Cchart model P k
          markCount hP hlower X localEquations selectedVar menu markOf i) := by
  let z : IntVector 13 := fun u ↦ base u + t * direction u
  have hQzero : (fun j ↦ (z j : ℝ)) ∈ affineIdealZeroLocus Q := by
    rw [hwhole]
    refine ⟨(t : ℝ), ?_⟩
    funext j
    simp [z]
  have hminimal :=
    ((mem_linearAffineComponents_iff
      (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
        markCount hP hlower I X localEquations selectedVar menu markOf
          auxiliaryForm i) Q).1 hQ).1
  have hJzero : (fun j ↦ (z j : ℝ)) ∈
      affineIdealZeroLocus
        (rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
          markCount hP hlower I X localEquations selectedVar menu markOf
            auxiliaryForm i) := by
    intro f hf
    exact hQzero f (le_of_mem_finiteMinimalPrimes hminimal hf)
  have hKzero :
      (fun j ↦ (integralAffineChartVector z j : ℚ)) ∈
        affineIdealZeroLocus
          (rankSevenDegreeOneProjectiveIdeal p x₀ equations CF Cchart
            model P k markCount hP hlower I X localEquations selectedVar
              menu markOf auxiliaryForm i) := by
    apply intPoint_mem_projectiveIdeal_of_mem_realProjectiveAffineChartIdeal
    rw [← rankSevenDegreeOneIdeal_eq_realProjectiveAffineChartIdeal
      p x₀ equations CF Cchart model P k markCount hP hlower I X
        localEquations selectedVar menu markOf auxiliaryForm i]
    exact hJzero
  intro f hf
  exact hKzero f
    (rankSevenDegreeOneSourceIdeal_le_projectiveIdeal
      p x₀ equations CF Cchart model P k markCount hP hlower I X hX
        localEquations selectedVar menu markOf auxiliaryForm i hf)

/-- Every active literal node, edge, or persistent degree-one component is
the complete affine line with the selected primitive integral direction.
Every integral point of that line maps into the original fixed cone, and
the primitive direction itself lies on that cone.  The last assertion uses
only homogeneity and cancellation of the nonzero fixed scale `p.m`. -/
theorem exists_rankSevenDegreeOne_fullLines_in_originalCone
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e)
    (Cchart : IntegralDepthSevenJacobianChartIndex equations)
    (model : FixedFivefoldResidueModel
      (indexedFinsetFamily (rationalizedEquationFinset equations)))
    (P : Finset ℕ) (k markCount : ℕ) (hP : ∀ s ∈ P, s.Prime)
    (hlower : ∀ q : ReservoirModulus P k,
      manuscriptReservoirTarget normalizedSurfaceReservoirConstant
        p.T (5 / 7) ≤ q.1)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (X : Finset (IntVector 13))
    (hX : X ⊆ rankSevenPersistentSurfaceCell
      p x₀ equations CF Cchart model.denominator P k hP hlower I)
    (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
    (selectedVar : Fin 11 → Fin 13)
    (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
    (markOf : IntVector 13 → Fin markCount)
    (auxiliaryForm : RankSevenPersistentRecord P k markCount →
      MvPolynomial (Fin 14) ℚ) :
    let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
      markCount hP hlower I X localEquations selectedVar menu markOf
        auxiliaryForm
    let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
      markCount hP hlower I X localEquations selectedVar menu markOf
    ∃ (base direction : TaggedLinearComponent J → IntVector 13)
      (parameter : TaggedLinearComponent J → IntVector 13 → ℤ),
      ∀ o ∈ activeTaggedLinearComponents J Y,
        PrimitiveDirection (direction o) ∧
        Set.InjOn (parameter o)
          (↑((assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
        (∀ z ∈ (assignedLinearComponentFibre J Y o).image
            (fun x ↦ x.2.1),
          z = fun i ↦ base o i + parameter o z * direction o i) ∧
        affineIdealZeroLocus o.2.1 =
          Set.range (fun t : ℝ ↦
            fun i ↦ (base o i : ℝ) + t * (direction o i : ℝ)) ∧
        (∀ t : ℤ, IntegralCommonZero equations
          (integralAffineMap x₀
            (fun i ↦ base o i + t * direction o i) p.m)) ∧
        IntegralCommonZero equations (direction o) := by
  classical
  dsimp only
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
  obtain ⟨base, direction, parameter, hdata⟩ :=
    exists_activeTaggedLinearComponent_fullIntegralLines hline J Y
  refine ⟨base, direction, parameter, ?_⟩
  intro o ho
  have hoData := hdata o ho
  have hfull : ∀ t : ℤ, IntegralCommonZero equations
      (integralAffineMap x₀
        (fun i ↦ base o i + t * direction o i) p.m) := by
    intro t
    have hsource := rankSevenDegreeOne_fullLine_mem_sourceIdeal
      p x₀ equations CF Cchart model P k markCount hP hlower I X hX
        localEquations selectedVar menu markOf auxiliaryForm o.1 o.2.1 o.2.2
          (base o) (direction o) hoData.2.2.2 t
    exact integralCommonZero_of_intPoint_mem_rankSevenDegreeOneSourceIdeal
      p x₀ equations CF hhomogeneous Cchart model P k markCount hP hlower X
        localEquations selectedVar menu markOf o.1
          (fun i ↦ base o i + t * direction o i) hsource
  let degree : MvPolynomial (Fin 13) ℤ → ℕ := fun f ↦
    if hf : f ∈ equations then Classical.choose (hhomogeneous f hf) else 0
  have hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f) := by
    intro f hf
    simp only [degree, dif_pos hf]
    exact Classical.choose_spec (hhomogeneous f hf)
  let originalBase : IntVector 13 := integralAffineMap x₀ (base o) p.m
  let scaledDirection : IntVector 13 :=
    fun i ↦ (p.m : ℤ) * direction o i
  have hscaledLine : ∀ f ∈ equations, ∀ t : ℤ,
      MvPolynomial.eval
        (fun i ↦ originalBase i + t * scaledDirection i) f = 0 := by
    intro f hf t
    have ht := hfull t f hf
    rw [show (fun i ↦ originalBase i + t * scaledDirection i) =
        integralAffineMap x₀ (fun i ↦ base o i + t * direction o i) p.m by
      funext i
      simp [originalBase, scaledDirection, integralAffineMap]
      ring]
    exact ht
  have hscaledDirection : scaledDirection ∈
      integralAffineConeZeroSet equations :=
    mem_integralAffineConeZeroSet_of_eval_line_zero
      equations degree hdegree originalBase scaledDirection hscaledLine
  have hdirection : IntegralCommonZero equations (direction o) := by
    intro f hf
    have hz := hscaledDirection f hf
    have hscale := eval_smul_of_isHomogeneous f (direction o)
      (p.m : ℤ) (degree f) (hdegree f hf)
    have hscaled :
        MvPolynomial.eval scaledDirection f =
          (p.m : ℤ) ^ degree f * MvPolynomial.eval (direction o) f := by
      simpa [scaledDirection] using hscale
    rw [hscaled] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (pow_ne_zero _ (by exact_mod_cast p.hm.ne'))
  exact ⟨hoData.1, hoData.2.1, hoData.2.2.1, hoData.2.2.2,
    hfull, hdirection⟩

end

end TranslatedDepthSeven
