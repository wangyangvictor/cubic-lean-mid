import TranslatedDepthSeven.RankSevenDegreeOneLowDirectionSource
import TranslatedDepthSeven.ProjectiveVertexTranslationInvariant
import TranslatedDepthSeven.DepthSevenRankSevenPacketAssembly

/-!
# Grouping the literal degree-one points in one projective star

The line ledger groups all active node, edge, and persistent degree-one
occurrences by their common *projective* direction.  This file supplies the
incidence statement in the orientation required by that grouping.

For one tagged point `z`, the original point `x₀ + m z` lies in the
explicit equation-level projective star centred at the primitive direction
of its occurrence.  If two occurrences have the same projective direction,
their primitive integral representatives are proportional, and the explicit
stars are equal.  Thus the whole low-direction fibre is contained in one
literal star.  No estimate for lines, stars, components, or points is an
input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

local instance rankSevenProperStarProjectiveDecidableEq :
    DecidableEq (Projectivization ℚ (Fin 13 → ℚ)) := Classical.decEq _

set_option maxHeartbeats 8000000

/-- A point assigned to an active integral line belongs, after undoing the
normalization, to the star centred at that occurrence's primitive direction.
The nonzero premise is exactly the punctured-cone condition retained in the
original depth-seven point set. -/
theorem activeTaggedPoint_mem_star_centeredAt_occurrenceDirection
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (base direction : TaggedLinearComponent J → IntVector 13)
    (parameter : TaggedLinearComponent J → IntVector 13 → ℤ)
    (hdata : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑((assignedLinearComponentFibre J Y o).image
          (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
      (∀ z ∈ (assignedLinearComponentFibre J Y o).image
          (fun x ↦ x.2.1),
        z = fun i ↦ base o i + parameter o z * direction o i))
    (hline : ∀ o ∈ activeTaggedLinearComponents J Y, ∀ t : ℤ,
      IntegralCommonZero equations
        (integralAffineMap x₀
          (fun i ↦ base o i + t * direction o i) p.m))
    (x : TaggedLinearContributionPoint J Y)
    (hx : x ∈ activeTaggedLinearContributionPoints J Y)
    (hxne : integralAffineMap x₀ x.2.1 p.m ≠ 0) :
    integralProjectiveClass (integralAffineMap x₀ x.2.1 p.m) hxne ∈
      integralProjectiveStarLocus equations degree
        (direction (linearComponentOccurrenceOfPoint J Y x)) := by
  classical
  let o := linearComponentOccurrenceOfPoint J Y x
  have ho : o ∈ activeTaggedLinearComponents J Y :=
    (mem_activeTaggedLinearContributionPoints_iff J Y x).1 hx
  have hxAssigned : x ∈ assignedLinearComponentFibre J Y o := by
    simp [assignedLinearComponentFibre, o]
  have hxImage : x.2.1 ∈
      (assignedLinearComponentFibre J Y o).image (fun w ↦ w.2.1) :=
    Finset.mem_image.mpr ⟨x, hxAssigned, rfl⟩
  have hxParam := (hdata o ho).2.2 x.2.1 hxImage
  apply basePoint_mem_projectiveStar_of_scaledIntegralLine
    equations degree hdegree (integralAffineMap x₀ x.2.1 p.m)
      (direction o) p.m p.hm hxne
  intro t
  have ht := hline o ho (parameter o x.2.1 + t)
  rw [show (fun i ↦ integralAffineMap x₀ x.2.1 p.m i +
        t * ((p.m : ℤ) * direction o i)) =
      integralAffineMap x₀
        (fun i ↦ base o i + (parameter o x.2.1 + t) * direction o i)
        p.m by
    funext i
    simp only [integralAffineMap]
    rw [congrFun hxParam i]
    ring]
  exact ht

/-- Equality of projective classes of two nonzero integral vectors gives
the literal nonzero rational proportionality used to identify their
explicit stars. -/
theorem exists_nonzero_rational_proportionality_of_integralProjectiveClass_eq
    {n : ℕ} (h k : IntVector n) (hh : h ≠ 0) (hk : k ≠ 0)
    (heq : integralProjectiveClass k hk = integralProjectiveClass h hh) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ i, (k i : ℚ) = q * (h i : ℚ) := by
  change Projectivization.mk ℚ (fun i ↦ (k i : ℚ)) _ =
    Projectivization.mk ℚ (fun i ↦ (h i : ℚ)) _ at heq
  obtain ⟨q, hq⟩ := (Projectivization.mk_eq_mk_iff' ℚ
    (fun i ↦ (k i : ℚ)) (fun i ↦ (h i : ℚ))
    (intCast_ne_zero (K := ℚ) hk) (intCast_ne_zero (K := ℚ) hh)).1 heq
  have hqne : q ≠ 0 := by
    intro hqzero
    subst q
    apply hk
    funext i
    have hiQ : (k i : ℚ) = 0 := by
      simpa only [zero_smul] using (congrFun hq i).symm
    exact_mod_cast hiQ
  refine ⟨q, hqne, ?_⟩
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun hq i).symm

/-- All active tagged points whose occurrences have one fixed projective
direction lie in the same explicit star, centred at any chosen primitive
integral representative supplied by one occurrence in that fibre. -/
theorem activeProjectiveDirectionFibre_subset_one_explicitStar
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    { ι : Type*} [Fintype ι]
    (J : ι → Ideal (MvPolynomial (Fin 13) ℝ))
    (Y : ι → Finset (IntVector 13))
    (base direction : TaggedLinearComponent J → IntVector 13)
    (parameter : TaggedLinearComponent J → IntVector 13 → ℤ)
    (hdata : ∀ o ∈ activeTaggedLinearComponents J Y,
      PrimitiveDirection (direction o) ∧
      Set.InjOn (parameter o)
        (↑((assignedLinearComponentFibre J Y o).image
          (fun x ↦ x.2.1)) : Set (IntVector 13)) ∧
      (∀ z ∈ (assignedLinearComponentFibre J Y o).image
          (fun x ↦ x.2.1),
        z = fun i ↦ base o i + parameter o z * direction o i))
    (hline : ∀ o ∈ activeTaggedLinearComponents J Y, ∀ t : ℤ,
      IntegralCommonZero equations
        (integralAffineMap x₀
          (fun i ↦ base o i + t * direction o i) p.m))
    (o₀ : TaggedLinearComponent J)
    (ho₀ : o₀ ∈ activeTaggedLinearComponents J Y)
    (x : TaggedLinearContributionPoint J Y)
    (hx : x ∈ activeTaggedLinearContributionPoints J Y)
    (hxDirection : taggedLinearPointProjectiveDirection J Y direction x =
      integralProjectiveClassOrFirstRankSeven (direction o₀))
    (hxne : integralAffineMap x₀ x.2.1 p.m ≠ 0) :
    integralProjectiveClass (integralAffineMap x₀ x.2.1 p.m) hxne ∈
      integralProjectiveStarLocus equations degree (direction o₀) := by
  classical
  let o := linearComponentOccurrenceOfPoint J Y x
  have ho : o ∈ activeTaggedLinearComponents J Y :=
    (mem_activeTaggedLinearContributionPoints_iff J Y x).1 hx
  have hoPrimitive := (hdata o ho).1
  have ho₀Primitive := (hdata o₀ ho₀).1
  have hOne := activeTaggedPoint_mem_star_centeredAt_occurrenceDirection
    p x₀ equations degree hdegree J Y base direction parameter hdata hline
      x hx hxne
  have hoNe : direction o ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hoPrimitive.exists_ne_zero
    exact hi (congrFun hz i)
  have ho₀Ne : direction o₀ ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := ho₀Primitive.exists_ne_zero
    exact hi (congrFun hz i)
  have hclasses : integralProjectiveClass (direction o) hoNe =
      integralProjectiveClass (direction o₀) ho₀Ne := by
    simpa [taggedLinearPointProjectiveDirection,
      integralProjectiveClassOrFirstRankSeven, o, hoNe, ho₀Ne] using
        hxDirection
  obtain ⟨q, hq, hproportional⟩ :=
    exists_nonzero_rational_proportionality_of_integralProjectiveClass_eq
      (direction o₀) (direction o) ho₀Ne hoNe hclasses
  rw [integralProjectiveStarLocus_eq_of_proportional_centers
    equations degree hdegree (direction o₀) (direction o) q hq
      hproportional]
  exact hOne

/-! ## Specialization to the literal node--edge--persistent family -/

/-- Every point retained by an actual degree-one node, edge, or persistent
record is still a point of the original normalized displacement set.  This
is the precise fact which supplies the nonzero original point used by the
projective-star incidence. -/
theorem rankSevenDegreeOnePointSet_mem_normalizedDisplacement
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
    (i : RankSevenDegreeOneIndex p x₀ equations CF Cchart model P k
      markCount hP hlower X localEquations selectedVar menu markOf)
    {z : IntVector 13}
    (hz : z ∈ rankSevenDegreeOnePointSet p x₀ equations CF Cchart model
      P k markCount hP hlower I X localEquations selectedVar menu markOf i) :
    z ∈ depthSevenNormalizedDisplacementFinset p x₀ equations CF := by
  have hzChart : z ∈
      depthSevenNormalizedJacobianChartCell p x₀ equations CF Cchart := by
    rcases i with (node | edge) | persistent
    · exact (mem_rankSevenNonSurfaceNodeRecordPointCell_iff
        p x₀ equations CF Cchart node.2.1 z).1 hz |>.1
    · exact (mem_rankSevenSurfaceEdgeFrontierPointCell_iff
        p x₀ equations CF Cchart P k edge.2.1.1 edge.2.2.1 z).1 hz |>.1
    · exact (mem_integralResiduePacket_iff.1
        ((mem_rankSevenPacketPointsOnSourceComponent_iff _ _ _).1 hz |>.1)).1
  exact (mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF Cchart z).1 hzChart |>.1

/-- Literal specialization of the preceding fibre theorem.  The indexing
family here is exactly the disjoint node/edge/persistent family, and its
point sets are the actual record cells.  For any active occurrence `o₀`,
every active tagged point whose occurrence has the same projective
direction as `o₀` maps to a point of the one explicit star centred at the
primitive direction of `o₀`.

No count of lines, stars, components, or points occurs in this statement.
The remaining smooth-centre and singular-nonvertex estimates can therefore
start from this displayed star without changing the literal ledger. -/
theorem exists_rankSevenDegreeOne_actual_fibres_in_one_explicitStar
    (hline : StandardAG.DegreeOneAffinePrimeCurveIsIntegralLine)
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
    (degree : MvPolynomial (Fin 13) ℤ → ℕ)
    (hdegree : ∀ f ∈ equations, f.IsHomogeneous (degree f))
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
      (∀ o ∈ activeTaggedLinearComponents J Y,
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
        IntegralCommonZero equations (direction o)) ∧
      ∀ o₀ ∈ activeTaggedLinearComponents J Y,
        ∀ x ∈ activeTaggedLinearContributionPoints J Y,
          taggedLinearPointProjectiveDirection J Y direction x =
              integralProjectiveClassOrFirstRankSeven (direction o₀) →
            ∃ hxne : integralAffineMap x₀ x.2.1 p.m ≠ 0,
              integralProjectiveClass
                  (integralAffineMap x₀ x.2.1 p.m) hxne ∈
                integralProjectiveStarLocus equations degree
                  (direction o₀) := by
  classical
  dsimp only
  let J := rankSevenDegreeOneIdeal p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf auxiliaryForm
  let Y := rankSevenDegreeOnePointSet p x₀ equations CF Cchart model P k
    markCount hP hlower I X localEquations selectedVar menu markOf
  have hhomogeneous : ∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e := by
    intro f hf
    exact ⟨degree f, hdegree f hf⟩
  obtain ⟨base, direction, parameter, hfull⟩ :=
    exists_rankSevenDegreeOne_fullLines_in_originalCone
      hline p x₀ equations CF hhomogeneous Cchart model P k markCount hP
        hlower I X hX localEquations selectedVar menu markOf auxiliaryForm
  refine ⟨base, direction, parameter, hfull, ?_⟩
  intro o₀ ho₀ x hx hxDirection
  have hxY : x.2.1 ∈ Y x.1 :=
    finitePointsOnLinearCurveComponents_subset (J x.1) (Y x.1) x.2.2
  have hxNormalized : x.2.1 ∈
      depthSevenNormalizedDisplacementFinset p x₀ equations CF :=
    rankSevenDegreeOnePointSet_mem_normalizedDisplacement
      p x₀ equations CF Cchart model P k markCount hP hlower I X
        localEquations selectedVar menu markOf x.1 hxY
  have hxdata := (Finset.mem_filter.mp hxNormalized).2
  dsimp only at hxdata
  obtain ⟨_hbox, _hzero, hxne, _hlinear, _hexceptional⟩ := hxdata
  refine ⟨hxne, ?_⟩
  apply activeProjectiveDirectionFibre_subset_one_explicitStar
    p x₀ equations degree hdegree J Y base direction parameter
      (fun o ho ↦ ⟨(hfull o ho).1, (hfull o ho).2.1,
        (hfull o ho).2.2.1⟩)
      (fun o ho ↦ (hfull o ho).2.2.2.2.1)
      o₀ ho₀ x hx hxDirection hxne

end

end TranslatedDepthSeven
