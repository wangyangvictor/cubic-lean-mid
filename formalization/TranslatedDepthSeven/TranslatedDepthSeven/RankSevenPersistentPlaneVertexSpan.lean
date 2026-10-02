import TranslatedDepthSeven.RankSevenNodeSurfaceExhaustion
import TranslatedDepthSeven.RankSevenPersistentPlaneDividedSpan
import TranslatedDepthSeven.RankSevenPersistentPlaneLineIncidence

/-!
# The translation vertex and the divided-difference plane

A persistent degree-one node component is a projective plane in the
four-plane section of the translated cone.  If the four-plane did not
contain the translation vertex, projection would carry this component
isomorphically to a degree-one surface component of the displayed
codimension-three section.  Its surviving point would then belong to the
literal low-degree exceptional locus.  Thus every retained plane contains
the translation vertex.

For a rank-two assigned cell, this incidence has a useful elementary
consequence.  The translated projection of the three-dimensional plane is
already spanned by the two-dimensional space of divided differences.
Consequently every original point `x₀ + m z` in the cell belongs to that
space.  Since the cell is contained in one of the fixed rank-seven Jacobian
charts, this supplies a regular point of the divided-difference span.  In
particular, the nominal singular rank-two-plane alternative is empty.

The three genuinely standard projective-geometric facts are stated
separately below.  All exceptional-locus, residue, component, and
linear-algebra bookkeeping is proved for the literal objects used in the
application.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

local instance planeVertexSpanPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

set_option maxHeartbeats 10000000

namespace StandardAG

/-- When the centre of the translated-cone projection belongs to the
cutting four-plane, every irreducible component of the resulting cone
section contains that centre.

This is the elementary component statement for a projective cone: the
section is stable under the one-dimensional additive action along the
vertex, and the connected group cannot permute its finitely many
irreducible components. -/
def RankFourTranslatedConeVertexComponentIncidence : Prop :=
  ∀ (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ)),
    (∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e) →
    A.rank = 4 →
    I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A) →
    Matrix.mulVec A (translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) = 0 →
    translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ) ∈ affineIdealZeroLocus I

/-- Away from the centre, restriction of the translated-cone projection
to the cutting four-plane is a projective linear isomorphism.  It carries
a degree-one source surface to a degree-one geometric component of the
displayed codimension-three image section.

This is degree invariance under a projective linear isomorphism, together
with the standard fact that a degree-one variety is geometrically integral.
Restricting the statement to degree one is essential: an arbitrary prime
over `ℚ` may split after extension to `Qbar`, in which case the degree of one
geometric component need not equal the degree of the rational component.
No counting or exceptional-locus assertion is included. -/
def RankFourTranslatedConeNonvertexDegreeOneComponentProjection : Prop :=
  ∀ (x₀ : IntVector 13) (m : ℕ) (hm : 0 < m)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (A : Matrix (Fin 4) (Fin 14) ℚ)
    (I : Ideal (MvPolynomial (Fin 14) ℚ))
    (z : IntVector 13),
    (∀ f ∈ equations, ∃ e : ℕ, f.IsHomogeneous e) →
    A.rank = 4 →
    I ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ m hm equations A) →
    HasProjectiveDimensionDegree I 2 1 →
    (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈
      affineIdealZeroLocus I →
    ∀ hx : integralAffineMap x₀ z m ≠ 0,
      ∀ i₀ : Fin 4,
        Matrix.mulVec A (translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) i₀ ≠ 0 →
        ∃ Q : Ideal (MvPolynomial (Fin 13) Qbar),
          IsProjectiveSectionComponent equations
              (translatedJoinImageThreeEquationMatrixFin A
                (fun j ↦ (x₀ j : ℚ)) (m : ℚ) i₀) Q ∧
          ProjectivePointVanishesOnGeometricIdeal Q
              (integralProjectiveClass (integralAffineMap x₀ z m) hx) ∧
          HasGeometricProjectiveDimensionDegree Q 2 1

/-- An integral projective surface of degree one is a projective plane;
equivalently its affine cone is a three-dimensional rational linear
subspace.  The dimension is recorded explicitly because it is needed by
the rank-nullity argument below. -/
def DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear : Prop :=
  ∀ (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)),
    I.IsPrime →
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
    HasProjectiveDimensionDegree I 2 1 →
    ∃ L : Submodule ℚ (Fin (N + 1) → ℚ),
      Module.finrank ℚ L = 3 ∧
      (L : Set (Fin (N + 1) → ℚ)) = affineIdealZeroLocus I

end StandardAG

/-- Forgetting the dimension certificate recovers the narrower linear-cone
input used by the full-line incidence file. -/
theorem degreeOneProjectiveSurfaceConeIsLinear_of_threeDimensional
    (hlinear :
      StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear) :
    StandardAG.DegreeOneProjectiveSurfaceConeIsLinear := by
  intro N I hprime hhomogeneous hdegree
  obtain ⟨L, _hLdim, hL⟩ :=
    hlinear N I hprime hhomogeneous hdegree
  exact ⟨L, hL⟩

/-! ## The elementary linear projection calculation -/

/-- The translated projection in standard `Fin 14` coordinates, written
as a linear map for the rank-nullity argument. -/
def rationalTranslatedJoinProjectionLinearMap
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    (Fin 14 → ℚ) →ₗ[ℚ] (Fin 13 → ℚ) where
  toFun := fun v j ↦ v 0 * x₀ j + m * v j.succ
  map_add' := by
    intro u v
    funext j
    simp
    ring
  map_smul' := by
    intro c v
    funext j
    simp
    ring

@[simp]
theorem rationalTranslatedJoinProjectionLinearMap_vertex
    (x₀ : Fin 13 → ℚ) (m : ℚ) :
    rationalTranslatedJoinProjectionLinearMap x₀ m
      (translatedJoinVertexFinVector x₀ m) = 0 := by
  funext j
  simp [rationalTranslatedJoinProjectionLinearMap,
    translatedJoinVertexFinVector, translatedProjectiveConeVertexVector]

@[simp]
theorem rationalTranslatedJoinProjectionLinearMap_affineChart
    (x₀ z : IntVector 13) (m : ℕ) :
    rationalTranslatedJoinProjectionLinearMap
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
        (fun i ↦ (integralAffineChartVector z i : ℚ)) =
      fun j ↦ (integralAffineMap x₀ z m j : ℚ) := by
  funext j
  simp [rationalTranslatedJoinProjectionLinearMap, integralAffineMap]

/-- A three-dimensional source plane containing the translation vertex
projects onto the rational span of any rank-two family of its affine
differences.  This is pure rank-nullity; it contains no algebraic geometry. -/
theorem integralAffineMap_mem_differenceSpan_of_threeDimensionalPlane
    (x₀ base : IntVector 13) (m : ℕ) (hm : 0 < m)
    (L : Submodule ℚ (Fin 14 → ℚ))
    (hLdim : Module.finrank ℚ L = 3)
    (hvertex : translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ) ∈ L)
    (hbase : (fun i ↦ (integralAffineChartVector base i : ℚ)) ∈ L)
    {ι : Type*} (z : ι → IntVector 13)
    (hz : ∀ i, (fun j ↦ (integralAffineChartVector (z i) j : ℚ)) ∈ L)
    (hrank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun i ↦
        rationalIntegralDifference base (z i))) = 2) :
    ∀ i,
      (fun j ↦ (integralAffineMap x₀ (z i) m j : ℚ)) ∈
        Submodule.span ℚ (Set.range fun i ↦
          rationalIntegralDifference base (z i)) := by
  let W : Submodule ℚ (Fin 13 → ℚ) :=
    Submodule.span ℚ (Set.range fun i ↦
      rationalIntegralDifference base (z i))
  let π : (Fin 14 → ℚ) →ₗ[ℚ] (Fin 13 → ℚ) :=
    rationalTranslatedJoinProjectionLinearMap
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)
  let g : L →ₗ[ℚ] (Fin 13 → ℚ) := π.domRestrict L
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have homegaNe :
      (⟨translatedJoinVertexFinVector
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ), hvertex⟩ : L) ≠ 0 := by
    intro hzero
    have hcoordinate := congrFun (congrArg Subtype.val hzero) 0
    simp [translatedJoinVertexFinVector,
      translatedProjectiveConeVertexVector] at hcoordinate
    exact hm.ne' hcoordinate
  have homegaKer :
      (⟨translatedJoinVertexFinVector
        (fun j ↦ (x₀ j : ℚ)) (m : ℚ), hvertex⟩ : L) ∈
          LinearMap.ker g := by
    change π (translatedJoinVertexFinVector
      (fun j ↦ (x₀ j : ℚ)) (m : ℚ)) = 0
    exact rationalTranslatedJoinProjectionLinearMap_vertex _ _
  have hkerPos : 1 ≤ Module.finrank ℚ (LinearMap.ker g) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    have hzero :
        (⟨translatedJoinVertexFinVector
          (fun j ↦ (x₀ j : ℚ)) (m : ℚ), hvertex⟩ : L) = 0 := by
      have :
          (⟨translatedJoinVertexFinVector
            (fun j ↦ (x₀ j : ℚ)) (m : ℚ), hvertex⟩ : L) ∈
              (⊥ : Submodule ℚ L) := by
        rw [← hbot]
        exact homegaKer
      simpa using this
    exact homegaNe hzero
  have hnullity := LinearMap.finrank_range_add_finrank_ker g
  have hrangeLe : Module.finrank ℚ (LinearMap.range g) ≤ 2 := by
    rw [hLdim] at hnullity
    omega
  have hWrange : W ≤ LinearMap.range g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let u : Fin 14 → ℚ :=
      (fun j ↦ (integralAffineChartVector (z i) j : ℚ)) -
        (fun j ↦ (integralAffineChartVector base j : ℚ))
    have huL : u ∈ L := L.sub_mem (hz i) hbase
    have hprojection : π u =
        (m : ℚ) • rationalIntegralDifference base (z i) := by
      funext j
      simp only [π, u, map_sub, rationalTranslatedJoinProjectionLinearMap_affineChart,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rationalIntegralDifference,
        Int.cast_sub]
      simp [integralAffineMap]
      ring
    refine ⟨(m : ℚ)⁻¹ • (⟨u, huL⟩ : L), ?_⟩
    change π ((m : ℚ)⁻¹ • u) = rationalIntegralDifference base (z i)
    rw [map_smul, hprojection, smul_smul, inv_mul_cancel₀ hmQ, one_smul]
  have hWfinrank : Module.finrank ℚ W = 2 := hrank
  have hWeq : W = LinearMap.range g :=
    Submodule.eq_of_le_of_finrank_le hWrange (by simpa [hWfinrank] using hrangeLe)
  intro i
  change (fun j ↦ (integralAffineMap x₀ (z i) m j : ℚ)) ∈ W
  rw [hWeq]
  let source : L :=
    ⟨fun j ↦ (integralAffineChartVector (z i) j : ℚ), hz i⟩
  refine ⟨source, ?_⟩
  exact rationalTranslatedJoinProjectionLinearMap_affineChart x₀ (z i) m

/-! ## Application to the literal persistent plane records -/

section LiteralFamily

variable (p : Parameters) (x₀ : IntVector 13)
  (equations : Finset (MvPolynomial (Fin 13) ℤ)) (CF : ℕ)
  (C : IntegralDepthSevenJacobianChartIndex equations)
  (denominator : ℤ) (P : Finset ℕ) (k : ℕ)
  (hP : ∀ s ∈ P, s.Prime)
  (hlower : ∀ q : ReservoirModulus P k,
    manuscriptReservoirTarget normalizedSurfaceReservoirConstant
      p.T (5 / 7) ≤ q.1)
  (X : Finset (IntVector 13)) (markCount : ℕ)
  (localEquations : Fin 11 → MvPolynomial (Fin 13) ℤ)
  (selectedVar : Fin 11 → Fin 13)
  (menu : Fin markCount → MvPolynomial (Fin 13) ℤ)
  (markOf : IntVector 13 → Fin markCount)

local notation "PlaneOccurrence" =>
  RankSevenPersistentPlaneOccurrence p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "oldCell" =>
  rankSevenPersistentPlanePointCell p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "oldBase" =>
  rankSevenPersistentPlaneRepresentative p x₀ equations CF C denominator
    P k hP hlower X markCount localEquations selectedVar menu markOf

local notation "assignedCell" =>
  rankSevenPersistentPlaneAssignedCell p x₀ equations CF C denominator P k
    hP hlower X markCount localEquations selectedVar menu markOf

local notation "assignedRank" =>
  rankSevenPersistentPlaneAssignedDifferenceRank p x₀ equations CF C
    denominator P k hP hlower X markCount localEquations selectedVar menu markOf

/-- The low-degree exceptional exclusion forces every retained persistent
plane to contain the actual translated-cone vertex `(m,-x₀)`. -/
theorem rankSevenPersistentPlane_vertex_mem_component
    (hvertexComponent :
      StandardAG.RankFourTranslatedConeVertexComponentIncidence)
    (hdegreeProjection :
      StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (o : PlaneOccurrence) :
    translatedJoinVertexFinVector
        (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) ∈
      affineIdealZeroLocus o.1.component := by
  have hplaneRecord := (mem_occupiedRankSevenPersistentPlaneRecords_iff
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o.1).mp o.2
  have hretained := (mem_occupiedRankSevenPersistentMultiplicityOneRecords_iff
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf o.1).mp hplaneRecord.1
  obtain ⟨w, hw⟩ := persistentMultiplicityOneRecord_has_witness
    p x₀ equations CF C denominator P k markCount hP hlower X
      localEquations selectedVar menu markOf o.1 hplaneRecord.1
  have hwSpec := (mem_rankSevenPersistentMultiplicityOneWitnessCell_iff
    p x₀ equations CF C denominator P k hP hlower X localEquations
      selectedVar menu markOf o.1 w).mp hw
  have hwCell := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf o.1 w).mp hwSpec.1
  have hwReservoir : w ∈ rankSevenChartReservoirCell
      p x₀ equations CF C denominator o.1.modulus.1 := by
    exact Finset.mem_filter.mpr ⟨hwCell.1, hwSpec.2.2.2.1⟩
  let Aint := selectedRankSevenPacketSectionMatrix
    p x₀ equations CF C o.1.modulus.1
      (integralResidueVector w : Fin 13 → ZMod o.1.modulus.1)
  let A := Aint.map ((↑) : ℤ → ℚ)
  have hA : A.rank = 4 :=
    selectedRankSevenPacketSectionMatrix_rank
      p x₀ equations CF C denominator P k hP hlower o.1.modulus w hwReservoir
  have hnode := rankSevenPersistentPlaneComponent_mem_nodeComponents
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o
  have hcomponentSource : o.1.component ∈ finiteMinimalPrimes
      (rankSevenSourceSectionIdeal x₀ p.m p.hm equations A) := by
    simpa [rankSevenNodeComponents, rankSevenNodeEquationIdeal,
      rankSevenSourceSectionEquationsAtResidue, A, Aint, hwCell.2.1] using hnode
  let base := oldBase o
  have hbaseOld : base ∈ oldCell o :=
    rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu markOf o
  have hbaseData := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf o.1 base).mp hbaseOld
  have hbaseComponent :
      (fun i ↦ (integralAffineChartVector base i : ℚ)) ∈
        affineIdealZeroLocus o.1.component := hbaseData.2.2.1
  have hbaseNormalized := (mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF C base).mp hbaseData.1 |>.1
  have hbaseNormalizedData := Finset.mem_filter.mp hbaseNormalized |>.2
  obtain ⟨_hbox, _hzero, hx, _hlinear, hnotExceptional⟩ :=
    hbaseNormalizedData
  have hdichotomy := selectedRankSevenPacketSection_projected_dichotomy
    p x₀ equations CF hCF hx₀ C denominator P k hP hlower
      o.1.modulus w hwReservoir
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
  rcases hdichotomy with hfour | hthree
  · exact hvertexComponent x₀ p.m p.hm equations A o.1.component hhomogeneous hA
      hcomponentSource hfour.1
  · obtain ⟨i₀, hpivot, hrank, hheight⟩ := hthree
    obtain ⟨Q, hQcomponent, hxQ, hQdegree⟩ :=
      hdegreeProjection x₀ p.m p.hm equations A o.1.component base hhomogeneous hA
        hcomponentSource hplaneRecord.2 hbaseComponent hx i₀ hpivot
    have hQbound := codimensionThree_component_dimension_degree_of_not_exceptional
      equations ⌈p.H ^ CF⌉₊
        (translatedJoinImageThreeEquationMatrixFin A
          (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) i₀)
        hrank hheight Q hQcomponent
        (integralProjectiveClass (integralAffineMap x₀ base p.m) hx)
        hxQ hnotExceptional hQdegree
    omega

/-- The literal retained component is a three-dimensional linear cone and
its linear space contains the translated-cone vertex. -/
theorem exists_rankSevenPersistentPlane_threeDimensionalLinearCone_through_vertex
    (hlinear :
      StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear)
    (hvertexComponent :
      StandardAG.RankFourTranslatedConeVertexComponentIncidence)
    (hdegreeProjection :
      StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (o : PlaneOccurrence) :
    ∃ L : Submodule ℚ (Fin 14 → ℚ),
      Module.finrank ℚ L = 3 ∧
      (L : Set (Fin 14 → ℚ)) = affineIdealZeroLocus o.1.component ∧
      translatedJoinVertexFinVector
        (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) ∈ L := by
  have hnode := rankSevenPersistentPlaneComponent_mem_nodeComponents
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o
  have hdegree := (mem_occupiedRankSevenPersistentPlaneRecords_iff
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf o.1).mp o.2 |>.2
  obtain ⟨L, hLdim, hL⟩ := hlinear 13 o.1.component
    (rankSevenNodeComponent_isPrime p x₀ equations CF C
      o.1.modulus.1 o.1.residue o.1.component hnode)
    (rankSevenNodeComponent_isHomogeneous p x₀ equations CF hhomogeneous C
      o.1.modulus.1 o.1.residue o.1.component hnode)
    hdegree
  refine ⟨L, hLdim, hL, ?_⟩
  change translatedJoinVertexFinVector
    (fun j ↦ (x₀ j : ℚ)) (p.m : ℚ) ∈ (L : Set (Fin 14 → ℚ))
  rw [hL]
  exact rankSevenPersistentPlane_vertex_mem_component
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf hvertexComponent hdegreeProjection
        hCF hx₀ hhomogeneous o

/-- Every original point assigned to a rank-two persistent plane belongs
to the rational span of that occurrence's actual divided differences. -/
theorem rankSevenPersistentPlane_originalPoint_mem_assignedDifferenceSpan
    (hlinear :
      StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear)
    (hvertexComponent :
      StandardAG.RankFourTranslatedConeVertexComponentIncidence)
    (hdegreeProjection :
      StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence)
    (hrank : assignedRank planePoints recordOf o = 2)
    (z : IntVector 13) (hz : z ∈ assignedCell planePoints recordOf o) :
    (fun i ↦ (integralAffineMap x₀ z p.m i : ℚ)) ∈
      Submodule.span ℚ (Set.range fun
        w : {w // w ∈ assignedCell planePoints recordOf o} ↦
          rationalIntegralDifference (oldBase o) w.1) := by
  obtain ⟨L, hLdim, hL, hvertex⟩ :=
    exists_rankSevenPersistentPlane_threeDimensionalLinearCone_through_vertex
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf hlinear hvertexComponent
          hdegreeProjection hCF hx₀ hhomogeneous o
  have hbase :
      (fun i ↦ (integralAffineChartVector (oldBase o) i : ℚ)) ∈ L := by
    change (fun i ↦ (integralAffineChartVector (oldBase o) i : ℚ)) ∈
      (L : Set (Fin 14 → ℚ))
    rw [hL]
    exact (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf o.1 (oldBase o)).mp
        (rankSevenPersistentPlaneRepresentative_mem p x₀ equations CF C
          denominator P k hP hlower X markCount localEquations selectedVar menu
            markOf o) |>.2.2.1
  have hpoints : ∀ w : {w // w ∈ assignedCell planePoints recordOf o},
      (fun i ↦ (integralAffineChartVector w.1 i : ℚ)) ∈ L := by
    intro w
    change (fun i ↦ (integralAffineChartVector w.1 i : ℚ)) ∈
      (L : Set (Fin 14 → ℚ))
    rw [hL]
    have hwOld := rankSevenPersistentPlaneAssignedCell_subset_oldCell
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf planePoints recordOf hrecordOf o w.2
    exact (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf o.1 w.1).mp hwOld |>.2.2.1
  exact integralAffineMap_mem_differenceSpan_of_threeDimensionalPlane
    x₀ (oldBase o) p.m p.hm L hLdim hvertex hbase
      (fun w : {w // w ∈ assignedCell planePoints recordOf o} ↦ w.1)
      hpoints hrank ⟨z, hz⟩

/-- If the rank-two difference span had no Jacobian-regular integral
point, every assigned displacement would lie in the fixed normalized
rank-at-most-six locus.  This is the precise set-theoretic form of the
nominal singular-span alternative. -/
theorem rankSevenPersistentPlaneAssignedCell_subset_rankAtMostSix_of_noRegularSpan
    (hlinear :
      StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear)
    (hvertexComponent :
      StandardAG.RankFourTranslatedConeVertexComponentIncidence)
    (hdegreeProjection :
      StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence)
    (hrank : assignedRank planePoints recordOf o = 2)
    (hnoRegular : ∀ x : IntVector 13,
      (fun i ↦ (x i : ℚ)) ∈
        Submodule.span ℚ (Set.range fun
          w : {w // w ∈ assignedCell planePoints recordOf o} ↦
            rationalIntegralDifference (oldBase o) w.1) →
      ¬ IsDepthSevenJacobianRegularAt equations x) :
    assignedCell planePoints recordOf o ⊆
      depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF := by
  intro z hz
  apply (mem_depthSevenNormalizedRankAtMostSixFinset_iff
    p x₀ equations CF z).mpr
  have hzOld := rankSevenPersistentPlaneAssignedCell_subset_oldCell
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf planePoints recordOf hrecordOf o hz
  have hzChart := (mem_rankSevenPersistentRecordPointCell_iff
    p x₀ equations CF C markOf o.1 z).mp hzOld |>.1
  refine ⟨(mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF C z).mp hzChart |>.1, ?_⟩
  apply hnoRegular (integralAffineMap x₀ z p.m)
  exact rankSevenPersistentPlane_originalPoint_mem_assignedDifferenceSpan
    p x₀ equations CF C denominator P k hP hlower X markCount
      localEquations selectedVar menu markOf hlinear hvertexComponent
        hdegreeProjection hCF hx₀ hhomogeneous planePoints recordOf hrecordOf
          o hrank z hz

/-- A rank-two assigned persistent-plane cell automatically has a regular
integral point in its divided-difference span.  The point is one of the
original vectors `x₀ + m z`; regularity is inherited from the literal
rank-seven chart containing the cell. -/
theorem exists_rankSevenPersistentPlane_regularPoint_in_assignedDifferenceSpan
    (hlinear :
      StandardAG.DegreeOneProjectiveSurfaceConeIsThreeDimensionalLinear)
    (hvertexComponent :
      StandardAG.RankFourTranslatedConeVertexComponentIncidence)
    (hdegreeProjection :
      StandardAG.RankFourTranslatedConeNonvertexDegreeOneComponentProjection)
    (hCF : depthSevenProjectedSectionHeightExponent ≤ CF)
    (hx₀ : x₀ ∈ depthSevenTranslatedPointFinset p equations CF)
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (planePoints : Finset (IntVector 13))
    (recordOf : IntVector 13 → PlaneOccurrence)
    (hrecordOf : IsLiteralPersistentPlaneAssignment p x₀ equations CF C
      denominator P k hP hlower X markCount localEquations selectedVar menu
        markOf planePoints recordOf)
    (o : PlaneOccurrence)
    (hrank : assignedRank planePoints recordOf o = 2) :
    ∃ x : IntVector 13,
      (fun i ↦ (x i : ℚ)) ∈
        Submodule.span ℚ (Set.range fun
          w : {w // w ∈ assignedCell planePoints recordOf o} ↦
            rationalIntegralDifference (oldBase o) w.1) ∧
      IsDepthSevenJacobianRegularAt equations x := by
  let v : {w // w ∈ assignedCell planePoints recordOf o} → IntVector 13 :=
    fun w i ↦ w.1 i - oldBase o i
  have hvRank : Module.finrank ℚ
      (Submodule.span ℚ (Set.range fun w i ↦ (v w i : ℚ))) = 2 := by
    simpa only [v, rationalIntegralDifference, Int.cast_sub] using hrank
  obtain ⟨w, _w', _hspan, _hminor⟩ :=
    exists_twoVector_generators_of_finrank_span_eq_two v hvRank
  let x : IntVector 13 := integralAffineMap x₀ w.1 p.m
  refine ⟨x, ?_, ?_⟩
  · exact rankSevenPersistentPlane_originalPoint_mem_assignedDifferenceSpan
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf hlinear hvertexComponent
          hdegreeProjection hCF hx₀ hhomogeneous planePoints recordOf
            hrecordOf o hrank w.1 w.2
  · have hwOld := rankSevenPersistentPlaneAssignedCell_subset_oldCell
      p x₀ equations CF C denominator P k hP hlower X markCount
        localEquations selectedVar menu markOf planePoints recordOf hrecordOf o w.2
    have hwChart := (mem_rankSevenPersistentRecordPointCell_iff
      p x₀ equations CF C markOf o.1 w.1).mp hwOld |>.1
    unfold IsDepthSevenJacobianRegularAt
    apply rationalJacobian_rank_ge_of_integralMinor_ne_zero
      (indexedFinsetFamily equations) x C.rows C.cols
    simpa only [IntegralDepthSevenJacobianChartIndex.determinant,
      eval_integralJacobianMinorPolynomial, x] using
        eval_chart_determinant_ne_zero_of_mem_normalizedChartCell
          p x₀ equations CF C hwChart

end LiteralFamily

end

end TranslatedDepthSeven
