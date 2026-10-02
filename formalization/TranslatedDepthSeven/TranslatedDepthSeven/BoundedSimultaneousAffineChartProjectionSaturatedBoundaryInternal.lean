import TranslatedDepthSeven.BoundedSimultaneousAffineChartProjectionPrimeInternal
import TranslatedDepthSeven.BoundedSimultaneousSaturatedBoundaryInternal

/-!
# A common bounded affine-chart projection for a source and a saturated boundary

For a positive-dimensional homogeneous prime source, a distinguished
normalization fixing `X₀` restricts to any prime homogeneous saturated
boundary containing the literal `X₀ = 0` specialization.  One bounded
primitive row can be chosen for both function-field extensions.  The
resulting literal integral matrix is therefore finite and birational on
the source and, after deleting its first row and column, finite and
birational on the boundary.  Both scheme-theoretic images retain the
given projective degree.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Matrix Published StandardAG
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 700000

/-- A single matrix from a coefficient-independent finite menu gives
finite birational projections of a source of dimension `r+1` and a chosen prime saturated boundary of dimension `r`, with exact image degrees and
the uniform geometric fibre bounds built into the projection predicates. -/
theorem exists_bounded_simultaneousAffineChartProjection_saturatedBoundary
    {N r degree degreeBound : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 2)) ℚ))
    (J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIJ : projectiveBoundaryIdeal I ≤ J)
    (hI : I.IsPrime)
    (hhom : I.IsHomogeneous
      (homogeneousSubmodule (Fin (N + 2)) ℚ))
    (hX : X (0 : Fin (N + 2)) ∉ I)
    (hdegree : HasProjectiveDimensionDegree I (r + 1) degree)
    (hJprime : J.IsPrime)
    (hJhom : J.IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hJdegree : HasProjectiveDimensionDegree J r degree)
    (hle : degree ≤ degreeBound) :
    ∃ A ∈ boundedIntegralSimultaneousAffineProjectionMatrices
          (N + 1) (r + 1) degreeBound,
      ∃ G : MvPolynomial (Fin (r + 3)) ℚ,
      ∃ H : MvPolynomial (Fin (r + 2)) ℚ,
        IsAffineChartFiniteBirationalLinearProjection
            (degree := degree) I hI A G ∧
        IsHomogeneousFiniteBirationalLinearProjection
            (degree := degree) J hJprime
            (affineChartProjectionBoundaryMatrix (N := N + 1) (r := r + 1)
              (A.map (Int.castRingHom ℚ))) H ∧
        HasProjectiveDimensionDegree
          (RingHom.ker
            (projectiveMatrixCoordinateMap I
              (A.map (Int.castRingHom ℚ))).toRingHom) (r + 1) degree ∧
        HasProjectiveDimensionDegree
          (RingHom.ker
            (projectiveMatrixCoordinateMap J
              (affineChartProjectionBoundaryMatrix (N := N + 1) (r := r + 1)
                (A.map (Int.castRingHom ℚ)))).toRingHom)
          r degree := by
  classical
  letI : I.IsPrime := hI
  obtain ⟨A₀, hA₀, hfirst, hinj, hfin⟩ :=
    exists_mem_boundedIntegralDistinguishedNormalizationMatrices
      (N + 1) I hI hhom hX hdegree hle
  let A₀Q := A₀.map (Int.castRingHom ℚ)
  have hfirstQ : ∀ j, A₀Q 0 j = if j = 0 then 1 else 0 := by
    intro j
    simp [A₀Q, hfirst]
  let D := homogeneousLinearNormalizationDataOfIntegralMatrix I A₀ hinj hfin
  let Dboundary := distinguishedNormalizationSaturatedBoundaryData I J hIJ A₀Q hfirstQ hfin
    hJprime hJdegree (Nat.succ_pos r)
  let vsource : Fin (N + 2) → (MvPolynomial (Fin (N + 2)) ℚ ⧸ I) :=
    fun i ↦ Ideal.Quotient.mk I (X i)
  let vboundary : Fin (N + 2) →
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ J) :=
    paddedSaturatedBoundaryQuotientCoordinates J
  have hgenerateSource :
      let B := MvPolynomial (Fin D.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 2)) ℚ ⧸ I
      letI : Algebra B R := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B R :=
        (faithfulSMul_iff_algebraMap_injective B R).mpr D.hom_injective
      letI : Algebra (FractionRing B) (FractionRing R) :=
        FractionRing.liftAlgebra B (FractionRing R)
      IntermediateField.adjoin (FractionRing B)
        (Set.range fun i ↦ algebraMap R (FractionRing R) (vsource i)) = ⊤ := by
    dsimp only
    let B := MvPolynomial (Fin D.parameterCount) ℚ
    let R := MvPolynomial (Fin (N + 2)) ℚ ⧸ I
    letI : Algebra B R := D.hom.toRingHom.toAlgebra
    letI : IsScalarTower ℚ B R :=
      IsScalarTower.of_algebraMap_eq fun k ↦ (D.hom.commutes k).symm
    letI : FaithfulSMul B R :=
      (faithfulSMul_iff_algebraMap_injective B R).mpr D.hom_injective
    letI : Algebra (FractionRing B) (FractionRing R) :=
      FractionRing.liftAlgebra B (FractionRing R)
    letI : IsScalarTower B (FractionRing B) (FractionRing R) :=
      FractionRing.isScalarTower_liftAlgebra B (FractionRing R)
    letI : IsScalarTower ℚ (FractionRing B) (FractionRing R) := inferInstance
    change IntermediateField.adjoin (FractionRing B)
      (Set.range fun i ↦ algebraMap R (FractionRing R) (vsource i)) = ⊤
    dsimp only [vsource]
    exact adjoin_fractionField_affineQuotient_coordinates_eq_top I
  have hgenerateBoundary :
      let B := MvPolynomial (Fin Dboundary.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 1)) ℚ ⧸ J
      letI : Algebra B R := Dboundary.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B R :=
        (faithfulSMul_iff_algebraMap_injective B R).mpr Dboundary.hom_injective
      letI : Algebra (FractionRing B) (FractionRing R) :=
        FractionRing.liftAlgebra B (FractionRing R)
      IntermediateField.adjoin (FractionRing B)
        (Set.range fun i ↦ algebraMap R (FractionRing R) (vboundary i)) = ⊤ := by
    dsimp only
    let B := MvPolynomial (Fin Dboundary.parameterCount) ℚ
    let R := MvPolynomial (Fin (N + 1)) ℚ ⧸ J
    letI : Algebra B R := Dboundary.hom.toRingHom.toAlgebra
    letI : IsScalarTower ℚ B R :=
      IsScalarTower.of_algebraMap_eq fun k ↦ (Dboundary.hom.commutes k).symm
    letI : FaithfulSMul B R :=
      (faithfulSMul_iff_algebraMap_injective B R).mpr Dboundary.hom_injective
    letI : Algebra (FractionRing B) (FractionRing R) :=
      FractionRing.liftAlgebra B (FractionRing R)
    letI : IsScalarTower B (FractionRing B) (FractionRing R) :=
      FractionRing.isScalarTower_liftAlgebra B (FractionRing R)
    letI : IsScalarTower ℚ (FractionRing B) (FractionRing R) := inferInstance
    change IntermediateField.adjoin (FractionRing B)
      (Set.range fun i ↦ algebraMap R (FractionRing R) (vboundary i)) = ⊤
    dsimp only [vboundary]
    exact adjoin_paddedSaturatedBoundaryQuotientCoordinates_eq_top J hJprime _
  have hcommon := exists_bounded_simultaneous_primitive_normalization_coordinate
    I hI hhom D hdegree hle
    J hJprime hJhom Dboundary
      hJdegree hle
    vsource vboundary hgenerateSource hgenerateBoundary
  dsimp only at hcommon
  obtain ⟨c, hc, hminSource, hprimitiveSource,
    hminBoundary, hprimitiveBoundary⟩ := hcommon
  let wsource : MvPolynomial (Fin (N + 2)) ℚ :=
    ∑ i, C (c i : ℚ) * X i
  let wboundary : MvPolynomial (Fin (N + 1)) ℚ :=
    simultaneousBoundaryPrimitivePolynomial c
  have hmksource : Ideal.Quotient.mk I wsource =
      ∑ i, (c i : ℚ) • vsource i := by
    simp [wsource, vsource, Algebra.smul_def]
  have hmkboundary : Ideal.Quotient.mk J wboundary =
      ∑ i, (c i : ℚ) • vboundary i := by
    simpa [wboundary, vboundary] using
      mk_simultaneousSaturatedBoundaryPrimitivePolynomial J c
  have hminSource' :
      let B := MvPolynomial (Fin D.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 2)) ℚ ⧸ I
      letI : Algebra B R := D.hom.toRingHom.toAlgebra
      (minpoly B (Ideal.Quotient.mk I wsource)).natDegree = degree := by
    dsimp only
    rw [hmksource]
    exact hminSource
  have hminBoundary' :
      let B := MvPolynomial (Fin Dboundary.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 1)) ℚ ⧸ J
      letI : Algebra B R := Dboundary.hom.toRingHom.toAlgebra
      (minpoly B (Ideal.Quotient.mk J wboundary)).natDegree =
        degree := by
    dsimp only
    rw [hmkboundary]
    exact hminBoundary
  have hprimitiveSource' :
      let B := MvPolynomial (Fin D.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 2)) ℚ ⧸ I
      letI : Algebra B R := D.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B R :=
        (faithfulSMul_iff_algebraMap_injective B R).mpr D.hom_injective
      letI : Algebra (FractionRing B) (FractionRing R) :=
        FractionRing.liftAlgebra B (FractionRing R)
      IntermediateField.adjoin (FractionRing B)
        ({algebraMap R (FractionRing R) (Ideal.Quotient.mk I wsource)} :
          Set (FractionRing R)) = ⊤ := by
    dsimp only
    rw [hmksource]
    exact hprimitiveSource
  have hprimitiveBoundary' :
      let B := MvPolynomial (Fin Dboundary.parameterCount) ℚ
      let R := MvPolynomial (Fin (N + 1)) ℚ ⧸ J
      letI : Algebra B R := Dboundary.hom.toRingHom.toAlgebra
      letI : FaithfulSMul B R :=
        (faithfulSMul_iff_algebraMap_injective B R).mpr Dboundary.hom_injective
      letI : Algebra (FractionRing B) (FractionRing R) :=
        FractionRing.liftAlgebra B (FractionRing R)
      IntermediateField.adjoin (FractionRing B)
        ({algebraMap R (FractionRing R)
            (Ideal.Quotient.mk J wboundary)} :
          Set (FractionRing R)) = ⊤ := by
    dsimp only
    rw [hmkboundary]
    exact hprimitiveBoundary
  have hwhomSource : wsource.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  obtain ⟨G₀, _hfinite₀, hker₀, hG₀hom, hG₀irr, hdegree₀⟩ :=
    augmentedLinearNormalization_exists_kernel_and_exact_image_degree
      I hI hhom D rfl wsource hwhomSource hdegree.2.1 hminSource'
  let σ := Equiv.swap (0 : Fin (r + 3)) 1
  let E := MvPolynomial.renameEquiv ℚ σ
  let projectionMatrix := primitiveAffineProjectionMatrix A₀ c
  let source := MvPolynomial (Fin (N + 2)) ℚ ⧸ I
  let hsourceMap : MvPolynomial (Fin (r + 3)) ℚ →ₐ[ℚ] source :=
    projectiveMatrixCoordinateMap I
      (projectionMatrix.map (Int.castRingHom ℚ))
  have hsourceMapEq : hsourceMap =
      (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I wsource)).comp
        E.toAlgHom := by
    simpa [hsourceMap, projectionMatrix, E, σ, wsource] using
      primitiveAffineProjectionMatrix_coordinateMap_eq_augmented
        I A₀ hinj hfin c
  have hsourceKernelData :=
    principal_kernel_and_projectiveDegree_precomp_rename
      (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I wsource))
      G₀ hker₀ hG₀hom hG₀irr hdegree₀ σ
  obtain ⟨hsourceKernel, hGhom, hGirr, hsourceImageDegree⟩ := hsourceKernelData
  rw [← hsourceMapEq] at hsourceKernel hsourceImageDegree
  let G := rename σ.symm G₀
  have hprimitiveKSource :
      IntermediateField.adjoin ℚ
        ((((IsScalarTower.toAlgHom ℚ source (FractionRing source)).comp D.hom).range :
          Set (FractionRing source)) ∪
          {algebraMap source (FractionRing source) (Ideal.Quotient.mk I wsource)}) =
        ⊤ := by
    let B := MvPolynomial (Fin D.parameterCount) ℚ
    letI : Algebra B source := D.hom.toRingHom.toAlgebra
    letI : IsScalarTower ℚ B source :=
      IsScalarTower.of_algebraMap_eq fun k ↦ (D.hom.commutes k).symm
    letI : FaithfulSMul B source :=
      (faithfulSMul_iff_algebraMap_injective B source).mpr D.hom_injective
    letI : Algebra (FractionRing B) (FractionRing source) :=
      FractionRing.liftAlgebra B (FractionRing source)
    letI : IsScalarTower B (FractionRing B) (FractionRing source) :=
      FractionRing.isScalarTower_liftAlgebra B (FractionRing source)
    exact adjoin_groundField_range_union_eq_top_of_fractionField_primitive
      (K := ℚ) (B := B)
      (algebraMap source (FractionRing source) (Ideal.Quotient.mk I wsource))
      hprimitiveSource'
  have hgenerateSourceImage :=
    precomposed_augmentedLinearNormalization_image_adjoin_eq_top
      hI D (Ideal.Quotient.mk I wsource) E hprimitiveKSource
  change IntermediateField.adjoin ℚ
    (((IsScalarTower.toAlgHom ℚ source (FractionRing source)).comp
      (Ideal.kerLiftAlg
        ((augmentedLinearNormalizationHom D (Ideal.Quotient.mk I wsource)).comp
          E.toAlgHom))).range : Set (FractionRing source)) = ⊤ at hgenerateSourceImage
  rw [← hsourceMapEq] at hgenerateSourceImage
  have hsourceFinite : hsourceMap.Finite := by
    rw [hsourceMapEq]
    exact precomposed_augmentedLinearNormalizationHom_finite
      D (Ideal.Quotient.mk I wsource) E
  have hsourceProjection :
      IsAffineChartFiniteBirationalLinearProjection
        (degree := degree) I hI projectionMatrix G := by
    refine ⟨primitiveAffineProjectionMatrix_first_row A₀ c hfirst, ?_⟩
    dsimp only [IsHomogeneousFiniteBirationalLinearProjection]
    refine ⟨?_, hsourceFinite, hsourceKernel, hGhom, hGirr, ?_, ?_⟩
    · intro i
      exact indexedMatrixRowLinearPolynomial_isHomogeneous
        (projectionMatrix.map (Int.castRingHom ℚ)) i
    · letI : (RingHom.ker hsourceMap).IsPrime := RingHom.ker_isPrime hsourceMap
      letI : IsDomain
          (MvPolynomial (Fin (r + 3)) ℚ ⧸ RingHom.ker hsourceMap) :=
        Ideal.Quotient.isDomain _
      exact fractionRing_finrank_eq_one_of_adjoin_range_eq_top_canonical
        (Ideal.kerLiftAlg hsourceMap) (Ideal.kerLiftAlg_injective hsourceMap)
        hgenerateSourceImage
    · intro L _ _ y
      apply homogeneousNormalization_refined_geometric_fibre_finite_ncard_le_degree
        I hI D hdegree hsourceMap
        (E.symm.toAlgHom.comp (mvPolynomialSuccInclusion ℚ D.parameterCount)) _ y
      rw [hsourceMapEq]
      exact precomposed_augmentedLinearNormalizationHom_comp_inclusion
        D (Ideal.Quotient.mk I wsource) E
  have hwhomBoundary : wboundary.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
    intro j _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  obtain ⟨H, hboundaryAugmentedFinite, hboundaryKernel₀, hHhom, hHirr,
      hboundaryImageDegree₀⟩ :=
    augmentedLinearNormalization_exists_kernel_and_exact_image_degree
      J hJprime hJhom Dboundary rfl
      wboundary hwhomBoundary hJdegree.2.1 hminBoundary'
  let boundaryMatrix := simultaneousBoundaryProjectionMatrix A₀Q c
  let boundarySource :=
    MvPolynomial (Fin (N + 1)) ℚ ⧸ J
  let hboundaryMap : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] boundarySource :=
    projectiveMatrixCoordinateMap J boundaryMatrix
  have hboundaryMapEq : hboundaryMap =
      augmentedLinearNormalizationHom Dboundary
        (Ideal.Quotient.mk J wboundary) := by
    simpa [hboundaryMap, boundaryMatrix, Dboundary, wboundary] using
      simultaneousSaturatedBoundaryProjection_coordinateMap_eq_augmented
        I J hIJ A₀Q hfirstQ hfin hJprime hJdegree (Nat.succ_pos r) c
  have hboundaryKernel : RingHom.ker hboundaryMap.toRingHom =
      Ideal.span ({H} : Set (MvPolynomial (Fin (r + 2)) ℚ)) := by
    rw [hboundaryMapEq]
    exact hboundaryKernel₀
  have hboundaryImageDegree :
      HasProjectiveDimensionDegree (RingHom.ker hboundaryMap.toRingHom)
        r degree := by
    rw [hboundaryMapEq]
    exact hboundaryImageDegree₀
  have hprimitiveKBoundary :
      IntermediateField.adjoin ℚ
        ((((IsScalarTower.toAlgHom ℚ boundarySource
          (FractionRing boundarySource)).comp Dboundary.hom).range :
          Set (FractionRing boundarySource)) ∪
          {algebraMap boundarySource (FractionRing boundarySource)
            (Ideal.Quotient.mk J wboundary)}) = ⊤ := by
    let B := MvPolynomial (Fin Dboundary.parameterCount) ℚ
    letI : Algebra B boundarySource := Dboundary.hom.toRingHom.toAlgebra
    letI : IsScalarTower ℚ B boundarySource :=
      IsScalarTower.of_algebraMap_eq fun k ↦ (Dboundary.hom.commutes k).symm
    letI : FaithfulSMul B boundarySource :=
      (faithfulSMul_iff_algebraMap_injective B boundarySource).mpr
        Dboundary.hom_injective
    letI : Algebra (FractionRing B) (FractionRing boundarySource) :=
      FractionRing.liftAlgebra B (FractionRing boundarySource)
    letI : IsScalarTower B (FractionRing B) (FractionRing boundarySource) :=
      FractionRing.isScalarTower_liftAlgebra B (FractionRing boundarySource)
    exact adjoin_groundField_range_union_eq_top_of_fractionField_primitive
      (K := ℚ) (B := B)
      (algebraMap boundarySource (FractionRing boundarySource)
        (Ideal.Quotient.mk J wboundary))
      hprimitiveBoundary'
  have hgenerateBoundaryImage :=
    augmentedLinearNormalization_image_adjoin_eq_top_of_primitive
      hJprime Dboundary
      (Ideal.Quotient.mk J wboundary)
      hprimitiveKBoundary
  change IntermediateField.adjoin ℚ
    (((IsScalarTower.toAlgHom ℚ boundarySource
      (FractionRing boundarySource)).comp
      (Ideal.kerLiftAlg
        (augmentedLinearNormalizationHom Dboundary
          (Ideal.Quotient.mk J wboundary)))).range :
      Set (FractionRing boundarySource)) = ⊤ at hgenerateBoundaryImage
  rw [← hboundaryMapEq] at hgenerateBoundaryImage
  have hboundaryFinite : hboundaryMap.Finite := by
    rw [hboundaryMapEq]
    exact hboundaryAugmentedFinite
  have hboundaryProjection :
      IsHomogeneousFiniteBirationalLinearProjection
        (degree := degree) J hJprime
          boundaryMatrix H := by
    dsimp only [IsHomogeneousFiniteBirationalLinearProjection]
    refine ⟨?_, hboundaryFinite, hboundaryKernel, hHhom, hHirr, ?_, ?_⟩
    · intro i
      exact indexedMatrixRowLinearPolynomial_isHomogeneous boundaryMatrix i
    · letI : (RingHom.ker hboundaryMap).IsPrime :=
        RingHom.ker_isPrime hboundaryMap
      letI : IsDomain
          (MvPolynomial (Fin (r + 2)) ℚ ⧸ RingHom.ker hboundaryMap) :=
        Ideal.Quotient.isDomain _
      exact fractionRing_finrank_eq_one_of_adjoin_range_eq_top_canonical
        (Ideal.kerLiftAlg hboundaryMap) (Ideal.kerLiftAlg_injective hboundaryMap)
        hgenerateBoundaryImage
    · intro L _ _ y
      apply homogeneousNormalization_refined_geometric_fibre_finite_ncard_le_degree
        J hJprime Dboundary hJdegree
        hboundaryMap (mvPolynomialSuccInclusion ℚ Dboundary.parameterCount) _ y
      rw [hboundaryMapEq]
      exact augmentedLinearNormalizationHom_comp_succInclusion Dboundary
        (Ideal.Quotient.mk J wboundary)
  have hmatrixBoundary :
      affineChartProjectionBoundaryMatrix
          (projectionMatrix.map (Int.castRingHom ℚ)) = boundaryMatrix := by
    simpa [projectionMatrix, boundaryMatrix, A₀Q] using
      affineChartProjectionBoundaryMatrix_primitiveAffineProjectionMatrix A₀ c
  refine ⟨projectionMatrix,
    primitiveAffineProjectionMatrix_mem_boundedIntegralSimultaneousAffineProjectionMatrices
      A₀ hA₀ c hc,
    G, H, hsourceProjection, ?_, hsourceImageDegree, ?_⟩
  · rw [hmatrixBoundary]
    exact hboundaryProjection
  · change HasProjectiveDimensionDegree
      (RingHom.ker
        (projectiveMatrixCoordinateMap J
          (affineChartProjectionBoundaryMatrix
            (projectionMatrix.map (Int.castRingHom ℚ)))).toRingHom) r degree
    rw [hmatrixBoundary]
    exact hboundaryImageDegree

end
end TranslatedDepthSeven
