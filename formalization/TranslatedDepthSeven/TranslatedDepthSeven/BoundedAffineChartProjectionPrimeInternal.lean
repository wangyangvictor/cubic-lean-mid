import TranslatedDepthSeven.BoundedAffineChartProjectionInternal

/-!
# Prime-only bounded affine-chart projections

The internal BHB--Marmon construction in
`BoundedAffineChartProjectionInternal` never uses geometric primality.  This
file exposes that exact stronger theorem.  It is useful for a projective
closure constructed from a prime affine ideal: geometric primality of the
closure is irrelevant to the linear normalization, primitive-element,
finite-fibre, and exact-degree arguments.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Matrix Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 600000

namespace StandardAG

/-- Prime-only version of the bounded integral affine-chart projection
menu.  This is the actual hypothesis list used by the internal proof. -/
def BoundedDegreeAffineChartProjectionMenuPrime : Prop :=
  ∀ (N r degreeBound : ℕ), r < N →
    ∃ menu : Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ),
      ∀ (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
        (hI : I.IsPrime),
        I.IsHomogeneous
          (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) →
        MvPolynomial.X (0 : Fin (N + 1)) ∉ I →
        ∀ degree : ℕ,
          HasProjectiveDimensionDegree I r degree →
          degree ≤ degreeBound →
            ∃ A ∈ menu, ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
              IsAffineChartFiniteBirationalLinearProjection
                (degree := degree) I hI A G ∧
              HasProjectiveDimensionDegree
                (RingHom.ker
                  (projectiveMatrixCoordinateMap I
                    (A.map (Int.castRingHom ℚ))).toRingHom)
                r degree

end StandardAG

/-- The bounded BHB--Marmon affine-chart projection, with exactly the
prime/homogeneous/chart/dimension-degree assumptions used in its proof. -/
theorem exists_mem_boundedIntegralAffineProjectionMatrices
    (N r dmax : ℕ) (_hr : r < N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hX : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (d : ℕ) (hdegree : HasProjectiveDimensionDegree I r d)
    (hdmax : d ≤ dmax) :
    ∃ A ∈ boundedIntegralAffineProjectionMatrices N r dmax,
      ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
        IsAffineChartFiniteBirationalLinearProjection
          (degree := d) I hI A G ∧
        HasProjectiveDimensionDegree
          (RingHom.ker (projectiveMatrixCoordinateMap I
            (A.map (Int.castRingHom ℚ))).toRingHom) r d := by
  classical
  letI : I.IsPrime := hI
  obtain ⟨A, hA, hfirst, hinj, hfin⟩ :=
    exists_mem_boundedIntegralDistinguishedNormalizationMatrices
      N I hI hhom hX hdegree hdmax
  let D := homogeneousLinearNormalizationDataOfIntegralMatrix I A hinj hfin
  obtain ⟨c, hc, hminpoly, hprimitive⟩ :=
    exists_bounded_primitive_linearNormalization_coordinate I hhom D hdegree hdmax
  let w : MvPolynomial (Fin (N + 1)) ℚ := ∑ i, C (c i : ℚ) * X i
  have hwhom : w.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _
  obtain ⟨G₀, _hfinite₀, hker₀, hG₀hom, hG₀irr, hdegree₀⟩ :=
    augmentedLinearNormalization_exists_kernel_and_exact_image_degree
      I hI hhom D rfl w hwhom hdegree.2.1 hminpoly
  let σ := Equiv.swap (0 : Fin (r + 2)) 1
  let E := MvPolynomial.renameEquiv ℚ σ
  let projectionMatrix := primitiveAffineProjectionMatrix A c
  let source := MvPolynomial (Fin (N + 1)) ℚ ⧸ I
  let h : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] source :=
    projectiveMatrixCoordinateMap I (projectionMatrix.map (Int.castRingHom ℚ))
  have hmap : h = (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).comp
      E.toAlgHom := primitiveAffineProjectionMatrix_coordinateMap_eq_augmented I A hinj hfin c
  have hnew := principal_kernel_and_projectiveDegree_precomp_rename
    (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w))
    G₀ hker₀ hG₀hom hG₀irr hdegree₀ σ
  obtain ⟨hker, hGhom, hGirr, hGdegree⟩ := hnew
  rw [← hmap] at hker hGdegree
  let G := rename σ.symm G₀
  have hprimitiveK :
      IntermediateField.adjoin ℚ
        ((((IsScalarTower.toAlgHom ℚ source (FractionRing source)).comp D.hom).range :
          Set (FractionRing source)) ∪
          {algebraMap source (FractionRing source) (Ideal.Quotient.mk I w)}) = ⊤ := by
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
      (K := ℚ) (B := B) (algebraMap source (FractionRing source) (Ideal.Quotient.mk I w))
      hprimitive
  have hgenerate := precomposed_augmentedLinearNormalization_image_adjoin_eq_top
    hI D (Ideal.Quotient.mk I w) E hprimitiveK
  change IntermediateField.adjoin ℚ
    (((IsScalarTower.toAlgHom ℚ source (FractionRing source)).comp
      (Ideal.kerLiftAlg ((augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).comp
        E.toAlgHom))).range : Set (FractionRing source)) = ⊤ at hgenerate
  rw [← hmap] at hgenerate
  have hfinite : h.Finite := by
    rw [hmap]
    exact precomposed_augmentedLinearNormalizationHom_finite D (Ideal.Quotient.mk I w) E
  refine ⟨projectionMatrix,
    primitiveAffineProjectionMatrix_mem_boundedIntegralAffineProjectionMatrices A hA c hc,
    G, ⟨primitiveAffineProjectionMatrix_first_row A c hfirst, ?_⟩, hGdegree⟩
  dsimp only [IsHomogeneousFiniteBirationalLinearProjection]
  refine ⟨?_, hfinite, hker, hGhom, hGirr, ?_, ?_⟩
  · intro i
    exact indexedMatrixRowLinearPolynomial_isHomogeneous
      (projectionMatrix.map (Int.castRingHom ℚ)) i
  · letI : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
    letI : IsDomain (MvPolynomial (Fin (r + 2)) ℚ ⧸ RingHom.ker h) :=
      Ideal.Quotient.isDomain _
    exact fractionRing_finrank_eq_one_of_adjoin_range_eq_top_canonical
      (Ideal.kerLiftAlg h) (Ideal.kerLiftAlg_injective h) hgenerate
  · intro L _ _ y
    apply homogeneousNormalization_refined_geometric_fibre_finite_ncard_le_degree
      I hI D hdegree h (E.symm.toAlgHom.comp
        (mvPolynomialSuccInclusion ℚ D.parameterCount)) _ y
    rw [hmap]
    exact precomposed_augmentedLinearNormalizationHom_comp_inclusion
      D (Ideal.Quotient.mk I w) E

/-- The existential menu interface, supplied by the explicit coefficient
box of the constructive internal projection theorem. -/
theorem boundedDegreeAffineChartProjectionMenuPrime_internal :
    StandardAG.BoundedDegreeAffineChartProjectionMenuPrime := by
  intro N r dmax hr
  exact ⟨boundedIntegralAffineProjectionMatrices N r dmax,
    exists_mem_boundedIntegralAffineProjectionMatrices N r dmax hr⟩

/-- A fixed finite prime-only affine-chart projection menu.  It depends
only on the ambient dimension, source dimension and degree bound. -/
def boundedDegreeAffineChartProjectionPrimeMenu
    (N r degreeBound : ℕ) (hr : r < N) :
    Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) :=
  Classical.choose
    (boundedDegreeAffineChartProjectionMenuPrime_internal N r degreeBound hr)

/-- Every integral homogeneous source of bounded degree admits a
BHB--Marmon projection from the fixed prime-only menu. -/
theorem exists_mem_boundedDegreeAffineChartProjectionPrimeMenu
    (N r degreeBound : ℕ) (hr : r < N)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime)
    (hhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hX : MvPolynomial.X (0 : Fin (N + 1)) ∉ I)
    (degree : ℕ)
    (hdegree : HasProjectiveDimensionDegree I r degree)
    (hle : degree ≤ degreeBound) :
    ∃ A ∈ boundedDegreeAffineChartProjectionPrimeMenu
        N r degreeBound hr,
      ∃ G : MvPolynomial (Fin (r + 2)) ℚ,
        StandardAG.IsAffineChartFiniteBirationalLinearProjection
          (degree := degree) I hI A G ∧
        HasProjectiveDimensionDegree
          (RingHom.ker
            (projectiveMatrixCoordinateMap I
              (A.map (Int.castRingHom ℚ))).toRingHom)
          r degree := by
  exact Classical.choose_spec
    (boundedDegreeAffineChartProjectionMenuPrime_internal N r degreeBound hr)
      I hI hhom hX degree hdegree hle

end

end TranslatedDepthSeven
