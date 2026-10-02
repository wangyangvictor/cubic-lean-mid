import TranslatedDepthSeven.ProjectiveBertiniIncidenceIntegral
import TranslatedDepthSeven.ProjectiveBertiniGenericQuotient
import TranslatedDepthSeven.ProjectiveBertiniSmoothGenericField
import TranslatedDepthSeven.AugmentedStandardSmoothGeometricDomainInternal
import TranslatedDepthSeven.AlgebraicallyClosedCoefficientPrime

/-! # Geometric integrality of the generic marked hyperplane quotient

The integral universal incidence and the selected smooth chart use the same
marked point. The actual generic quotient injects into its standard-smooth
principal localization; that localization has the induced rational point.
The existing geometric-domain theorem therefore applies to every further
field extension. No geometric-integrality premise is used.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped TensorProduct
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Use an already supplied standard-smooth principal chart, avoiding a
conversion through the abstract smooth-point predicate. -/
theorem tensorProduct_affineQuotient_isDomain_of_standardSmooth_principalOpen
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    [IsDomain (MvPolynomial (Fin N) K ⧸ I)]
    (z : Fin N → K) (hz : I ≤ RingHom.ker (aeval z).toRingHom)
    (G : MvPolynomial (Fin N) K) (hG : aeval z G ≠ 0) (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K
      (Localization.Away (Ideal.Quotient.mk I G))]
    (E : Type*) [Field E] [Algebra K E] :
    IsDomain (E ⊗[K] (MvPolynomial (Fin N) K ⧸ I)) := by
  let A := MvPolynomial (Fin N) K ⧸ I
  let a : A := Ideal.Quotient.mk I G
  let B := Localization.Away a
  let f := affineQuotientRationalPoint I z hz
  have ha : f a ≠ 0 := by simpa only [f, a, affineQuotientRationalPoint_mk] using hG
  have ha0 : a ≠ 0 := fun h ↦ ha (by simp [h])
  have hM : Submonoid.powers a ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ha0
  letI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  let g : A →ₐ[K] B := IsScalarTower.toAlgHom K A B
  have hg : Function.Injective g := IsLocalization.injective B hM
  let fB : B →ₐ[K] K := IsLocalization.liftAlgHom
    (M := Submonoid.powers a) (f := f) (fun y ↦ by
      obtain ⟨n, hn⟩ := y.property
      apply isUnit_iff_ne_zero.mpr
      change f (y : A) ≠ 0
      rw [← hn, map_pow]
      exact pow_ne_zero n ha)
  exact tensorProduct_isDomain_of_injective_into_standardSmooth_rationalPoint
    g hg fB r E

/-- The actual generic marked hyperplane quotient stays a domain after
every field extension of the generic coefficient field. -/
theorem bertiniGenericMarkedQuotient_tensorProduct_isDomain_of_selectedJacobianChart
    {K L : Type*} [Field K] [Field L] {N c : ℕ}
    [Algebra (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L]
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j k : Fin N) (hjk : j ≠ k)
    (hj : j ∉ Set.range cols) (hk : k ∉ Set.range cols)
    (E : Type*) [Field E] [Algebra L E] :
    IsDomain (E ⊗[L] (MvPolynomial (Fin N) L ⧸
      (J.map (MvPolynomial.map ((algebraMap (MvPolynomial (Fin N) K) L).comp C)) ⊔
        Ideal.span {MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)
          (bertiniGenericMarkedHyperplane z)}))) := by
  let φ := algebraMap (MvPolynomial (Fin N) K) L
  let I := J.map (MvPolynomial.map (φ.comp C)) ⊔
    Ideal.span {MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)}
  letI : IsDomain (BertiniIncidenceRing
      (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i)))) :=
    marked_linear_incidence_isDomain_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk
  letI : IsDomain (MvPolynomial (Fin N) L ⧸ I) :=
    bertiniGenericMarkedQuotient_isDomain L J z hz
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  obtain ⟨G, hzL, hG, hsm⟩ :=
    bertiniGenericMarkedHyperplane_field_standardSmooth_chart φ hφ
      J equations cols hcols u hIJ hclear z hz hminor j hj
  letI : Algebra.IsStandardSmoothOfRelativeDimension (N - (c + 1)) L
      (Localization.Away (Ideal.Quotient.mk I G)) := hsm
  exact tensorProduct_affineQuotient_isDomain_of_standardSmooth_principalOpen
    I (fun i ↦ φ (C (z i))) hzL G hG (N - (c + 1)) E

/-- The same conclusion in literal polynomial coordinates over the further
extension field, with the original ideal and hyperplane maps composed. -/
theorem bertiniGenericMarkedQuotient_extension_isDomain_of_selectedJacobianChart
    {K L : Type*} [Field K] [Field L] {N c : ℕ}
    [Algebra (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L]
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j k : Fin N) (hjk : j ≠ k)
    (hj : j ∉ Set.range cols) (hk : k ∉ Set.range cols)
    (E : Type*) [Field E] [Algebra L E] :
    IsDomain (MvPolynomial (Fin N) E ⧸
      (J.map (MvPolynomial.map ((algebraMap L E).comp
          ((algebraMap (MvPolynomial (Fin N) K) L).comp C))) ⊔
        Ideal.span {MvPolynomial.map
          ((algebraMap L E).comp (algebraMap (MvPolynomial (Fin N) K) L))
          (bertiniGenericMarkedHyperplane z)})) := by
  let φ := algebraMap (MvPolynomial (Fin N) K) L
  let I := J.map (MvPolynomial.map (φ.comp C)) ⊔
    Ideal.span {MvPolynomial.map φ (bertiniGenericMarkedHyperplane z)}
  letI : IsDomain (E ⊗[L] (MvPolynomial (Fin N) L ⧸ I)) :=
    bertiniGenericMarkedQuotient_tensorProduct_isDomain_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk E
  have hmap : I.map (MvPolynomial.map (algebraMap L E)) =
      J.map (MvPolynomial.map ((algebraMap L E).comp (φ.comp C))) ⊔
        Ideal.span {MvPolynomial.map ((algebraMap L E).comp φ)
          (bertiniGenericMarkedHyperplane z)} := by
    simp only [I, Ideal.map_sup, Ideal.map_map, Ideal.map_span,
      Set.image_singleton, MvPolynomial.map_map]
    congr 2
    ext a i <;> simp
  rw [← hmap]
  exact (polynomialQuotientTensorAlgEquiv (L := E) I).toMulEquiv.isDomain _

/-- Select the marked point and all Jacobian data from the original prime
affine ideal. One point works for every generic coefficient field and every
further field extension; callers need not supply a smooth chart. -/
theorem exists_bertiniGenericMarkedQuotient_geometricDomain_of_primeAffine_dimension
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (z : Fin N → K) (_hz : J ≤ RingHom.ker (aeval z).toRingHom),
      ∀ (L : Type*) [Field L] [Algebra (MvPolynomial (Fin N) K) L]
        [IsFractionRing (MvPolynomial (Fin N) K) L]
        (E : Type*) [Field E] [Algebra L E],
      IsDomain (MvPolynomial (Fin N) E ⧸
        (J.map (MvPolynomial.map ((algebraMap L E).comp
            ((algebraMap (MvPolynomial (Fin N) K) L).comp C))) ⊔
          Ideal.span {MvPolynomial.map
            ((algebraMap L E).comp (algebraMap (MvPolynomial (Fin N) K) L))
            (bertiniGenericMarkedHyperplane z)})) := by
  obtain ⟨equations, cols, u, z, j, k, hcols, hjk, hj, hk, hIJ, hclear, hz, hminor⟩ :=
    exists_marked_selectedJacobianChart_two_free_coordinates J hJ hdim hr
  refine ⟨z, hz, ?_⟩
  intro L _ _ _ E _ _
  exact bertiniGenericMarkedQuotient_extension_isDomain_of_selectedJacobianChart (L := L)
    J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk E

/-- Preserve a nonzero marked coordinate difference at the same chosen
point. This supplies noncontainment of the eventual generic linear form. -/
theorem exists_bertiniGenericMarkedQuotient_geometricDomain_nonconstant_of_primeAffine_dimension
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (z : Fin N → K) (_hz : J ≤ RingHom.ker (aeval z).toRingHom),
      (∃ i : Fin N, X i - C (z i) ∉ J) ∧
      ∀ (L : Type*) [Field L] [Algebra (MvPolynomial (Fin N) K) L]
        [IsFractionRing (MvPolynomial (Fin N) K) L]
        (E : Type*) [Field E] [Algebra L E],
      IsDomain (MvPolynomial (Fin N) E ⧸
        (J.map (MvPolynomial.map ((algebraMap L E).comp
            ((algebraMap (MvPolynomial (Fin N) K) L).comp C))) ⊔
          Ideal.span {MvPolynomial.map
            ((algebraMap L E).comp (algebraMap (MvPolynomial (Fin N) K) L))
            (bertiniGenericMarkedHyperplane z)})) := by
  obtain ⟨equations, cols, u, z, j, k, hcols, hjk, hj, hk, hIJ, hclear, hz, hminor⟩ :=
    exists_marked_selectedJacobianChart_two_free_coordinates J hJ hdim hr
  obtain ⟨s, _hs, ha, _hb⟩ :=
    exists_principalOpen_regular_coordinate_pair_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk
  have hjnon : X j - C (z j) ∉ J := by
    intro hjmem
    apply ha
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hjmem, map_zero]
  refine ⟨z, hz, ⟨j, hjnon⟩, ?_⟩
  intro L _ _ _ E _ _
  exact bertiniGenericMarkedQuotient_extension_isDomain_of_selectedJacobianChart (L := L)
    J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk E

end
end TranslatedDepthSeven
