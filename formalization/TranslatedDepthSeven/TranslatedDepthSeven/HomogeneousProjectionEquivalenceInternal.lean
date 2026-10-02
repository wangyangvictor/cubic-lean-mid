import TranslatedDepthSeven.AffineChartProjectionMenu

/-!
# Invariance of the complete projection contract under source isomorphism

The image equation is unchanged.  Finiteness is transported by composition,
the image ideals are literally equal, the fraction fields form a commuting
square, and every geometric fibre is carried bijectively to the old fibre.
No degree or counting bound is introduced as a new premise.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial StandardAG

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- A commuting square of domain isomorphisms preserves the degree of the
induced extension of fraction fields. -/
theorem fractionRing_finrank_eq_of_commuting_ringEquivs
    {R₀ S₀ R₁ S₁ : Type*}
    [CommRing R₀] [IsDomain R₀] [CommRing S₀] [IsDomain S₀]
    [CommRing R₁] [IsDomain R₁] [CommRing S₁] [IsDomain S₁]
    [Algebra R₀ S₀] [NoZeroSMulDivisors R₀ S₀]
    [Algebra R₁ S₁] [NoZeroSMulDivisors R₁ S₁]
    (eR : R₀ ≃+* R₁) (eS : S₀ ≃+* S₁)
    (hcommute : ∀ x, eS (algebraMap R₀ S₀ x) = algebraMap R₁ S₁ (eR x)) :
    letI : Algebra (FractionRing R₀) (FractionRing S₀) :=
      FractionRing.liftAlgebra R₀ (FractionRing S₀)
    letI : Algebra (FractionRing R₁) (FractionRing S₁) :=
      FractionRing.liftAlgebra R₁ (FractionRing S₁)
    Module.finrank (FractionRing R₀) (FractionRing S₀) =
      Module.finrank (FractionRing R₁) (FractionRing S₁) := by
  letI : Algebra (FractionRing R₀) (FractionRing S₀) :=
    FractionRing.liftAlgebra R₀ (FractionRing S₀)
  letI : Algebra (FractionRing R₁) (FractionRing S₁) :=
    FractionRing.liftAlgebra R₁ (FractionRing S₁)
  apply Algebra.finrank_eq_of_equiv_equiv
    (IsFractionRing.ringEquivOfRingEquiv eR)
    (IsFractionRing.ringEquivOfRingEquiv eS)
  ext x
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (A := R₀) x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_div₀,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [← IsScalarTower.algebraMap_apply R₀ (FractionRing R₀) (FractionRing S₀),
    ← IsScalarTower.algebraMap_apply R₁ (FractionRing R₁) (FractionRing S₁)]
  simp only [IsScalarTower.algebraMap_apply R₀ S₀ (FractionRing S₀),
    IsScalarTower.algebraMap_apply R₁ S₁ (FractionRing S₁),
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, hcommute]

/-- Precomposing geometric points with a source isomorphism gives exact
equality of fibres, as finite sets with their cardinalities. -/
theorem algHom_fibre_finite_ncard_of_source_equiv
    {K R S T L : Type*} [CommRing K] [CommRing R]
    [CommRing S] [CommRing T] [CommRing L]
    [Algebra K R] [Algebra K S] [Algebra K T] [Algebra K L]
    (h : R →ₐ[K] S) (h' : R →ₐ[K] T) (E : S ≃ₐ[K] T)
    (hc : E.toAlgHom.comp h = h') (y : R →ₐ[K] L)
    (d : ℕ)
    (hf : Set.Finite {z : S →ₐ[K] L | z.comp h = y} ∧
      Set.ncard {z : S →ₐ[K] L | z.comp h = y} ≤ d) :
    Set.Finite {z : T →ₐ[K] L | z.comp h' = y} ∧
      Set.ncard {z : T →ₐ[K] L | z.comp h' = y} ≤ d := by
  let e := AlgEquiv.arrowCongr E (AlgEquiv.refl : L ≃ₐ[K] L)
  have hset : {z : T →ₐ[K] L | z.comp h' = y} =
      e '' {z : S →ₐ[K] L | z.comp h = y} := by
    ext z
    constructor
    · intro hz
      refine ⟨z.comp E.toAlgHom, ?_, ?_⟩
      · change (z.comp E.toAlgHom).comp h = y
        rw [AlgHom.comp_assoc, hc]
        exact hz
      · ext a
        change z (E (E.symm a)) = z a
        rw [E.apply_symm_apply]
    · rintro ⟨z, hz, rfl⟩
      change (z.comp E.symm.toAlgHom).comp h' = y
      have hback : E.symm.toAlgHom.comp h' = h := by
        ext f
        change E.symm (h' f) = h f
        rw [← AlgHom.congr_fun hc f]
        exact E.symm_apply_apply _
      rw [AlgHom.comp_assoc, hback]
      exact hz
  rw [hset]
  exact ⟨hf.1.image e, by rw [Set.ncard_image_of_injective _ e.injective]; exact hf.2⟩

/-- The complete homogeneous projection condition is invariant under an
isomorphism of the source coordinate rings which commutes with the literal
matrix coordinate maps. -/
theorem isHomogeneousFiniteBirationalLinearProjection_of_source_equiv
    {N r d : ℕ}
    (I J : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : I.IsPrime) (hJ : J.IsPrime)
    (A B : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (E : (MvPolynomial (Fin (N + 1)) ℚ ⧸ I) ≃ₐ[ℚ]
      (MvPolynomial (Fin (N + 1)) ℚ ⧸ J))
    (hc : E.toAlgHom.comp (projectiveMatrixCoordinateMap I A) =
      projectiveMatrixCoordinateMap J B)
    (hp : IsHomogeneousFiniteBirationalLinearProjection
      (degree := d) I hI A G) :
    IsHomogeneousFiniteBirationalLinearProjection
      (degree := d) J hJ B G := by
  letI : I.IsPrime := hI
  letI : J.IsPrime := hJ
  let S := MvPolynomial (Fin (N + 1)) ℚ ⧸ I
  let T := MvPolynomial (Fin (N + 1)) ℚ ⧸ J
  let h : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] S :=
    projectiveMatrixCoordinateMap I A
  let h' : MvPolynomial (Fin (r + 2)) ℚ →ₐ[ℚ] T :=
    projectiveMatrixCoordinateMap J B
  let K₀ := RingHom.ker h.toRingHom
  let K₁ := RingHom.ker h'.toRingHom
  have hker : K₀ = K₁ := by
    ext f
    change h f = 0 ↔ h' f = 0
    have hcf : E (h f) = h' f := AlgHom.congr_fun hc f
    rw [← hcf]
    exact (map_eq_zero_iff E E.injective).symm
  letI : K₀.IsPrime := RingHom.ker_isPrime h.toRingHom
  letI : K₁.IsPrime := RingHom.ker_isPrime h'.toRingHom
  let R₀ := MvPolynomial (Fin (r + 2)) ℚ ⧸ K₀
  let R₁ := MvPolynomial (Fin (r + 2)) ℚ ⧸ K₁
  let eR : R₀ ≃ₐ[ℚ] R₁ := Ideal.quotientEquivAlgOfEq ℚ hker
  letI : Algebra R₀ S := (Ideal.kerLiftAlg h).toRingHom.toAlgebra
  letI : Algebra R₁ T := (Ideal.kerLiftAlg h').toRingHom.toAlgebra
  letI : NoZeroSMulDivisors R₀ S :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (Ideal.kerLiftAlg_injective h)
  letI : NoZeroSMulDivisors R₁ T :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (Ideal.kerLiftAlg_injective h')
  letI : Algebra (FractionRing R₀) (FractionRing S) :=
    FractionRing.liftAlgebra R₀ (FractionRing S)
  letI : Algebra (FractionRing R₁) (FractionRing T) :=
    FractionRing.liftAlgebra R₁ (FractionRing T)
  have hcompat (x : R₀) : E (algebraMap R₀ S x) = algebraMap R₁ T (eR x) := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change E (h f) = h' f
    exact AlgHom.congr_fun hc f
  have hdegree : Module.finrank (FractionRing R₀) (FractionRing S) =
      Module.finrank (FractionRing R₁) (FractionRing T) :=
    fractionRing_finrank_eq_of_commuting_ringEquivs eR.toRingEquiv E.toRingEquiv hcompat
  dsimp only [IsHomogeneousFiniteBirationalLinearProjection] at hp ⊢
  refine ⟨?_, ?_, ?_, hp.2.2.2.1, hp.2.2.2.2.1, ?_, ?_⟩
  · intro i
    exact IsHomogeneous.sum Finset.univ _ _
      (fun j _ ↦ isHomogeneous_C_mul_X (B i j) j)
  · rw [← hc]
    exact AlgHom.Finite.comp
      (AlgHom.Finite.of_surjective E.toAlgHom E.surjective) hp.2.1
  · change K₁ = Ideal.span {G}
    rw [← hker]
    exact hp.2.2.1
  · exact hdegree ▸ hp.2.2.2.2.2.1
  · intro L _ _ y
    exact algHom_fibre_finite_ncard_of_source_equiv h h' E hc y d
      (hp.2.2.2.2.2.2 L y)

end

end TranslatedDepthSeven
