import TranslatedDepthSeven.ProjectiveBertiniSmoothCoordinateSection
import TranslatedDepthSeven.StandardSmoothChartLocalRingInternal

/-!
# Free coordinates remain nonzero in the marked local ring

The first jet of a smooth coordinate section has one fewer dimension.
Consequently the cutting coordinate cannot belong to the square of the
point ideal, even modulo the original equations. This certifies that it
cannot be annihilated by a denominator nonzero at the marked point.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- The first-jet comparison is made in the original affine polynomial
ring, retaining the literal ideal of the marked point. -/
noncomputable def affineQuotientPointAugmentedJetAlgEquiv
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom) (k : ℕ) :
    augmentedJet (affineQuotientRationalPoint J z hz) k ≃ₐ[K]
      MvPolynomial (Fin N) K ⧸ (J ⊔ RingHom.ker (aeval z).toRingHom ^ (k + 1)) := by
  let M : Ideal (MvPolynomial (Fin N) K) := RingHom.ker (aeval z).toRingHom
  let q := Ideal.Quotient.mkₐ K J
  have hm : RingHom.ker (affineQuotientRationalPoint J z hz).toRingHom = M.map q := by
    simpa [affineQuotientRationalPoint, M, q] using
      (Ideal.ker_quotient_lift (I := J)
        (aeval z : MvPolynomial (Fin N) K →ₐ[K] K).toRingHom hz)
  have hpow : RingHom.ker (affineQuotientRationalPoint J z hz).toRingHom ^ (k + 1) =
      (M ^ (k + 1)).map q := by
    rw [hm, Ideal.map_pow]
  exact (Ideal.quotientEquivAlgOfEq K hpow).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ K J (M ^ (k + 1)))

/-- A marked smooth principal chart computes the first jet already in
the original affine polynomial ring. -/
theorem finrank_affinePointFirstJet_of_principalOpen_standardSmooth
    {K : Type*} [Field K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (G : MvPolynomial (Fin N) K) (hG : aeval z G ≠ 0)
    (hstandard : Algebra.IsStandardSmoothOfRelativeDimension r K
      (Localization.Away (Ideal.Quotient.mk J G))) :
    Module.finrank K (MvPolynomial (Fin N) K ⧸
      (J ⊔ RingHom.ker (aeval z).toRingHom ^ 2)) = r + 1 := by
  letI := hstandard
  obtain ⟨point, hpoint⟩ := exists_algHom_principalOpen_at_affinePoint J z hz G hG
  let eQ := affineQuotientPointAugmentedJetAlgEquiv J z hz 1
  let eL := localizationAugmentedJetAlgEquiv (Ideal.Quotient.mk J G) point 1
  have hL := eL.toLinearEquiv.finrank_eq
  change Module.finrank K (augmentedJet
      (point.comp (IsScalarTower.toAlgHom K (MvPolynomial (Fin N) K ⧸ J)
        (Localization.Away (Ideal.Quotient.mk J G)))) 1) =
    Module.finrank K (augmentedJet point 1) at hL
  rw [hpoint] at hL
  have hrank := finrank_firstJet_eq_add_one_of_isStandardSmoothOfRelativeDimension point r
  exact eQ.toLinearEquiv.finrank_eq.symm.trans (hL.trans hrank)

/-- An omitted coordinate has nonzero first-order class at the marked
point. Its vanishing section has a first jet of strictly smaller dimension. -/
theorem coordinateDifference_not_mem_point_square_mod_ideal
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j : Fin N) (hj : j ∉ Set.range cols) (hc : c < N) :
    X j - C (z j) ∉ J ⊔ RingHom.ker (aeval z).toRingHom ^ 2 := by
  intro hmem
  let M : Ideal (MvPolynomial (Fin N) K) := RingHom.ker (aeval z).toRingHom
  have heq : (J ⊔ Ideal.span {X j - C (z j)}) ⊔ M ^ 2 = J ⊔ M ^ 2 := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (Ideal.span_le.mpr (by simpa using hmem)))
        le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hfirst := finrank_affinePointFirstJet_of_principalOpen_standardSmooth
    J z hz (u * selectedJacobianDeterminant equations cols) hminor
    (local_equations_selectedJacobian_standardSmooth_principalOpen
      J equations cols hcols u hIJ hclear)
  have hsecond := finrank_affinePointFirstJet_of_principalOpen_standardSmooth
    (J ⊔ Ideal.span {X j - C (z j)}) z
    (affinePoint_coordinateDifference_ideal_le_ker J z hz j)
    (u * selectedJacobianDeterminant equations cols) hminor
    (coordinateDifference_standardSmooth_principalOpen
      J equations cols hcols u hIJ hclear j (z j) hj)
  change Module.finrank K (MvPolynomial (Fin N) K ⧸
    ((J ⊔ Ideal.span {X j - C (z j)}) ⊔ M ^ 2)) = N - (c + 1) + 1 at hsecond
  change Module.finrank K (MvPolynomial (Fin N) K ⧸
    (J ⊔ M ^ 2)) = N - c + 1 at hfirst
  rw [heq] at hsecond
  rw [hfirst] at hsecond
  omega

/-- No polynomial nonzero at the marked point can annihilate a free
coordinate modulo the affine equations. This is a literal denominator
criterion for nonvanishing in the marked local ring. -/
theorem coordinateDifference_mul_not_mem_of_eval_ne_zero
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j : Fin N) (hj : j ∉ Set.range cols) (hc : c < N)
    (s : MvPolynomial (Fin N) K) (hs : aeval z s ≠ 0) :
    s * (X j - C (z j)) ∉ J := by
  intro hmul
  let M : Ideal (MvPolynomial (Fin N) K) := RingHom.ker (aeval z).toRingHom
  let I := J ⊔ M ^ 2
  have hbM : X j - C (z j) ∈ M := by
    change aeval z (X j - C (z j)) = 0
    simp
  have hsM : s - C (aeval z s) ∈ M := by
    change aeval z (s - C (aeval z s)) = 0
    simp
  have hprod : (s - C (aeval z s)) * (X j - C (z j)) ∈ I := by
    apply (show M ^ 2 ≤ I from le_sup_right)
    simpa only [pow_two] using Ideal.mul_mem_mul hsM hbM
  have hsmul : C (aeval z s) * (X j - C (z j)) ∈ I := by
    have := I.sub_mem ((show J ≤ I from le_sup_left) hmul) hprod
    convert this using 1
    ring
  have hunit : IsUnit (C (aeval z s) : MvPolynomial (Fin N) K) :=
    (isUnit_iff_ne_zero.mpr hs).map C
  have hb : X j - C (z j) ∈ I := (Ideal.unit_mul_mem_iff_mem I hunit).mp hsmul
  exact coordinateDifference_not_mem_point_square_mod_ideal
    J equations cols hcols u hIJ hclear z hz hminor j hj hc hb

/-- The marked local ring beneath the selected chart is a domain. This
applies equally to the original affine ideal and to its coordinate cuts. -/
theorem isDomain_pointLocalization_of_selectedJacobianChart
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (M : Ideal (MvPolynomial (Fin N) K ⧸ J)) [M.IsPrime]
    (hM : M = RingHom.ker (affineQuotientRationalPoint J z hz).toRingHom) :
    IsDomain (Localization.AtPrime M) := by
  letI := local_equations_selectedJacobian_standardSmooth_principalOpen
    J equations cols hcols u hIJ hclear
  obtain ⟨point, hpoint⟩ := exists_algHom_principalOpen_at_affinePoint J z hz
    (u * selectedJacobianDeterminant equations cols) hminor
  have hM' : M = RingHom.ker (point.comp (IsScalarTower.toAlgHom K
      (MvPolynomial (Fin N) K ⧸ J)
      (Localization.Away (Ideal.Quotient.mk J
        (u * selectedJacobianDeterminant equations cols))))).toRingHom := by
    rw [hpoint]
    exact hM
  exact (localRing_of_standardSmooth_localizationChart
    (Submonoid.powers (Ideal.Quotient.mk J
      (u * selectedJacobianDeterminant equations cols))) point (N - c) M hM').1

/-- An omitted coordinate difference is nonzero in the actual local
ring at the marked point, including after any earlier coordinate cut. -/
theorem coordinateDifference_ne_zero_pointLocalization
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j : Fin N) (hj : j ∉ Set.range cols) (hc : c < N)
    (M : Ideal (MvPolynomial (Fin N) K ⧸ J)) [M.IsPrime]
    (hM : M = RingHom.ker (affineQuotientRationalPoint J z hz).toRingHom) :
    algebraMap (MvPolynomial (Fin N) K ⧸ J) (Localization.AtPrime M)
      (Ideal.Quotient.mk J (X j - C (z j))) ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl
    (Localization.AtPrime M) (Ideal.Quotient.mk J (X j - C (z j)))).mp hzero
  obtain ⟨S, hS⟩ := Ideal.Quotient.mk_surjective (s : MvPolynomial (Fin N) K ⧸ J)
  have hSz : aeval z S ≠ 0 := by
    intro h
    apply s.property
    apply hM.ge
    change affineQuotientRationalPoint J z hz (s : MvPolynomial (Fin N) K ⧸ J) = 0
    rw [← hS]
    exact h
  apply coordinateDifference_mul_not_mem_of_eval_ne_zero
    J equations cols hcols u hIJ hclear z hz hminor j hj hc S hSz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_mul, hS]
  exact hs

end
end TranslatedDepthSeven
