import TranslatedDepthSeven.IntegralCurveStandardSmoothChartInternal
import TranslatedDepthSeven.SmoothRationalPointLocalDomainInternal

/-!
# Coordinate sections of a selected Jacobian chart

Coordinates omitted from a nonsingular Jacobian minor are actual affine
linear parameters. Appending one of their differences to the equations
preserves that minor, and hence gives a marked smooth hyperplane section.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000

/-- Adding a free coordinate difference as the first equation and its
coordinate as the first selected variable preserves the Jacobian minor. -/
theorem selectedJacobianDeterminant_cons_coordinateDifference
    {K : Type*} [CommRing K] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (j : Fin N) (a : K)
    (hj : j ∉ Set.range cols) :
    selectedJacobianDeterminant (Fin.cons (X j - C a) equations) (Fin.cons j cols) =
      selectedJacobianDeterminant equations cols := by
  classical
  have hne (i : Fin c) : cols i ≠ j := by
    intro h
    exact hj ⟨i, h⟩
  unfold selectedJacobianDeterminant
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, pderiv_X, hne, Matrix.submatrix]

/-- Local equations for an affine ideal remain local equations after
adjoining a coordinate difference. The same denominator clears them. -/
theorem coordinateDifference_local_equations
    {K : Type*} [CommRing K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (j : Fin N) (a : K) :
    let J' := J ⊔ Ideal.span {X j - C a}
    let equations' := Fin.cons (X j - C a) equations
    Ideal.span (Set.range equations') ≤ J' ∧
      ∀ f ∈ J', u * f ∈ Ideal.span (Set.range equations') := by
  classical
  dsimp only
  have hspan : Ideal.span (Set.range (Fin.cons (X j - C a) equations)) =
      J ⊓ Ideal.span (Set.range equations) ⊔ Ideal.span {X j - C a} := by
    rw [Fin.range_cons, Ideal.span_insert, inf_eq_right.mpr hIJ, sup_comm]
  rw [hspan, inf_eq_right.mpr hIJ]
  refine ⟨sup_le_sup_right hIJ _, ?_⟩
  intro f hf
  obtain ⟨g, hg, h, hh, rfl⟩ := Submodule.mem_sup.mp hf
  rw [mul_add]
  exact Submodule.mem_sup.mpr ⟨u * g, hclear g hg, u * h,
    (Ideal.span {X j - C a}).mul_mem_left u hh, rfl⟩

/-- On a selected Jacobian principal chart, cutting by a coordinate
omitted from the minor is again standard smooth, of relative dimension
one less. The cut is by a literal affine linear polynomial. -/
theorem coordinateDifference_standardSmooth_principalOpen
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (j : Fin N) (a : K) (hj : j ∉ Set.range cols) :
    Algebra.IsStandardSmoothOfRelativeDimension (N - (c + 1)) K
      (Localization.Away (Ideal.Quotient.mk (J ⊔ Ideal.span {X j - C a})
        (u * selectedJacobianDeterminant equations cols))) := by
  obtain ⟨hIJ', hclear'⟩ :=
    coordinateDifference_local_equations J equations u hIJ hclear j a
  have h := local_equations_selectedJacobian_standardSmooth_principalOpen
    (J ⊔ Ideal.span {X j - C a}) (Fin.cons (X j - C a) equations)
    (Fin.cons j cols) (Fin.cons_injective_of_injective hj hcols) u hIJ' hclear'
  rw [selectedJacobianDeterminant_cons_coordinateDifference equations cols j a hj] at h
  exact h

/-- Evaluation at an affine point extends over every principal open whose
denominator is nonzero at that point. The compatibility is retained. -/
theorem exists_algHom_principalOpen_at_affinePoint
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (G : MvPolynomial (Fin N) K) (hG : aeval z G ≠ 0) :
    ∃ point : Localization.Away (Ideal.Quotient.mk J G) →ₐ[K] K,
      point.comp (IsScalarTower.toAlgHom K (MvPolynomial (Fin N) K ⧸ J)
        (Localization.Away (Ideal.Quotient.mk J G))) =
        affineQuotientRationalPoint J z hz := by
  let Q := MvPolynomial (Fin N) K ⧸ J
  let T := Localization.Away (Ideal.Quotient.mk J G)
  let pointQ : Q →ₐ[K] K := affineQuotientRationalPoint J z hz
  have hunit : IsUnit (pointQ (Ideal.Quotient.mk J G)) :=
    isUnit_iff_ne_zero.mpr hG
  have hmapUnits : ∀ s : Submonoid.powers (Ideal.Quotient.mk J G), IsUnit (pointQ s) := by
    rintro ⟨s, n, rfl⟩
    simpa only [map_pow] using hunit.pow n
  let point : T →ₐ[K] K := IsLocalization.liftAlgHom hmapUnits
  refine ⟨point, ?_⟩
  apply AlgHom.ext
  intro x
  change (IsLocalization.liftAlgHom hmapUnits) (algebraMap Q T x) = pointQ x
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- The marked point lies on every coordinate-difference section. -/
theorem affinePoint_coordinateDifference_ideal_le_ker
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (aeval z).toRingHom) (j : Fin N) :
    J ⊔ Ideal.span {X j - C (z j)} ≤ RingHom.ker (aeval z).toRingHom := by
  refine sup_le hz (Ideal.span_le.mpr ?_)
  intro f hf
  obtain rfl := Set.mem_singleton_iff.mp hf
  change aeval z (X j - C (z j)) = 0
  simp

/-- Cutting a free coordinate through the marked point keeps that point
on a standard-smooth principal chart. -/
theorem coordinateDifference_marked_standardSmooth_principalOpen
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j : Fin N) (hj : j ∉ Set.range cols) :
    let J' := J ⊔ Ideal.span {X j - C (z j)}
    let T := Localization.Away (Ideal.Quotient.mk J'
      (u * selectedJacobianDeterminant equations cols))
    Algebra.IsStandardSmoothOfRelativeDimension (N - (c + 1)) K T ∧
      Nonempty (T →ₐ[K] K) := by
  refine ⟨coordinateDifference_standardSmooth_principalOpen
    J equations cols hcols u hIJ hclear j (z j) hj, ?_⟩
  obtain ⟨point, _hpoint⟩ := exists_algHom_principalOpen_at_affinePoint
    (J ⊔ Ideal.span {X j - C (z j)}) z
    (affinePoint_coordinateDifference_ideal_le_ker J z hz j)
    (u * selectedJacobianDeterminant equations cols) hminor
  exact ⟨point⟩

/-- An integral affine variety of dimension at least two has an explicit
Jacobian chart, a rational point in that chart, and two distinct ambient
coordinates omitted from its selected minor. -/
theorem exists_marked_selectedJacobianChart_two_free_coordinates
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (equations : Fin (N - r) → MvPolynomial (Fin N) K)
      (cols : Fin (N - r) → Fin N) (u : MvPolynomial (Fin N) K)
      (z : Fin N → K) (j k : Fin N),
      Function.Injective cols ∧ j ≠ k ∧ j ∉ Set.range cols ∧ k ∉ Set.range cols ∧
      Ideal.span (Set.range equations) ≤ J ∧
      (∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations)) ∧
      J ≤ RingHom.ker (aeval z).toRingHom ∧
      aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0 := by
  classical
  letI : J.IsPrime := hJ
  obtain ⟨s, hsN, g, hginj, hgfinite, htrdeg⟩ :=
    exists_finite_injective_normalization_of_primeAffine_with_trdeg J
  have hsr : s = r := by
    have h := htrdeg.symm.trans (trdeg_eq_nat_of_primeAffine_ringKrullDim_eq K J hJ hdim)
    exact_mod_cast h
  subst s
  obtain ⟨n, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  obtain ⟨rows, cols, u, _hrows, hcols, hu, hDdvd, hclear, _haway⟩ :=
    exists_genericPrime_principalOpen_selectedJacobianChart J F hF g hginj hgfinite
  let equations := fun i ↦ F (rows i)
  let D := selectedJacobianDeterminant equations cols
  have hDnot : D ∉ J := by
    intro hD
    obtain ⟨b, hb⟩ := hDdvd
    apply hu
    rw [hb]
    exact J.mul_mem_right b hD
  have hproduct : u * D ∉ J := hJ.mul_notMem hu hDnot
  have hIJ : Ideal.span (Set.range equations) ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hF.le (Ideal.subset_span ⟨rows i, rfl⟩)
  have hex : ∃ z : Fin N → K, z ∈ zeroLocus K J ∧ aeval z (u * D) ≠ 0 := by
    by_contra h
    have hvanish : u * D ∈ vanishingIdeal K (zeroLocus K J) := by
      intro z hz
      by_contra hne
      exact h ⟨z, hz, hne⟩
    rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hvanish
    exact hproduct hvanish
  obtain ⟨z, hz, hpoint⟩ := hex
  have hcard : ((Finset.univ.image cols)ᶜ : Finset (Fin N)).card = r := by
    rw [Finset.card_compl, Finset.card_image_of_injective _ hcols]
    simp only [Fintype.card_fin, Finset.card_univ]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (show
      1 < ((Finset.univ.image cols)ᶜ : Finset (Fin N)).card by omega)
  have hj' : j ∉ Set.range cols := by simpa using hj
  have hk' : k ∉ Set.range cols := by simpa using hk
  exact ⟨equations, cols, u, z, j, k, hcols, hjk, hj', hk', hIJ, hclear, hz, hpoint⟩

end
end TranslatedDepthSeven
