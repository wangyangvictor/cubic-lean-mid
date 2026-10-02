import TranslatedDepthSeven.FiniteRationalSmoothJacobianMenu
import TranslatedDepthSeven.LocalizedJacobianComponentMultiplicityOne
import TranslatedDepthSeven.RankSevenPersistentSurfaceSmoothDevissage
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# A standard-smooth principal neighbourhood of a smooth rational point

Select local equations from any finite generating family using the residual
conormal sequence.  Clear their local equality with the given ideal and
invert the product of that clearing element and the selected Jacobian
minor.  No degree, equidimensionality, or component bound is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

universe u

theorem isStandardSmoothOfRelativeDimension_of_algEquiv
    {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (r : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K A]
    (e : A ≃ₐ[K] B) : Algebra.IsStandardSmoothOfRelativeDimension r K B := by
  have h : RingHom.IsStandardSmoothOfRelativeDimension r
      (algebraMap K A) := by
    simpa only [RingHom.IsStandardSmoothOfRelativeDimension, toAlgebra_algebraMap]
      using (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension r K A)
  have he := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := r)).left
    (algebraMap K A) e.toRingEquiv h
  have heq : e.toRingHom.comp (algebraMap K A) = algebraMap K B := by
    ext k
    exact e.commutes k
  rw [heq] at he
  simpa only [RingHom.IsStandardSmoothOfRelativeDimension, toAlgebra_algebraMap] using he

/-- Local equality with a selected-equation ideal gives a standard-smooth
principal open of the actual quotient, not merely of a containing scheme. -/
theorem local_equations_selectedJacobian_standardSmooth_principalOpen
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K))
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations)) :
    Algebra.IsStandardSmoothOfRelativeDimension (N - c) K
      (Localization.Away (Ideal.Quotient.mk J
        (u * selectedJacobianDeterminant equations cols))) := by
  let R := MvPolynomial (Fin N) K
  let I : Ideal R := Ideal.span (Set.range equations)
  let QI := R ⧸ I
  let QJ := R ⧸ J
  let D := selectedJacobianDeterminant equations cols
  let chartI : QI := Ideal.Quotient.mk I (u * D)
  let chartJ : QJ := Ideal.Quotient.mk J (u * D)
  let T := Localization.Away chartI
  let gR : R →ₐ[K] T := (IsScalarTower.toAlgHom K QI T).comp
    (Ideal.Quotient.mkₐ K I)
  have huT : IsUnit (gR u) := by
    change IsUnit (algebraMap QI T (Ideal.Quotient.mk I u))
    apply IsLocalization.Away.isUnit_of_dvd chartI
    refine ⟨Ideal.Quotient.mk I D, ?_⟩
    exact map_mul (Ideal.Quotient.mk I) u D
  have hJkill : ∀ f ∈ J, gR f = 0 := by
    intro f hf
    have huf : gR (u * f) = 0 := by
      change algebraMap QI T (Ideal.Quotient.mk I (u * f)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hclear f hf), map_zero]
    rw [map_mul] at huf
    exact huT.mul_right_eq_zero.mp huf
  let componentMap : QJ →ₐ[K] T := Ideal.Quotient.liftₐ J gR hJkill
  letI : Algebra QJ T := componentMap.toRingHom.toAlgebra
  letI : IsScalarTower K QJ T :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (componentMap.commutes a).symm
  let factor : QI →ₐ[K] QJ := Ideal.Quotient.factorₐ K hIJ
  have hcompat : (RingHom.id T).comp (algebraMap QI T) =
      (algebraMap QJ T).comp factor.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  have hAwayMapped : IsLocalization
      (Submonoid.map factor.toRingHom (Submonoid.powers chartI)) T :=
    IsLocalization.of_surjective (Submonoid.powers chartI) T factor.toRingHom
      (Ideal.Quotient.factor_surjective hIJ) (RingHom.id T)
      Function.surjective_id hcompat bot_le
  letI : IsLocalization.Away chartJ T := by
    simpa only [Submonoid.map_powers] using hAwayMapped
  let P := equationPreSubmersivePresentation equations cols hcols
  have hchart : chartI = Ideal.Quotient.mk I u * P.jacobian := by
    rw [equationPreSubmersivePresentation_jacobian_eq_mk_selectedJacobian]
    exact map_mul (Ideal.Quotient.mk I) u D
  letI : IsLocalization.Away (Ideal.Quotient.mk I u * P.jacobian) T := by
    rw [← hchart]
    infer_instance
  letI : Algebra.IsStandardSmoothOfRelativeDimension (N - c) K T :=
    finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      equations cols hcols (Ideal.Quotient.mk I u) T
  exact isStandardSmoothOfRelativeDimension_of_algEquiv (N - c)
    ((IsLocalization.algEquiv (Submonoid.powers chartJ) T
      (Localization.Away chartJ)).restrictScalars K)

/-- At a smooth rational point of an arbitrary affine polynomial quotient,
one literal nonvanishing quotient element defines a standard-smooth chart.
The chosen relative dimension is not assumed or identified in advance. -/
theorem exists_standardSmooth_principalOpen_at_smooth_affineRationalPoint
    {K : Type*} [Field K] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (z : Fin N → K)
    (hz : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (hsmooth : IsSmoothAffineIdealRationalPoint J z) :
    ∃ a : MvPolynomial (Fin N) K ⧸ J,
      affineQuotientRationalPoint J z hz a ≠ 0 ∧
      ∃ r : ℕ, Algebra.IsStandardSmoothOfRelativeDimension r K
        (Localization.Away a) := by
  classical
  letI : Algebra.FormallySmooth K (AffineQuotientRationalPointLocalRing J z hz) := by
    obtain ⟨hz', hs⟩ := hsmooth
    exact hs
  let S := AffineQuotientRationalPointLocalRing J z hz
  let s := Module.finrank (IsLocalRing.ResidueField S)
    (IsLocalRing.ResidueField S ⊗[S] KaehlerDifferential K S)
  obtain ⟨n, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian J)
  obtain ⟨rows, cols, _hrows, hcols, hminor, hgenerate⟩ :=
    exists_selected_affineIdeal_generators_and_literal_minor J z hz
      (s := s) rfl F hF
  let equations := fun i ↦ F (rows i)
  let I := Ideal.span (Set.range equations)
  have hIJ : I ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hF]
    exact Ideal.subset_span ⟨rows i, rfl⟩
  have hlocal : Ideal.map (algebraMap (MvPolynomial (Fin N) K)
      (Localization.AtPrime (affineEvaluationPrime z))) I =
      Ideal.map (algebraMap (MvPolynomial (Fin N) K)
        (Localization.AtPrime (affineEvaluationPrime z))) J := by
    rw [← affineQuotientLocalExtension_ker J z hz, ← hgenerate]
    change Ideal.map _ (Ideal.span (Set.range equations)) = _
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨u, hu, hclear, _⟩ :=
    exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq I J
      (affineEvaluationPrime z) hIJ (IsNoetherian.noetherian J) hlocal
  refine ⟨Ideal.Quotient.mk J
    (u * selectedJacobianDeterminant equations cols), ?_,
    N - (N - s), ?_⟩
  · change MvPolynomial.aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hu hminor
  · exact local_equations_selectedJacobian_standardSmooth_principalOpen
      J equations cols hcols u hIJ hclear

end

end TranslatedDepthSeven
