import TranslatedDepthSeven.LocalizedStandardSmoothMultiplicityOne
import TranslatedDepthSeven.LocalizedIdealEquality

/-!
# A locally presented component has multiplicity one at a full-Jacobian point

The equations in a complete-intersection chart need not generate the
component ideal globally.  It is enough to give one literal denominator
`u`: the displayed equations lie in the component ideal, and multiplication
by `u` carries the component ideal back into the equation ideal.  On the
principal open where `u` is nonzero the two ideals therefore agree.

After additionally inverting the displayed full Jacobian minor, the equation
quotient is standard smooth.  The same ring is a principal localization of
the component quotient.  Finite-jet localization then gives the exact
binomial Hilbert--Samuel function at the marked point.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
/-- A literal local complete-intersection presentation and a nonzero full
Jacobian minor imply multiplicity one on the selected component.

`hclear` is the explicit principal-open equality certificate: together with
`hIJ`, it says that the equation ideal and `J₀` become equal after `u` is
inverted.  No smoothness or component-presentation predicate is assumed. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_local_equations_selectedJacobian
    {N c p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p)
    (hP : Published.IsPointOnSpecialFiber
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P))
    (equations : Fin c → MvPolynomial (Fin N) (ZMod p))
    (selectedVar : Fin c → Fin N)
    (hselected : Function.Injective selectedVar)
    (u : MvPolynomial (Fin N) (ZMod p))
    (hIJ : Ideal.span (Set.range equations) ≤
      Published.standardAffineChartIdeal J)
    (hclear : ∀ f ∈ Published.standardAffineChartIdeal J,
      u * f ∈ Ideal.span (Set.range equations))
    (hu : MvPolynomial.aeval (Published.standardAffineChartPoint P) u ≠ 0)
    (hminor : MvPolynomial.aeval (Published.standardAffineChartPoint P)
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    Published.HasHilbertSamuelMultiplicityAt hp J P (N - c) 1 := by
  let R := MvPolynomial (Fin N) (ZMod p)
  let I : Ideal R := Ideal.span (Set.range equations)
  let J₀ : Ideal R := Published.standardAffineChartIdeal J
  let z := Published.standardAffineChartPoint P
  have hz : J₀ ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    change Published.standardAffineChartIdeal J ≤
      RingHom.ker
        (MvPolynomial.aeval (Published.standardAffineChartPoint P)).toRingHom
    simpa [Published.IsPointOnSpecialFiber,
      Published.specialFiberEvaluation, MvPolynomial.aeval_def] using hP
  have hIz : I ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom :=
    hIJ.trans hz
  let QI := R ⧸ I
  let QJ := R ⧸ J₀
  let D := selectedJacobianDeterminant equations selectedVar
  let chartI : QI := Ideal.Quotient.mk I (u * D)
  let chartJ : QJ := Ideal.Quotient.mk J₀ (u * D)
  let T := Localization.Away chartI
  let qI : R →ₐ[ZMod p] QI := Ideal.Quotient.mkₐ (ZMod p) I
  let toT : QI →ₐ[ZMod p] T := IsScalarTower.toAlgHom (ZMod p) QI T
  let gR : R →ₐ[ZMod p] T := toT.comp qI
  have huT : IsUnit (gR u) := by
    change IsUnit (algebraMap QI T (Ideal.Quotient.mk I u))
    apply IsLocalization.Away.isUnit_of_dvd chartI
    refine ⟨Ideal.Quotient.mk I D, ?_⟩
    change Ideal.Quotient.mk I (u * D) =
      Ideal.Quotient.mk I u * Ideal.Quotient.mk I D
    rw [map_mul]
  have hJkill : ∀ f ∈ J₀, gR f = 0 := by
    intro f hf
    have huf : gR (u * f) = 0 := by
      change algebraMap QI T (Ideal.Quotient.mk I (u * f)) = 0
      rw [show Ideal.Quotient.mk I (u * f) = 0 by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hclear f hf), map_zero]
    rw [map_mul] at huf
    exact huT.mul_right_eq_zero.mp huf
  let componentMap : QJ →ₐ[ZMod p] T :=
    Ideal.Quotient.liftₐ J₀ gR hJkill
  letI : Algebra QJ T := componentMap.toRingHom.toAlgebra
  letI : IsScalarTower (ZMod p) QJ T :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (componentMap.commutes a).symm
  let factor : QI →ₐ[ZMod p] QJ :=
    Ideal.Quotient.factorₐ (ZMod p) hIJ
  have hfactorSurj : Function.Surjective factor := by
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I f, rfl⟩
  have hcompat : (RingHom.id T).comp (algebraMap QI T) =
      (algebraMap QJ T).comp factor.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro f
    rfl
  have hAwayMapped :
      IsLocalization (Submonoid.map factor.toRingHom
        (Submonoid.powers chartI)) T :=
    IsLocalization.of_surjective (Submonoid.powers chartI) T
      factor.toRingHom hfactorSurj (RingHom.id T) Function.surjective_id
      hcompat bot_le
  have hfactorChart : factor chartI = chartJ := by
    rfl
  letI : IsLocalization.Away chartJ T := by
    letI : IsLocalization.Away (factor chartI) T := by
      simpa only [Submonoid.map_powers] using hAwayMapped
    exact IsLocalization.Away.of_associated (Associated.of_eq hfactorChart)
  let Ppres := equationPreSubmersivePresentation
    equations selectedVar hselected
  have hchartPresentation : chartI =
      Ideal.Quotient.mk I u * Ppres.jacobian := by
    change Ideal.Quotient.mk I (u * D) =
      Ideal.Quotient.mk I u * Ppres.jacobian
    rw [equationPreSubmersivePresentation_jacobian_eq_mk_selectedJacobian,
      ← map_mul]
  letI : IsLocalization.Away
      (Ideal.Quotient.mk I u * Ppres.jacobian) T := by
    rw [← hchartPresentation]
    infer_instance
  have hsmooth : Algebra.IsStandardSmoothOfRelativeDimension
      (N - c) (ZMod p) T :=
    finEquationQuotient_localizedAt_mul_jacobian_isStandardSmoothOfRelativeDimension
      equations selectedVar hselected (Ideal.Quotient.mk I u) T
  letI : Algebra.IsStandardSmoothOfRelativeDimension
      (N - c) (ZMod p) T := hsmooth
  let pointI : QI →ₐ[ZMod p] ZMod p :=
    affineQuotientRationalPoint I z hIz
  have hchartValue : pointI chartI =
      MvPolynomial.aeval z (u * D) := by
    rfl
  have hchartNonzero : pointI chartI ≠ 0 := by
    rw [hchartValue, map_mul]
    exact mul_ne_zero hu hminor
  have hchartUnit : IsUnit (pointI chartI) :=
    isUnit_iff_ne_zero.mpr hchartNonzero
  have hmapUnits : ∀ y : Submonoid.powers chartI, IsUnit (pointI y) := by
    rintro ⟨y, n, rfl⟩
    simpa only [map_pow] using hchartUnit.pow n
  let point : T →ₐ[ZMod p] ZMod p := IsLocalization.liftAlgHom hmapUnits
  have hpointComponent : point.comp componentMap =
      affineQuotientRationalPoint J₀ z hz := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change point (componentMap (Ideal.Quotient.mk J₀ (MvPolynomial.X i))) =
      MvPolynomial.aeval z (MvPolynomial.X i)
    rw [show componentMap (Ideal.Quotient.mk J₀ (MvPolynomial.X i)) =
      algebraMap QI T (Ideal.Quotient.mk I (MvPolynomial.X i)) by rfl]
    rw [MvPolynomial.aeval_X]
    change (IsLocalization.liftAlgHom hmapUnits)
      (algebraMap QI T (Ideal.Quotient.mk I (MvPolynomial.X i))) = z i
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change affineQuotientRationalPoint I z hIz
      (Ideal.Quotient.mk I (MvPolynomial.X i)) = z i
    rw [affineQuotientRationalPoint_mk, MvPolynomial.aeval_X]
  have hpointPublished : localizationRestrictedPoint (A := QJ) point =
      specialFiberQuotientEvaluationAlgHom J₀ z hz := by
    calc
      localizationRestrictedPoint (A := QJ) point =
          affineQuotientRationalPoint J₀ z hz := hpointComponent
      _ = specialFiberQuotientEvaluationAlgHom J₀ z hz := by rfl
  exact hasHilbertSamuelMultiplicityAt_one_of_localization_isStandardSmooth
    hp J P (N - c) hP chartJ T point hpointPublished

end

end TranslatedDepthSeven
