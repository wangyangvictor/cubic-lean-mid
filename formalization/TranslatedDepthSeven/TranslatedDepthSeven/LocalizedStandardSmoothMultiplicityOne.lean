import TranslatedDepthSeven.AugmentedJetLocalization
import TranslatedDepthSeven.JacobianMinorStandardSmoothChart

/-!
# Multiplicity one from a standard-smooth principal neighbourhood

Hilbert--Samuel jets only see a neighbourhood of their marked point.  This
file combines the explicit finite-jet localization equivalence with the
standard-smooth jet calculation.  It then applies the result to the literal
selected-Jacobian principal open of a displayed affine equation family.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

variable {K : Type u} [Field K]
variable {A : Type v} {T : Type w}
variable [CommRing A] [CommRing T]
variable [Algebra K A] [Algebra A T] [Algebra K T]
variable [IsScalarTower K A T]

/-- Finite-dimensionality of a jet may be checked on any standard-smooth
principal neighbourhood containing the point. -/
theorem augmentedJet_moduleFinite_of_localization_isStandardSmooth
    (s : A) [IsLocalization.Away s T]
    (x : T →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K T] :
    Module.Finite K
      (augmentedJet (localizationRestrictedPoint (A := A) x) k) := by
  letI : Module.Finite K (augmentedJet x k) :=
    augmentedJet_moduleFinite_of_isStandardSmoothOfRelativeDimension x r k
  exact Module.Finite.equiv
    (localizationAugmentedJetAlgEquiv s x k).symm.toLinearEquiv

/-- Exact binomial jet length may be checked on any standard-smooth
principal neighbourhood containing the point. -/
theorem finrank_augmentedJet_eq_choose_of_localization_isStandardSmooth
    (s : A) [IsLocalization.Away s T]
    (x : T →ₐ[K] K) (r k : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension r K T] :
    Module.finrank K
        (augmentedJet (localizationRestrictedPoint (A := A) x) k) =
      (k + r).choose r := by
  rw [(localizationAugmentedJetAlgEquiv s x k).toLinearEquiv.finrank_eq]
  exact finrank_augmentedJet_eq_choose_of_isStandardSmoothOfRelativeDimension
    x r k

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
/-- A standard-smooth principal neighbourhood of the displayed affine-chart
point implies multiplicity one in the literal published definition. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_localization_isStandardSmooth
    {N p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p) (r : ℕ)
    (hP : Published.IsPointOnSpecialFiber
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P))
    (s : HasQuotient.Quotient (MvPolynomial (Fin N) (ZMod p))
      (Published.standardAffineChartIdeal J))
    (T : Type w) [CommRing T]
    [Algebra
      (HasQuotient.Quotient (MvPolynomial (Fin N) (ZMod p))
        (Published.standardAffineChartIdeal J)) T]
    [Algebra (ZMod p) T]
    [IsScalarTower (ZMod p)
      (HasQuotient.Quotient (MvPolynomial (Fin N) (ZMod p))
        (Published.standardAffineChartIdeal J)) T]
    [IsLocalization.Away s T]
    (x : T →ₐ[ZMod p] ZMod p)
    (hx : localizationRestrictedPoint
        (A := HasQuotient.Quotient (MvPolynomial (Fin N) (ZMod p))
          (Published.standardAffineChartIdeal J)) x =
      specialFiberQuotientEvaluationAlgHom
        (Published.standardAffineChartIdeal J)
        (Published.standardAffineChartPoint P) hP)
    [Algebra.IsStandardSmoothOfRelativeDimension r (ZMod p) T] :
    Published.HasHilbertSamuelMultiplicityAt hp J P r 1 := by
  apply hasHilbertSamuelMultiplicityAt_one_of_finrank_specialFiberJetSpace_eq_choose
    hp J P r hP
  · intro k
    let E := specialFiberPointPowerQuotientAlgEquivJetSpace
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P) hP k
    letI : Module.Finite (ZMod p)
        ((MvPolynomial (Fin N) (ZMod p) ⧸
          Published.standardAffineChartIdeal J) ⧸
            Published.specialFiberPointIdeal
              (Published.standardAffineChartIdeal J)
              (Published.standardAffineChartPoint P) hP ^ (k + 1)) := by
      change Module.Finite (ZMod p)
        (augmentedJet
          (specialFiberQuotientEvaluationAlgHom
            (Published.standardAffineChartIdeal J)
            (Published.standardAffineChartPoint P) hP) k)
      rw [← hx]
      exact augmentedJet_moduleFinite_of_localization_isStandardSmooth
        s x r k
    exact Module.Finite.equiv E.toLinearEquiv
  · intro k
    let E := specialFiberPointPowerQuotientAlgEquivJetSpace
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P) hP k
    rw [← E.toLinearEquiv.finrank_eq]
    change Module.finrank (ZMod p)
      (augmentedJet
        (specialFiberQuotientEvaluationAlgHom
          (Published.standardAffineChartIdeal J)
          (Published.standardAffineChartPoint P) hP) k) =
      (k + r).choose r
    rw [← hx]
    exact finrank_augmentedJet_eq_choose_of_localization_isStandardSmooth
      s x r k

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
/-- Literal selected equations, equality with the affine component ideal,
and one nonzero full Jacobian minor imply multiplicity one at the marked
point.  No smoothness predicate occurs among the hypotheses. -/
theorem hasHilbertSamuelMultiplicityAt_one_of_selectedJacobian
    {N c p : ℕ} (hp : p.Prime) [Fact p.Prime]
    (J : Ideal (MvPolynomial (Fin (N + 1)) (ZMod p)))
    (P : Fin (N + 1) → ZMod p)
    (hP : Published.IsPointOnSpecialFiber
      (Published.standardAffineChartIdeal J)
      (Published.standardAffineChartPoint P))
    (equations : Fin c → MvPolynomial (Fin N) (ZMod p))
    (selectedVar : Fin c → Fin N)
    (hselected : Function.Injective selectedVar)
    (hJ : Ideal.span (Set.range equations) =
      Published.standardAffineChartIdeal J)
    (hminor : MvPolynomial.aeval (Published.standardAffineChartPoint P)
      (selectedJacobianDeterminant equations selectedVar) ≠ 0) :
    Published.HasHilbertSamuelMultiplicityAt hp J P (N - c) 1 := by
  let J₀ := Published.standardAffineChartIdeal J
  let z := Published.standardAffineChartPoint P
  have hz : J₀ ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
    simpa [J₀, z, Published.IsPointOnSpecialFiber,
      Published.specialFiberEvaluation, MvPolynomial.aeval_def] using hP
  let A₀ := HasQuotient.Quotient (MvPolynomial (Fin N) (ZMod p)) J₀
  let chart : A₀ := Ideal.Quotient.mk J₀
    (selectedJacobianDeterminant equations selectedVar)
  let T₀ := Localization.Away chart
  obtain ⟨x, hx, hsmooth⟩ :=
    selectedJacobian_principalOpen_standardSmooth_and_point
      equations selectedVar hselected J₀ hJ z hz hminor
  letI : Algebra.IsStandardSmoothOfRelativeDimension
      (N - c) (ZMod p) T₀ := hsmooth
  have hxf : localizationRestrictedPoint (A := A₀) x =
      specialFiberQuotientEvaluationAlgHom J₀ z hz := by
    calc
      localizationRestrictedPoint (A := A₀) x =
          affineQuotientRationalPoint J₀ z hz := hx
      _ = specialFiberQuotientEvaluationAlgHom J₀ z hz := by
        rfl
  exact hasHilbertSamuelMultiplicityAt_one_of_localization_isStandardSmooth
    hp J P (N - c) hP chart T₀ x hxf

end

end TranslatedDepthSeven
