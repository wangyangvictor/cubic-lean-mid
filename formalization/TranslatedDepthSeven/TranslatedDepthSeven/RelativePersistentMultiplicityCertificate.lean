import TranslatedDepthSeven.RelativeTriangularCoefficientHeight
import TranslatedDepthSeven.IntegralSelectedJacobianCertificate
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Relative local multiplicity certificates

A relative affine polynomial is written as a polynomial in the affine-point
variables whose coefficients are integral polynomials in the family
parameters.  This file retains a finite family of local equations, a fixed
Jacobian minor, and a finite family of principal-open clearing polynomials as
literal data.  It proves that, after integral specialization, the exceptional
integer used by the multiplicity-one argument is the value of one fixed
polynomial in the joint parameter and point variables.

Consequently one finite support--coefficient--degree triple bounds all such
integers by a fixed power of the joint height.  No component construction,
elimination theorem, or assertion about specialization of prime ideals occurs
here; those are precisely the geometric inputs which must supply the displayed
relative charts.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- An integral polynomial in `N` affine variables with coefficients that
are integral polynomials in `M` family parameters. -/
abbrev RelativeIntegralAffinePolynomial (M N : ℕ) :=
  MvPolynomial (Fin N) (MvPolynomial (Fin M) ℤ)

/-- Specialize the parameter coefficients of a relative affine polynomial. -/
def specializeRelativeIntegralAffinePolynomial {M N : ℕ}
    (parameter : Fin M → ℤ) :
    RelativeIntegralAffinePolynomial M N →+*
      MvPolynomial (Fin N) ℤ :=
  MvPolynomial.map (MvPolynomial.eval parameter)

/-- Regard an iterated relative polynomial as one polynomial in the disjoint
union of the affine and parameter variables. -/
def flattenRelativeIntegralAffinePolynomial {M N : ℕ}
    (f : RelativeIntegralAffinePolynomial M N) :
    MvPolynomial (Fin N ⊕ Fin M) ℤ :=
  (MvPolynomial.sumRingEquiv ℤ (Fin N) (Fin M)).symm f

/-- Evaluation of a specialized relative polynomial is simultaneous
evaluation of its fixed joint-variable polynomial. -/
theorem eval_specializeRelativeIntegralAffinePolynomial
    {M N : ℕ} (parameter : Fin M → ℤ) (point : Fin N → ℤ)
    (f : RelativeIntegralAffinePolynomial M N) :
    MvPolynomial.eval point
        (specializeRelativeIntegralAffinePolynomial parameter f) =
      MvPolynomial.eval (Sum.elim point parameter)
        (flattenRelativeIntegralAffinePolynomial f) := by
  let lhs : RelativeIntegralAffinePolynomial M N →+* ℤ :=
    (MvPolynomial.eval point).comp
      (specializeRelativeIntegralAffinePolynomial parameter)
  let rhs : RelativeIntegralAffinePolynomial M N →+* ℤ :=
    (MvPolynomial.eval (Sum.elim point parameter)).comp
      (MvPolynomial.sumRingEquiv ℤ (Fin N) (Fin M)).symm.toRingHom
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro g
      dsimp [lhs, rhs, specializeRelativeIntegralAffinePolynomial]
      simp only [MvPolynomial.map_C, MvPolynomial.eval_C]
      change MvPolynomial.eval parameter g =
        MvPolynomial.eval (Sum.elim point parameter)
          (MvPolynomial.iterToSum ℤ (Fin N) (Fin M) (MvPolynomial.C g))
      let phi : MvPolynomial (Fin M) ℤ →+* ℤ :=
        (MvPolynomial.eval (Sum.elim point parameter)).comp
          ((MvPolynomial.iterToSum ℤ (Fin N) (Fin M)).comp
            MvPolynomial.C)
      have hphi : phi = MvPolynomial.eval parameter := by
        apply MvPolynomial.ringHom_ext
        · intro z
          simp [phi]
        · intro j
          simp [phi, MvPolynomial.iterToSum_C_X]
      exact (RingHom.congr_fun hphi g).symm
    · intro i
      dsimp [lhs, rhs, specializeRelativeIntegralAffinePolynomial]
      simp only [MvPolynomial.map_X, MvPolynomial.eval_X]
      change point i =
        MvPolynomial.eval (Sum.elim point parameter)
          (MvPolynomial.iterToSum ℤ (Fin N) (Fin M) (MvPolynomial.X i))
      rw [MvPolynomial.iterToSum_X]
      simp
  exact RingHom.congr_fun h f

/-- Literal data on one relative local chart.  The equations and clearing
polynomials are chosen before specialization.  The algebraic-geometric
construction must separately prove that the specialized equations generate
the required component locally and that the displayed clearing polynomials
generate enough of the corresponding colon ideal. -/
structure RelativePersistentSurfaceChart
    (M N equationCount clearingCount : ℕ) where
  equation : Fin equationCount → RelativeIntegralAffinePolynomial M N
  selectedVar : Fin equationCount → Fin N
  selectedVar_injective : Function.Injective selectedVar
  clearingPolynomial : Fin clearingCount →
    RelativeIntegralAffinePolynomial M N

/-- The specialized integral affine equations of a relative chart. -/
def RelativePersistentSurfaceChart.specializedEquations
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) :
    Fin equationCount → MvPolynomial (Fin N) ℤ :=
  fun i ↦ specializeRelativeIntegralAffinePolynomial parameter
    (chart.equation i)

/-- The specialized principal-open clearing polynomial. -/
def RelativePersistentSurfaceChart.specializedClearingPolynomial
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) (i : Fin clearingCount) :
    MvPolynomial (Fin N) ℤ :=
  specializeRelativeIntegralAffinePolynomial parameter
    (chart.clearingPolynomial i)

/-- The selected relative Jacobian determinant, before specialization. -/
def RelativePersistentSurfaceChart.relativeJacobianDeterminant
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount) :
    RelativeIntegralAffinePolynomial M N :=
  selectedJacobianDeterminant chart.equation chart.selectedVar

/-- The fixed joint-variable polynomial whose specialization is the bad-prime
integer attached to one clearing polynomial on one relative chart. -/
def RelativePersistentSurfaceChart.certificatePolynomial
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (i : Fin clearingCount) : MvPolynomial (Fin N ⊕ Fin M) ℤ :=
  flattenRelativeIntegralAffinePolynomial (chart.clearingPolynomial i) *
    flattenRelativeIntegralAffinePolynomial
      chart.relativeJacobianDeterminant

/-- The selected Jacobian determinant commutes exactly with specialization
of the family parameters. -/
theorem RelativePersistentSurfaceChart.specialize_jacobianDeterminant
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) :
    specializeRelativeIntegralAffinePolynomial parameter
        chart.relativeJacobianDeterminant =
      selectedJacobianDeterminant
        (chart.specializedEquations parameter) chart.selectedVar := by
  exact map_selectedJacobianDeterminant
    (MvPolynomial.eval parameter) chart.equation chart.selectedVar

/-- The specialized exceptional integer is literally evaluation of the
fixed joint-variable certificate polynomial. -/
theorem RelativePersistentSurfaceChart.certificate_eq_eval
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) (point : Fin N → ℤ)
    (i : Fin clearingCount) :
    integralSelectedJacobianChartCertificate
        (chart.specializedEquations parameter) chart.selectedVar
        (chart.specializedClearingPolynomial parameter i) point =
      MvPolynomial.eval (Sum.elim point parameter)
        (chart.certificatePolynomial i) := by
  rw [integralSelectedJacobianChartCertificate,
    RelativePersistentSurfaceChart.certificatePolynomial,
    map_mul]
  change
    MvPolynomial.eval point
          (specializeRelativeIntegralAffinePolynomial parameter
            (chart.clearingPolynomial i)) *
        MvPolynomial.eval point
          (selectedJacobianDeterminant
            (chart.specializedEquations parameter) chart.selectedVar) = _
  rw [← chart.specialize_jacobianDeterminant parameter]
  rw [eval_specializeRelativeIntegralAffinePolynomial,
    eval_specializeRelativeIntegralAffinePolynomial]

/-- All certificate polynomials of one relative chart, as one literal finite
family. -/
def RelativePersistentSurfaceChart.certificatePolynomialFamily
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount) :
    Fin clearingCount → MvPolynomial (Fin N ⊕ Fin M) ℤ :=
  chart.certificatePolynomial

/-- Uniform natural-number height bound for every specialized certificate
of one relative chart.  All constants are finite suprema computed from the
literal joint-variable certificate family. -/
theorem RelativePersistentSurfaceChart.certificate_natAbs_le
    {M N equationCount clearingCount Y : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) (point : Fin N → ℤ)
    (hparameter : ∀ j, (parameter j).natAbs ≤ Y)
    (hpoint : ∀ j, (point j).natAbs ≤ Y)
    (i : Fin clearingCount) :
    (integralSelectedJacobianChartCertificate
      (chart.specializedEquations parameter) chart.selectedVar
      (chart.specializedClearingPolynomial parameter i) point).natAbs ≤
        finiteIntegralPolynomialSupportBound
            chart.certificatePolynomialFamily *
          finiteIntegralPolynomialCoefficientBound
            chart.certificatePolynomialFamily *
          max 1 Y ^ finiteIntegralPolynomialDegreeBound
            chart.certificatePolynomialFamily := by
  rw [chart.certificate_eq_eval parameter point i]
  apply finiteIntegralPolynomialFamily_eval_natAbs_le
  intro j
  cases j with
  | inl j => exact hpoint j
  | inr j => exact hparameter j

/-- A completely explicit power of a real height which absorbs the finite
support and coefficient constants of one relative chart.  The deliberately
generous exponent is harmless in the reservoir argument: the chart is fixed,
so this is one fixed natural number. -/
def RelativePersistentSurfaceChart.certificateHeightExponent
    {M N equationCount clearingCount : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (coordinateExponent : ℕ) : ℕ :=
  finiteIntegralPolynomialSupportBound chart.certificatePolynomialFamily *
      finiteIntegralPolynomialCoefficientBound
        chart.certificatePolynomialFamily +
    coordinateExponent *
      finiteIntegralPolynomialDegreeBound chart.certificatePolynomialFamily

/-- If every parameter and point coordinate is bounded by `Y`, and `Y` is
itself at most the `coordinateExponent`-th power of a real height `H ≥ 2`,
then every specialized exceptional integer is at most the fixed power of
`H` displayed by `certificateHeightExponent`.

The proof uses only the elementary estimate `K ≤ 2^K`, so no effective
elimination or hidden coefficient-height theorem occurs here. -/
theorem RelativePersistentSurfaceChart.certificate_natAbs_cast_le_heightPower
    {M N equationCount clearingCount Y coordinateExponent : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) (point : Fin N → ℤ)
    (hparameter : ∀ j, (parameter j).natAbs ≤ Y)
    (hpoint : ∀ j, (point j).natAbs ≤ Y)
    (i : Fin clearingCount) (H : ℝ) (hH : 2 ≤ H)
    (hY : (Y : ℝ) ≤ H ^ coordinateExponent) :
    ((integralSelectedJacobianChartCertificate
      (chart.specializedEquations parameter) chart.selectedVar
      (chart.specializedClearingPolynomial parameter i) point).natAbs : ℝ) ≤
        H ^ chart.certificateHeightExponent coordinateExponent := by
  let K : ℕ :=
    finiteIntegralPolynomialSupportBound chart.certificatePolynomialFamily *
      finiteIntegralPolynomialCoefficientBound chart.certificatePolynomialFamily
  let E : ℕ :=
    finiteIntegralPolynomialDegreeBound chart.certificatePolynomialFamily
  have hnatural := chart.certificate_natAbs_le parameter point
    hparameter hpoint i
  have hcast :
      ((integralSelectedJacobianChartCertificate
        (chart.specializedEquations parameter) chart.selectedVar
        (chart.specializedClearingPolynomial parameter i) point).natAbs : ℝ) ≤
        (K : ℝ) * ((max 1 Y : ℕ) : ℝ) ^ E := by
    exact_mod_cast hnatural
  have hKtwo : (K : ℝ) ≤ (2 : ℝ) ^ K := by
    have hKtwoNat : K ≤ 2 ^ K := by
      induction K with
      | zero => simp
      | succ K hK =>
          calc
            K + 1 ≤ 2 ^ K + 1 := Nat.add_le_add_right hK 1
            _ ≤ 2 ^ K + 2 ^ K :=
              Nat.add_le_add_left Nat.one_le_two_pow (2 ^ K)
            _ = 2 ^ (K + 1) := by rw [pow_succ]; omega
    exact_mod_cast hKtwoNat
  have hK : (K : ℝ) ≤ H ^ K :=
    hKtwo.trans (pow_le_pow_left₀ (by norm_num) hH K)
  have honeH : (1 : ℝ) ≤ H := by linarith
  have honePow : (1 : ℝ) ≤ H ^ coordinateExponent :=
    one_le_pow₀ honeH
  have hmax : ((max 1 Y : ℕ) : ℝ) ≤ H ^ coordinateExponent := by
    norm_num only [Nat.cast_max, Nat.cast_one]
    exact max_le honePow hY
  calc
    ((integralSelectedJacobianChartCertificate
      (chart.specializedEquations parameter) chart.selectedVar
      (chart.specializedClearingPolynomial parameter i) point).natAbs : ℝ) ≤
        (K : ℝ) * ((max 1 Y : ℕ) : ℝ) ^ E := hcast
    _ ≤ H ^ K * (H ^ coordinateExponent) ^ E := by
      exact mul_le_mul hK
        (pow_le_pow_left₀ (by positivity) hmax E)
        (by positivity) (by positivity)
    _ = H ^ (K + coordinateExponent * E) := by ring
    _ = H ^ chart.certificateHeightExponent coordinateExponent := by
      rfl

/-- Real-exponent form matching the certificate-size hypothesis in
`exists_finite_persistentSurface_multiplicityOne_records`. -/
theorem RelativePersistentSurfaceChart.certificate_natAbs_cast_le_rpow
    {M N equationCount clearingCount Y coordinateExponent : ℕ}
    (chart : RelativePersistentSurfaceChart M N equationCount clearingCount)
    (parameter : Fin M → ℤ) (point : Fin N → ℤ)
    (hparameter : ∀ j, (parameter j).natAbs ≤ Y)
    (hpoint : ∀ j, (point j).natAbs ≤ Y)
    (i : Fin clearingCount) (H A : ℝ) (hH : 2 ≤ H)
    (hY : (Y : ℝ) ≤ H ^ coordinateExponent)
    (hA : (chart.certificateHeightExponent coordinateExponent : ℝ) ≤ A) :
    ((integralSelectedJacobianChartCertificate
      (chart.specializedEquations parameter) chart.selectedVar
      (chart.specializedClearingPolynomial parameter i) point).natAbs : ℝ) ≤
        H ^ A := by
  have hnatural := chart.certificate_natAbs_cast_le_heightPower
    parameter point hparameter hpoint i H hH hY
  apply hnatural.trans
  simpa only [Real.rpow_natCast] using
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hA)

end

end TranslatedDepthSeven
