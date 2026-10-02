import TranslatedDepthSeven.HomogeneousCone
import TranslatedDepthSeven.JacobianMinorStandardSmoothChart
import TranslatedDepthSeven.PrincipalOpenReduction

/-!
# One integer for a marked selected-Jacobian chart

For a fixed integral equation family, an integral principal-open element,
and an integral marked point, the product of two literal evaluations is a
single integer certificate.  At every prime not dividing that integer, both
the principal-open element and the selected Jacobian determinant remain
nonzero at the reduced point.

No smoothness or component condition is asserted here.  Those conditions
enter only through the integral equations and the integral clearing identity
to which this certificate is later applied.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Evaluation of the selected Jacobian determinant commutes with reduction
of both coefficients and the marked integral point. -/
theorem eval_selectedJacobianDeterminant_map_intCast
    {R : Type*} [CommRing R] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin c → Fin N) (x : Fin N → ℤ) :
    MvPolynomial.eval (fun i ↦ (x i : R))
        (selectedJacobianDeterminant
          (fun j ↦ MvPolynomial.map (Int.castRingHom R) (equations j))
          selectedVar) =
      (MvPolynomial.eval x
        (selectedJacobianDeterminant equations selectedVar) : R) := by
  rw [← map_selectedJacobianDeterminant]
  exact eval_map_intCast
    (selectedJacobianDeterminant equations selectedVar) x

/-- The literal bad-prime certificate attached to an integral local chart at
an integral marked point. -/
def integralSelectedJacobianChartCertificate
    {N c : ℕ} (equations : Fin c → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin c → Fin N)
    (u : MvPolynomial (Fin N) ℤ) (x : Fin N → ℤ) : ℤ :=
  MvPolynomial.eval x u *
    MvPolynomial.eval x
      (selectedJacobianDeterminant equations selectedVar)

/-- Avoiding the one displayed integer makes both factors defining the
marked selected-Jacobian chart nonzero after reduction. -/
theorem integralSelectedJacobianChartCertificate_nonvanishing
    {N c p : ℕ} (hp : p.Prime)
    (equations : Fin c → MvPolynomial (Fin N) ℤ)
    (selectedVar : Fin c → Fin N)
    (u : MvPolynomial (Fin N) ℤ) (x : Fin N → ℤ)
    (hpCertificate : ¬p ∣
      (integralSelectedJacobianChartCertificate
        equations selectedVar u x).natAbs) :
    MvPolynomial.aeval (fun i ↦ (x i : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) u) ≠ 0 ∧
      MvPolynomial.aeval (fun i ↦ (x i : ZMod p))
        (selectedJacobianDeterminant
          (fun j ↦ MvPolynomial.map (Int.castRingHom (ZMod p))
            (equations j)) selectedVar) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcertificate :
      (integralSelectedJacobianChartCertificate
        equations selectedVar u x : ZMod p) ≠ 0 :=
    intCast_zmod_ne_zero_of_not_dvd_natAbs
      (integralSelectedJacobianChartCertificate
        equations selectedVar u x) p hpCertificate
  have hproduct :
      (MvPolynomial.eval x u : ZMod p) *
          (MvPolynomial.eval x
            (selectedJacobianDeterminant equations selectedVar) : ZMod p) ≠
        0 := by
    simpa only [integralSelectedJacobianChartCertificate, Int.cast_mul]
      using hcertificate
  obtain ⟨hu, hminor⟩ := mul_ne_zero_iff.mp hproduct
  constructor
  · change MvPolynomial.eval (fun i ↦ (x i : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) u) ≠ 0
    simpa only [eval_map_intCast] using hu
  · change MvPolynomial.eval (fun i ↦ (x i : ZMod p))
        (selectedJacobianDeterminant
          (fun j ↦ MvPolynomial.map (Int.castRingHom (ZMod p))
            (equations j)) selectedVar) ≠ 0
    simpa only [eval_selectedJacobianDeterminant_map_intCast] using hminor

end

end TranslatedDepthSeven
