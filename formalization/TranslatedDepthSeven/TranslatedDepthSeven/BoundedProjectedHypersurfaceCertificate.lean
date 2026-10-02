import TranslatedDepthSeven.ProjectedHypersurfaceDerivativeBridge

/-!
# A bounded integer certifying smooth reduction of the hypersurface image

This combines the literal one-row Jacobian identity, Euler's identity,
the elementary coefficient bound and the checked primitive closure lemma.
The only primes excluded are divisors of the displayed nonzero integer.
The statement concerns the image hypersurface, not a source component.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

theorem exists_bounded_projectedHypersurface_derivative_certificate
    {r e C R : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℤ)
    (hprimitive : IsPrimitiveIntegralMvPolynomial P)
    (hirreducible : Irreducible (P.map (Int.castRingHom ℚ)))
    (hhom : P.IsHomogeneous e)
    (hcoeff : ∀ m, (P.coeff m).natAbs ≤ C)
    (z : Fin (r + 1) → ℤ) (hR : 1 ≤ R)
    (hz : ∀ i, (z i).natAbs ≤ R)
    (hpoint : MvPolynomial.eval (integralAffineProjectivePoint z) P = 0)
    (hgradient : ∃ i,
      MvPolynomial.eval (integralAffineProjectivePoint z)
        (MvPolynomial.pderiv i P) ≠ 0) :
    ∃ j : Fin (r + 1),
      let Δ : ℤ := MvPolynomial.eval (integralAffineProjectivePoint z)
        (MvPolynomial.pderiv j.succ P)
      Δ ≠ 0 ∧
      Δ.natAbs ≤ (e + 1) ^ (r + 2) * e * C * max 1 R ^ e ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ Δ.natAbs →
        HasHilbertSamuelMultiplicityAt hp
          (projectiveSpecialFiberIdeal (Ideal.span {P.map (Int.castRingHom ℚ)}))
          (fun i ↦ (integralAffineProjectivePoint z i : ZMod p)) r 1 := by
  obtain ⟨j, hj⟩ := exists_nonzero_affine_partial_of_homogeneous_gradient
    P hhom (integralAffineProjectivePoint z) (by rfl) hpoint hgradient
  refine ⟨j, hj, ?_, ?_⟩
  · apply bounded_homogeneous_partial_derivative P hhom hcoeff
      (integralAffineProjectivePoint z) _ j.succ
    intro i
    exact Fin.cases (by simpa using hR) hz i
  · have hdehom : MvPolynomial.eval z (integralDehomogenizeAtZeroHom P) = 0 := by
      rw [eval_integralDehomogenizeAtZeroHom]
      exact hpoint
    have hminor : MvPolynomial.eval z
        (selectedJacobianDeterminant (projectedHypersurfaceAffineEquation P)
          (projectedHypersurfaceSelectedVariable j)) ≠ 0 := by
      rw [eval_projectedHypersurfaceJacobian_eq_spatial_partial]
      exact hj
    have hcertificate := projectedHypersurface_multiplicityOne_of_primitiveEquation
      P hprimitive hirreducible z j hdehom hminor
    simpa only [eval_projectedHypersurfaceJacobian_eq_spatial_partial] using
      hcertificate.2

end

end TranslatedDepthSeven
