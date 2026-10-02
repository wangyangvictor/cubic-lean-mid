import TranslatedDepthSeven.JacobianCertificate
import TranslatedDepthSeven.TangentPacketSpan

/-!
# Nonzero and bounded Jacobian-minor certificates

This file closes the finite-dimensional linear-algebra portion of the
smooth-specialisation certificate.  A rational rank lower bound produces
literal row and column maps with a nonzero integral Jacobian minor.  A
uniform bound for the entries of the displayed integral Jacobian gives an
explicit factorial determinant bound for that same minor.

The remaining geometric-height problem is only to construct the equations
and prove an entry bound for their evaluated derivatives.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Every explicitly selected Jacobian minor has the usual Leibniz
factorial bound once all evaluated derivatives are bounded. -/
theorem integralJacobianMinor_natAbs_le_factorial_mul_pow
    {c N r M : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin r → Fin c) (cols : Fin r → Fin N)
    (hentry : ∀ i j, (integralJacobianMatrix F y i j).natAbs ≤ M) :
    (integralJacobianMinor F y rows cols).natAbs ≤
      r.factorial * M ^ r := by
  exact TangentPacketSpan.det_natAbs_le_factorial_mul_pow
    ((integralJacobianMatrix F y).submatrix rows cols)
    (fun i j ↦ hentry (rows i) (cols j))

/-- Rank at least r over the rationals supplies a literal nonzero r by r
integral Jacobian minor.  The row and column maps are also proved injective,
so the certificate is an honest minor rather than a repeated-index
determinant. -/
theorem exists_nonzero_integralJacobianMinor_of_rank_ge
    {c N r : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (hrank : r ≤
      ((integralJacobianMatrix F y).map
        (Int.castRingHom ℚ)).rank) :
    ∃ rows : Fin r → Fin c, ∃ cols : Fin r → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor F y rows cols ≠ 0 := by
  let A : Matrix (Fin c) (Fin N) ℚ :=
    (integralJacobianMatrix F y).map (Int.castRingHom ℚ)
  have hspan : r ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range A.row)) := by
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hrank
  obtain ⟨rows, cols, hrows, hcols, hdet⟩ :=
    TangentPacketSpan.exists_nonzero_minor_of_finrank_span_ge
      A.row hspan
  refine ⟨rows, cols, hrows, hcols, ?_⟩
  intro hzero
  apply hdet
  have hcast :
      (integralJacobianMinor F y rows cols : ℚ) =
        Matrix.det (Matrix.of fun i j ↦ A (rows i) (cols j)) := by
    change (Int.castRingHom ℚ)
        (((integralJacobianMatrix F y).submatrix rows cols).det) = _
    rw [RingHom.map_det]
    rfl
  change Matrix.det (Matrix.of fun i j ↦ A (rows i) (cols j)) = 0
  rw [← hcast, hzero]
  norm_num

/-- Combined form: a rational rank lower bound and an entry bound produce
a nonzero integer certificate with an explicit absolute-value bound. -/
theorem exists_bounded_nonzero_integralJacobianMinor
    {c N r M : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (hrank : r ≤
      ((integralJacobianMatrix F y).map
        (Int.castRingHom ℚ)).rank)
    (hentry : ∀ i j, (integralJacobianMatrix F y i j).natAbs ≤ M) :
    ∃ rows : Fin r → Fin c, ∃ cols : Fin r → Fin N,
      Function.Injective rows ∧ Function.Injective cols ∧
        integralJacobianMinor F y rows cols ≠ 0 ∧
        (integralJacobianMinor F y rows cols).natAbs ≤
          r.factorial * M ^ r := by
  obtain ⟨rows, cols, hrows, hcols, hnonzero⟩ :=
    exists_nonzero_integralJacobianMinor_of_rank_ge F y hrank
  exact ⟨rows, cols, hrows, hcols, hnonzero,
    integralJacobianMinor_natAbs_le_factorial_mul_pow
      F y rows cols hentry⟩

end

end TranslatedDepthSeven
