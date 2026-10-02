import TranslatedDepthSeven.JacobianCertificate

/-!
# The exact special-fibre endpoint of an explicit Jacobian certificate

For a displayed finite family of integral equations, a nonzero integral
Jacobian minor remains nonzero modulo every prime not dividing it.  This file
records the precise geometric linear-algebra consequence: the tangent kernel
of the *displayed special-fibre equations* has the expected upper dimension.

This statement is deliberately component-free.  It does not identify the
displayed zero scheme with a chosen reduced irreducible component, does not
assert a lower bound for its local dimension, and therefore does not by itself
assert that any component is smooth.  Those are separate scheme-theoretic
inputs in an application of Salberger's determinant method.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The simultaneous tangent kernel modulo `p` of an indexed finite family of
integral equations at an integral point. -/
def reducedEquationFamilyTangentKernel {c N p : ℕ}
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ) :
    Submodule (ZMod p) (Fin N → ZMod p) :=
  LinearMap.ker (jacobianMatrix F y p).mulVecLin

/-- Rank--nullity gives the exact dimension of the displayed special-fibre
tangent kernel. -/
theorem finrank_reducedEquationFamilyTangentKernel {c N p : ℕ}
    (hp : p.Prime) (F : Fin c → MvPolynomial (Fin N) ℤ)
    (y : Fin N → ℤ) :
    Module.finrank (ZMod p)
        (reducedEquationFamilyTangentKernel (p := p) F y) =
      N - (jacobianMatrix F y p).rank := by
  letI : Fact p.Prime := ⟨hp⟩
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker
      (jacobianMatrix F y p).mulVecLin
  have hsum :
      (jacobianMatrix F y p).rank +
          Module.finrank (ZMod p)
            (reducedEquationFamilyTangentKernel (p := p) F y) = N := by
    simpa [Matrix.rank, reducedEquationFamilyTangentKernel] using
      hrankNullity
  omega

/-- A nonvanishing `(N-d)`-minor bounds the tangent dimension of the
displayed special-fibre equation family by `d`. -/
theorem finrank_reducedEquationFamilyTangentKernel_le_of_minor_not_dvd
    {c N d p : ℕ} (hp : p.Prime) (hdN : d ≤ N)
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin (N - d) → Fin c) (cols : Fin (N - d) → Fin N)
    (hminor : ¬(p : ℤ) ∣ integralJacobianMinor F y rows cols) :
    Module.finrank (ZMod p)
        (reducedEquationFamilyTangentKernel (p := p) F y) ≤ d := by
  have hrank : N - d ≤ (jacobianMatrix F y p).rank :=
    jacobian_rank_ge_of_minor_not_dvd hp F y rows cols hminor
  rw [finrank_reducedEquationFamilyTangentKernel hp F y]
  omega

/-- One integral minor coprime to `q` gives the displayed tangent-dimension
bound at every prime divisor of `q`.  Squarefreeness is not needed here. -/
theorem finrank_reducedEquationFamilyTangentKernel_le_for_prime_divisors
    {c N d q : ℕ} (hdN : d ≤ N)
    (F : Fin c → MvPolynomial (Fin N) ℤ) (y : Fin N → ℤ)
    (rows : Fin (N - d) → Fin c) (cols : Fin (N - d) → Fin N)
    (hcop : Nat.Coprime q
      (integralJacobianMinor F y rows cols).natAbs) :
    ∀ p, p.Prime → p ∣ q →
      Module.finrank (ZMod p)
        (reducedEquationFamilyTangentKernel (p := p) F y) ≤ d := by
  intro p hp hpq
  exact
    finrank_reducedEquationFamilyTangentKernel_le_of_minor_not_dvd
      hp hdN F y rows cols
        (prime_not_dvd_int_of_coprime_natAbs hp hpq hcop)

end

end TranslatedDepthSeven
