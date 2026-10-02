import HessianTheorem11.GeometricFactorization

/-! Internal dependency for the already proved geometric irreducibility of
anisotropic cubics. Public aggregate theorems construct this statement from
the semistability proof; it is not a new external textbook assumption. -/

namespace HessianTheorem11

def CubicGeometricIrreducibility : Prop :=
  ∀ {n : ℕ} (F : AnisotropicCubic n), 4 ≤ n →
    Irreducible (geometricPolynomial F.polynomial)

/-- Compatibility with the earlier factorization-based route. The reduced
public interface instead supplies the direct semistability-based proof. -/
theorem cubicGeometricIrreducibility_of_factorization
    (GF : GeometricHomogeneousFactorizationInput) (DTQ : DeterminantalTangentOver ℚ) :
    CubicGeometricIrreducibility := by
  intro n F hn
  exact anisotropic_cubic_geometrically_irreducible GF DTQ F hn

end HessianTheorem11
