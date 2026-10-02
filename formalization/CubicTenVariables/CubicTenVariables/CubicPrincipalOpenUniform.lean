import CubicTenVariables.CubicPrincipalOpenIntegrality

/-! Internally proved interface for spreading integrality of homogeneous
cubic hypersurfaces on a fixed principal parameter open. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicPrincipalOpenUniform
open MvPolynomial

/-- This cubic-family interface has an unconditional inhabitant. It does
not claim the older general finitely presented family spreading theorem. -/
def Uniform : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ)
    (F : MvPolynomial (Fin n) (MvPolynomial σ ℤ)), F.IsHomogeneous 3 →
    ∀ h : MvPolynomial σ ℤ,
    (∀ v : σ → AlgebraicClosure ℚ,
      eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v h ≠ 0 →
        (map (eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v) F).totalDegree = 3 ∧
        IsDomain (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
          Ideal.span {map (eval₂Hom (Int.castRingHom (AlgebraicClosure ℚ)) v) F})) →
    ∃ D : ℕ, 1 ≤ D ∧ ∀ p : ℕ, ¬ p ∣ D →
      ∀ (K : Type) [Field K] [CharP K p] (v : σ → K),
        eval₂Hom (Int.castRingHom K) v h ≠ 0 →
        IsDomain (MvPolynomial (Fin n) K ⧸
          Ideal.span {map (eval₂Hom (Int.castRingHom K) v) F})

/-- The uniform characteristic statement follows from the explicit factor
equations and integer denominator clearing. -/
theorem proved : Uniform := by
  intro σ _ n F hF h hgeneric
  exact CubicPrincipalOpenIntegrality.exists_good_characteristic F hF h hgeneric

end CubicTenVariables.CubicPrincipalOpenUniform
