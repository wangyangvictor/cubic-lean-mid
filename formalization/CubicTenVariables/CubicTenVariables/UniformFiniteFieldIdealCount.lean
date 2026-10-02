import CubicTenVariables.NoetherianFiniteFieldBound
import CubicTenVariables.GenericComponentFiniteFieldCount

/-! Uniform finite-field point counts for one fixed affine equation ideal
over a Noetherian parameter ring. Component normalization supplies the dense
open bounds; finite Noetherian devissage includes all exceptional parameter
strata. No counting or dimension-specialization result is assumed as input. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.UniformFiniteFieldIdealCount
open MvPolynomial

/-- One dense open of an integral parameter base admits a uniform count
with exponent the actual specialized quotient dimension. -/
theorem exists_dense_open_bound
    {B K : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [Algebra B K] [IsFractionRing B K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B)) :
    ∃ s : B, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
      ∀ (L : Type) [Field L] [Fintype L] (ρ : B →+* L), ρ s ≠ 0 → ∀ j : ℕ,
        ringKrullDim (MvPolynomial (Fin N) (L) ⧸ I.map (MvPolynomial.map ρ)) ≤
          (j : WithBot ℕ∞) →
        Nat.card {x : Fin N → L // ∀ f ∈ I, MvPolynomial.eval₂Hom ρ x f = 0} ≤ C * Nat.card L^j := by
  apply NoetherianFiniteFieldBound.exists_dense_open_of_component_bounds (K := K) I
  intro Q hQ
  exact GenericComponentFiniteFieldCount.exists_bound I Q hQ

/-- A single constant precedes every finite field, parameter specialization and
dimension threshold. All finite fields and all exceptional fibers are included. -/
theorem exists_bound
    {R : Type} [CommRing R] [IsNoetherianRing R] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [Fintype L] (ρ : R →+* L) (j : ℕ),
      ringKrullDim (MvPolynomial (Fin N) (L) ⧸ I.map (MvPolynomial.map ρ)) ≤
        (j : WithBot ℕ∞) →
      Nat.card {x : Fin N → L // ∀ f ∈ I, MvPolynomial.eval₂Hom ρ x f = 0} ≤ C * Nat.card L^j := by
  apply NoetherianFiniteFieldBound.exists_uniform_of_quotient_open I
  intro P _
  exact exists_dense_open_bound (K := FractionRing (R ⧸ P))
    (I.map (MvPolynomial.map (Ideal.Quotient.mk P)))

end CubicTenVariables.UniformFiniteFieldIdealCount
