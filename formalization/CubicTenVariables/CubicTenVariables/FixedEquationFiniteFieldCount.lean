import CubicTenVariables.FixedEquationDimensionAll
import CubicTenVariables.LocalizedIntegerExceptionalSet

/-! Finite-field counts for one fixed integral equation model, obtained
from the existing finite normalization. One exceptional integer and one
constant work for all finite extensions. Empty generic models are included.
This does not assert a bound uniform over arbitrary bounded-degree equations. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedEquationFiniteFieldCount
open MvPolynomial FixedEquationNormalization FixedEquationDimensionReduction

/-- The rational dimension of a fixed integral model controls its point
count in every finite field away from one integer. No point-count input is used. -/
theorem exists_good_characteristic_bound {n t r : ℕ}
    (f : Fin t → MvPolynomial (Fin n) ℤ)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ equationIdeal f ℚ) ≤
      (r : WithBot ℕ∞)) :
    ∃ D C : ℕ, 1 ≤ D ∧ 1 ≤ C ∧ ∀ (p : ℕ), p.Prime → ¬ p ∣ D →
      ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
        Nat.card {x : Fin n → K // ∀ i, eval₂ (Int.castRingHom K) x (f i) = 0} ≤
          C * (Fintype.card K)^r := by
  by_cases htop : equationIdeal f ℚ = ⊤
  · obtain ⟨D,hD,hgood⟩ := FixedEquationDimensionAll.exists_good_characteristic_top f htop
    refine ⟨D,1,hD,by omega,?_⟩
    intro p _ hp K _ _ _
    change Nat.card (zeroSet f K) ≤ _
    rw [(hgood p hp K).2]
    simp
  · obtain ⟨Δ,hΔ,δ,hδ,C,hC,hcount⟩ := exists_specialization_bound f htop hdim
    obtain ⟨D,hD,_hΔD,hunit⟩ :=
      LocalizedIntegerExceptionalSet.exists_exceptionalInteger Δ hΔ δ hδ
    refine ⟨D,C,hD,hC,?_⟩
    intro p hp hpD K _ _ _
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨hpΔ,hu⟩ := hunit p hp hpD
    let ρ := (ZMod.castHom (dvd_refl p) K).comp
      (TranslatedDepthSeven.awayIntToZMod Δ p hp hpΔ)
    have hρ : IsUnit (ρ δ) := hu.map (ZMod.castHom (dvd_refl p) K)
    simpa only [Nat.card_eq_fintype_card] using hcount K ρ hρ

end CubicTenVariables.FixedEquationFiniteFieldCount
