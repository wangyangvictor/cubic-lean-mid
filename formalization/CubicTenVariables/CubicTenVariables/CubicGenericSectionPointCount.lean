import CubicTenVariables.CubicGenericSmoothSectionCertificate
import CubicTenVariables.CubicFixedFamilySlicing

/-! The fixed-cubic point-count endpoint from a literal generic Jacobian
condition and the numerical smooth-cubic Weil bound. The generic condition
is an explicit local argument, not a new global literature assumption.
The exceptional integer is chosen before the prime and every finite
extension; the displayed constant is 15. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicGenericSectionPointCount
open MvPolynomial Literature CubicGenericSmoothSectionCertificate
open ProjectiveLinearSectionJacobian

/-- Smoothness of the one generic section supplies the entire good-prime
ambient estimate needed by the shifted average. -/
theorem exists_uniform_bound
    (weil : SmoothCubicWeil) {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (F : MvPolynomial (Fin 10) ℤ) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (ι : ParameterRing →+* Ω) (hι : Function.Injective ι)
    (hjac : ∀ x : Fin 10 → Ω, x ≠ 0 →
      eval x (MvPolynomial.map (ι.comp C) F) = 0 →
      (genericNormal.map ι).mulVec x = 0 →
      (augmentedSectionJacobian (MvPolynomial.map (ι.comp C) F)
        (genericNormal.map ι) x).rank = 6) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ A →
      ∀ (E : Type) [Field E] [Fintype E] [CharP E p],
        |(affineZeroCount (map (Int.castRingHom E) F) : ℝ) -
            (Fintype.card E : ℝ) ^ 9| ≤
          15 * ((Fintype.card E : ℝ) - 1) *
            (Fintype.card E : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨Δ, hΔ, hgood⟩ := exists_nonzero_goodJacobian_certificate F ι hι hjac
  apply CubicFixedFamilySlicing.exists_good_prime_affine_bound
    weil F hFne hF Δ hΔ 1 le_rfl
  intro p _ _ E _ _ _ γ hγ
  exact hgood E γ hγ

/-- The literal prime-field form, with the origin included in the count. -/
theorem exists_prime_bound
    (weil : SmoothCubicWeil) {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (F : MvPolynomial (Fin 10) ℤ) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (ι : ParameterRing →+* Ω) (hι : Function.Injective ι)
    (hjac : ∀ x : Fin 10 → Ω, x ≠ 0 →
      eval x (MvPolynomial.map (ι.comp C) F) = 0 →
      (genericNormal.map ι).mulVec x = 0 →
      (augmentedSectionJacobian (MvPolynomial.map (ι.comp C) F)
        (genericNormal.map ι) x).rank = 6) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ p : ℕ, (hp : p.Prime) → ¬ p ∣ A →
      letI : Fact p.Prime := ⟨hp⟩
      |(Nat.card {x : Fin 10 → ZMod p // eval₂ (Int.castRingHom (ZMod p)) x F = 0} : ℝ) -
          (p : ℝ) ^ 9| ≤ 15 * ((p : ℝ) - 1) * (p : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨A, hA, hgood⟩ := exists_uniform_bound weil F hFne hF ι hι hjac
  refine ⟨A, hA, ?_⟩
  intro p hp hpA
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [affineZeroCount, eval_map, ZMod.card] using hgood p hp hpA (ZMod p)

end CubicTenVariables.CubicGenericSectionPointCount
