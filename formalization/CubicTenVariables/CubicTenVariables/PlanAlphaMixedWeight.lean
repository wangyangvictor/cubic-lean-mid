import CubicTenVariables.LocalizedRestrictedMultiplicativity
import CubicTenVariables.CubefullRefinedAverage

/-! The literal frequency weight for a fixed localized factor and a
cube-full factor, its CRT identity, and its sharp cube-full mass bound. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaMixedWeight
open MvPolynomial HessianTheorem11 LocalizedRestrictedMultiplicativity
open scoped BigOperators

def weight (F : MvPolynomial (Fin 10) ℤ) (g W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (r : ℕ) (v : Fin 10 → ℤ) : ℝ :=
  ‖localizedCompleteCubicSum F g W Ω v‖ * ‖completeCubicSum F r v‖

theorem weight_nonneg (F : MvPolynomial (Fin 10) ℤ) (g W : ℕ)
    (Ω : Set (Fin 10 → ZMod W)) (r : ℕ) (v : Fin 10 → ℤ) :
    0 ≤ weight F g W Ω r v := mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The frequency is unchanged in all three factors. -/
theorem norm_eq_weight (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (g d r W : ℕ) [NeZero g] [NeZero d] [NeZero r] [NeZero W]
    (Ω : Set (Fin 10 → ZMod W)) (hΩ : ResidueUnitInvariant Ω)
    (hgr : (g*W).Coprime r) (hgd : ((g*r)*W).Coprime d) (v : Fin 10 → ℤ) :
    ‖localizedCompleteCubicSum F (g*d*r) W Ω v‖ =
      weight F g W Ω r v * ‖completeCubicSum F d v‖ := by
  have he : g*d*r = (g*r)*d := by ac_rfl
  rw [he,localized_mul_outside F hF (g*r) d W hgd Ω hΩ v,
    localized_mul_outside F hF g r W hgr Ω hΩ v]
  simp only [norm_mul,weight]

/-- The cube-full average controls the actual frequency-weight mass,
uniformly before all moduli, restrictions, boxes and local pointwise bounds.
The supplied pointwise bound is a helper hypothesis, discharged by the
localized prime-power estimates in the final mixed argument. -/
theorem exists_mass_bound (F : MvPolynomial (Fin 10) ℤ)
    (hF : F.IsHomogeneous 3) (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ r ∈ Q, 0 < r ∧ CubeFullSmithParameters.CubeFull r ∧ (r : ℝ) ≤ 2*X) →
      ∀ (g W : ℕ) (Ω : Set (Fin 10 → ZMod W))
        (V : Finset (Fin 10 → ℤ)) (u : Fin 10 → ℝ) (R H : ℝ),
      1 ≤ R → 0 ≤ H → (∀ v ∈ V, ∀ i, |(v i : ℝ)-u i| ≤ R) →
      (∀ v ∈ V, ‖localizedCompleteCubicSum F g W Ω v‖ ≤ H) →
      (∑ r ∈ Q, ∑ v ∈ V, weight F g W Ω r v) ≤
        H*K*X^((32 : ℝ)/5+ε)*(R+X^((1 : ℝ)/3))^10 := by
  obtain ⟨K,hK,hbound⟩ := CubefullRefinedAverage.exists_dyadic_bound F hF hAn ε hε
  refine ⟨K,hK,?_⟩
  intro X hX Q hQ g W Ω V u R H hR hH hbox hpoint
  calc
    _ ≤ ∑ r ∈ Q, ∑ v ∈ V, H*‖completeCubicSum F r v‖ := by
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum fun v hv =>
        mul_le_mul_of_nonneg_right (hpoint v hv) (norm_nonneg _)
    _ = H*(∑ r ∈ Q, ∑ v ∈ V, ‖completeCubicSum F r v‖) := by
      simp only [Finset.mul_sum]
    _ ≤ H*(K*X^((32 : ℝ)/5+ε)*(R+X^((1 : ℝ)/3))^10) :=
      mul_le_mul_of_nonneg_left (hbound X hX Q hQ V u R hR hbox) hH
    _ = _ := by ring

end CubicTenVariables.PlanAlphaMixedWeight
