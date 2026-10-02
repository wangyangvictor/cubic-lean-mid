import CubicTenVariables.CubeFullSmithBound
import CubicTenVariables.CubefullSmithWeightLocal
import CubicTenVariables.ResidueMajorantExtraction
import CubicTenVariables.ResidueMajorantCRT
import CubicTenVariables.PlanAlphaMixedWeight

/-! Actual cube-full complete sums admit finite-window residue majorants.
The Smith threshold is fixed before the modulus and the frequency window;
the resulting majorant is fixed before any later cube-free modulus sum.
The required Smith bound is proved without unproved literature inputs. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubeFullResidueMajorant
open MvPolynomial HessianTheorem11 CubeFullSmithParameters
open IntegerResidueClasses (residue)
open CubefullSmithWeightLocal (omega)
open scoped BigOperators

/-- The finite-window majorant has exactly the unnormalised mass used
in Plan Alpha (4.3). No periodicity of the complete sum is assumed. -/
theorem exists_uniform_bound 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (η : ℝ) (hη : 0 < η) :
    ∃ p₀ : ℕ, 3 ≤ p₀ ∧ ∀ r : ℕ, 0 < r → CubeFull r →
      (∀ p ∈ r.primeFactors, p₀ ≤ p) →
      ∀ V : Finset (Fin 10 → ℤ),
      ∃ P : (Fin 10 → ZMod (A r)) → ℝ, (∀ b, 0 ≤ P b) ∧
        (∀ v ∈ V, ‖completeCubicSum F r v‖ ≤ P (residue (A r) v)) ∧
        (∑ b, P b) ≤ (r : ℝ)^(10+η)*omega r := by
  obtain ⟨p₀,hp₀,hbound⟩ := CubeFullSmithBound.exists_uniform_bound
     F hF hAn η hη
  refine ⟨p₀,hp₀,?_⟩
  intro r hr hc helig V
  apply ResidueMajorantExtraction.exists_majorant (A r) V
    (fun v => ‖completeCubicSum F r v‖) ((r : ℝ)^(10+η)*omega r)
    (fun _ _ => norm_nonneg _) (by unfold omega; positivity)
  intro U _
  simpa only [one_mul,omega,mul_assoc] using
    hbound r hr hc helig U (fun _ => 1) (fun _ _ => zero_le_one)

/-- Combine an actual localized-factor majorant with the Smith majorant.
The resulting product majorant depends on the fixed factors and frequency
set, but has no dependence on a later cube-free factor. -/
theorem exists_mixed_majorant 
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F)) (η : ℝ) (hη : 0 < η) :
    ∃ p₀ : ℕ, 3 ≤ p₀ ∧ ∀ r : ℕ, 0 < r → CubeFull r →
      (∀ p ∈ r.primeFactors, p₀ ≤ p) →
      ∀ (V : Finset (Fin 10 → ℤ)) (g W a : ℕ) [NeZero a],
      ∀ (Ω : Set (Fin 10 → ZMod W)) (Pg : (Fin 10 → ZMod a) → ℝ),
      a.Coprime (A r) → (∀ b, 0 ≤ Pg b) →
      (∀ v ∈ V, ‖localizedCompleteCubicSum F g W Ω v‖ ≤ Pg (residue a v)) →
      ∃ P : (Fin 10 → ZMod (a*A r)) → ℝ, (∀ b, 0 ≤ P b) ∧
        (∀ v ∈ V, PlanAlphaMixedWeight.weight F g W Ω r v ≤
          P (residue (a*A r) v)) ∧
        (∑ b, P b) ≤ (∑ b, Pg b)*((r : ℝ)^(10+η)*omega r) := by
  obtain ⟨p₀,hp₀,hbound⟩ := exists_uniform_bound  F hF hAn η hη
  refine ⟨p₀,hp₀,?_⟩
  intro r hr hc helig V g W a ha Ω Pg hcop hPg hmajor
  obtain ⟨Pr,hPr,hdom,hmass⟩ := hbound r hr hc helig V
  refine ⟨ResidueMajorantCRT.product hcop Pg Pr,
    ResidueMajorantCRT.product_nonneg hcop Pg Pr hPg hPr,?_,?_⟩
  · exact ResidueMajorantCRT.product_majorizes hcop Pg Pr V
      (fun v => ‖localizedCompleteCubicSum F g W Ω v‖)
      (fun v => ‖completeCubicSum F r v‖)
      (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hmajor hdom
  · exact ResidueMajorantCRT.product_mass_le hcop Pg Pr hPg hPr
      (∑ b, Pg b) ((r : ℝ)^(10+η)*omega r) le_rfl hmass

end CubicTenVariables.CubeFullResidueMajorant
