import CubicTenVariables.DegreeTwoEightPlane
import CubicTenVariables.ConePlaneMomentDecay

/-! The exact low-degree cone moment limit for degrees one and two,
without a projective degree-span premise. This is the arithmetic input to
the first two microlocal promotion levels. The plane-curve Weil bound remains
an explicit input; no sheaf or trace dichotomy is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.DegreeTwoConeMomentDecay
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven Filter
open scoped BigOperators Classical Topology
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev modelIdeal {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))

theorem exists_decay
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d : ℕ)
    (hprime : (modelIdeal G).IsPrime)
    (hgeometric : ((modelIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (modelIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (modelIdeal G) r d)
    (hsmall : r+d ≤ 8) (hd : d ≤ 2) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ∀ (K : ℕ → Type) [∀ a, Field (K a)] [∀ a, Fintype (K a)]
        [∀ a, CharP (K a) p]
        (ψ : ∀ a, AddChar (K a) ℂ) (U : ∀ a, Finset (Fin 10 → K a)),
        (∀ a, 1 ≤ a → Fintype.card (K a) = p^a) →
        (∀ a, 1 ≤ a → ψ a ≠ 1) →
        (∀ a, 1 ≤ a → ∀ v ∈ U a, ∀ i,
          eval v (map (Int.castRingHom (K a)) (G i)) = 0) →
        Tendsto (fun a =>
          (∑ v ∈ U a, ‖normalizedFourierSum (ψ a) (map (Int.castRingHom (K a)) F) v‖^2) /
            (p : ℝ)^(a*18)) atTop (𝓝 0) := by
  obtain ⟨B,_hrank,hB,hrows⟩ := DegreeTwoEightPlane.exists_integral_rows
    (modelIdeal G) r d
    hprime hgeometric hhom hdegree hsmall hd
  exact ConePlaneMomentDecay.exists_decay weil F hF hAn G B hB hrows

end CubicTenVariables.DegreeTwoConeMomentDecay
