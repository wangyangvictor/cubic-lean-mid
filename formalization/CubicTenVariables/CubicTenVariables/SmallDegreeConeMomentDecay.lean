import CubicTenVariables.DegreeSpanEightPlane
import CubicTenVariables.DegreeSpanReduction
import CubicTenVariables.RationalKernelMomentDecay
import CubicTenVariables.DegreeTwoConeMomentDecay

/-! Vanishing normalized moments on actual low-degree cone models.
The containing plane is constructed internally in degrees one and two.
Only higher degrees use the Hilbert-polynomial degree--span input;
integral ideal certificates prove containment in every permitted finite
field. The cubic second moment then rules out a positive q^18-normalized
limsup. A sheaf-theoretic trace dichotomy is still a separate obligation. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.SmallDegreeConeMomentDecay
open MvPolynomial Matrix HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven Filter
open scoped BigOperators Classical Topology
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev modelIdeal {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) :=
  Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (G i)))

theorem exists_decay
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d : ℕ)
    (hprime : (modelIdeal G).IsPrime)
    (hgeometric : ((modelIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (modelIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (modelIdeal G) r d)
    (hsmall : r+d ≤ 8) :
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
  by_cases hd : d ≤ 2
  · exact DegreeTwoConeMomentDecay.exists_decay weil F hF hAn G r d
      hprime hgeometric hhom hdegree hsmall hd
  obtain ⟨B,_hrank,hB,hrows⟩ := DegreeSpanEightPlane.exists_integral_rows degreeSpan
    (modelIdeal G) r d hprime hgeometric hhom hdegree hsmall
  exact ConePlaneMomentDecay.exists_decay weil F hF hAn G B hB hrows

end CubicTenVariables.SmallDegreeConeMomentDecay
