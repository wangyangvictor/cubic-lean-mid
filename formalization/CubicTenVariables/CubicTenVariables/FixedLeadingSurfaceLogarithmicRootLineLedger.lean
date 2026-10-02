import CubicTenVariables.FixedLeadingSurfaceNormalizedLinePrefix
import CubicTenVariables.FixedLeadingSurfacePersistentRootDegreeSplit
import CubicTenVariables.FixedLeadingSurfaceSingularCount

/-!
# Root lines in the normalized fixed-leading line ledger

Stable geometric root lines descend to rational components of the exact root
cut; nonstable lines contribute at most one rational point each.  This file
combines that descent with the existing Heath--Brown fixed-ternary line
estimate and the root Bezout degree cap.
-/

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceLogarithmicRootLineLedger

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedLinePrefix
open FixedLeadingSurfaceResidualLinePrefix
open FixedLeadingSurfacePersistentRootDegreeSplit
open FixedLeadingSurfaceSingularCount
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- One uniform fixed-leading constant bounds the actual degree-one root-cell
union.  The first term is the root Bezout occurrence mass; the last term is
the one-point allowance for each nonstable geometric line. -/
theorem exists_uniform_normalized_rootLine_contribution
    (hConjugate :
      StandardAG.QbarConjugatePreservesProjectiveDimensionDegree)
    (lineCurveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d)
    (k : MvPolynomial (Fin 3) ℤ) (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (a b : ℤ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
      g.totalDegree ≤ d →
      map (Int.castRingHom ℚ) (homogeneousComponent d g) =
        C c * map (Int.castRingHom ℚ) k →
      let F := projectiveEquiv a b (homogenize d g)
      let sourceEquations : Finset (MvPolynomial (Fin 4) ℚ) :=
        {map (Int.castRingHom ℚ) F}
      ∀ (G₀ : MvPolynomial (Fin 4) ℚ) (e₀ Lroot : ℕ),
      G₀.IsHomogeneous e₀ →
      G₀ ∉ Ideal.span {map (Int.castRingHom ℚ) F} →
      e₀ ≤ Lroot →
      ∀ (degree : Ideal (MvPolynomial (Fin 4) Qbar) → ℕ),
      (∀ Q ∈ finiteEquationMinimalPrimes
          (qbarSurfaceCutEquationFamily sourceEquations G₀),
        Q.IsPrime ∧
        Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar) ∧
        HasProjectiveDimensionDegree Q 1 (degree Q)) →
      ∀ (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          Finset (IntVector 3)),
      let active := activeQbarPersistentRootComponentOptions
        sourceEquations G₀ cell
      active.card ≤ d * Lroot →
      (∀ o ∈ active, ∀ z ∈ cell o,
        selectedFiniteEquationComponent
          (qbarSurfaceCutEquationFamily sourceEquations G₀)
          (fun i ↦ (progressionHomogeneousPoint 0 1 z i : Qbar)) = o) →
      ∀ H : ℕ, 1 ≤ H →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ i,
        |integralAffineMap 0 z 1 i| ≤ (H : ℤ)) →
      ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
        ((d * Lroot : ℕ) : ℝ) ^ 2 +
          A * (H : ℝ) ^ (1 + epsilon) +
          ((d * Lroot : ℕ) : ℝ) := by
  classical
  obtain ⟨A, hA, hline⟩ :=
    exists_uniform_normalized_prefix_linear_contribution lineCurveCount
      hd k hk hirr a b epsilon hepsilon
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop
  dsimp only
  let F := projectiveEquiv a b (homogenize d g)
  let sourceEquations : Finset (MvPolynomial (Fin 4) ℚ) :=
    {map (Int.castRingHom ℚ) F}
  intro G₀ e₀ Lroot hG₀hom hG₀proper he₀ degree hrootData cell
  let active := activeQbarPersistentRootComponentOptions
    sourceEquations G₀ cell
  intro hactive hselected H hH hbox
  obtain ⟨_hne, hFhom, _hprime, _hdim⟩ :=
    normalized_surface_certificate (by omega : 0 < d) a b g hdegree
      (irreducible_actual_top k g c hirr hc htop)
  have hsourceHom : (finiteEquationIdeal sourceEquations).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ) := by
    have hspan : (Ideal.span {map (Int.castRingHom ℚ) F}).IsHomogeneous
        (homogeneousSubmodule (Fin 4) ℚ) := by
      apply Ideal.homogeneous_span
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact ⟨d, hFhom.map _⟩
    simpa [sourceEquations, finiteEquationIdeal] using hspan
  have hdescent :=
    persistentRootLinePointUnion_card_le_rationalLedger_add_active
      hConjugate sourceEquations hsourceHom G₀ hG₀hom degree hrootData cell
      0 1 (by decide) hselected
  have hlineBound := hline g c hc hdegree htop active
    (fun _ ↦ e₀) (fun _ ↦ G₀)
    (by
      intro _ _
      exact ⟨hG₀hom, hG₀proper⟩)
    0 1 cell H hH hbox
  have hoccurrence : (∑ _o ∈ active, d * e₀) ≤
      d ^ 2 * Lroot * Lroot :=
    degreeSum_le_twoCap active (fun _ ↦ e₀) d Lroot Lroot hactive
      (fun _ _ ↦ he₀)
  have hoccurrenceReal :
      (((∑ _o ∈ active, d * e₀ : ℕ) : ℝ)) ≤
        ((d * Lroot : ℕ) : ℝ) ^ 2 := by
    calc
      (((∑ _o ∈ active, d * e₀ : ℕ) : ℝ)) ≤
          ((d ^ 2 * Lroot * Lroot : ℕ) : ℝ) := by exact_mod_cast hoccurrence
      _ = ((d * Lroot : ℕ) : ℝ) ^ 2 := by
        norm_num [pow_two]
        ring
  have hactiveReal : (active.card : ℝ) ≤ ((d * Lroot : ℕ) : ℝ) := by
    exact_mod_cast hactive
  have hlineBound' := hlineBound.trans
    (add_le_add hoccurrenceReal le_rfl)
  have hlineBound'' :
      ((quantitativePrefixPersistentRationalLinearPointUnion
        (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
          0 1 cell).card : ℝ) ≤
        ((d * Lroot : ℕ) : ℝ) ^ 2 +
          A * (H : ℝ) ^ (1 + epsilon) := by
    simpa [sourceEquations, F, finiteEquationIdeal] using hlineBound'
  calc
    ((persistentRootLinePointUnion degree active cell).card : ℝ) ≤
        ((quantitativePrefixPersistentRationalLinearPointUnion
          (finiteEquationIdeal sourceEquations) active (fun _ ↦ G₀)
            0 1 cell).card : ℝ) + active.card := hdescent
    _ ≤ (((d * Lroot : ℕ) : ℝ) ^ 2 +
          A * (H : ℝ) ^ (1 + epsilon)) +
          ((d * Lroot : ℕ) : ℝ) := add_le_add hlineBound'' hactiveReal
    _ = ((d * Lroot : ℕ) : ℝ) ^ 2 +
          A * (H : ℝ) ^ (1 + epsilon) +
          ((d * Lroot : ℕ) : ℝ) := rfl

end CubicTenVariables.FixedLeadingSurfaceLogarithmicRootLineLedger
