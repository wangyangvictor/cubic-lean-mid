import CubicTenVariables.FixedLeadingSurfaceResidualLinePrefix

/-! The actual line bound in the same fixed coordinates as the determinant
auxiliaries. The curve-count constant depends on the transformed fixed
leading form and precedes every varying surface equation. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceNormalizedLinePrefix

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateChoice FixedLeadingSurfaceCoordinateTransport
open FixedLeadingSurfaceNormalizedPrimeCount FixedLeadingSurfaceResidualLinePrefix
open scoped BigOperators

theorem absolutelyIrreducible_coordinateEquiv
    (a b : ℤ) (k : MvPolynomial (Fin 3) ℤ)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k)) :
    IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) (coordinateEquiv a b k)) := by
  unfold IsAbsolutelyIrreducible at hirr ⊢
  rw [map_coordinateEquiv, map_coordinateEquiv]
  exact hirr.map (coordinateEquiv
    (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)))

theorem scalar_top_coordinateEquiv
    (a b : ℤ) {d : ℕ} (g k : MvPolynomial (Fin 3) ℤ) (c : ℚ)
    (htop : map (Int.castRingHom ℚ) (homogeneousComponent d g) =
      C c * map (Int.castRingHom ℚ) k) :
    map (Int.castRingHom ℚ) (homogeneousComponent d (coordinateEquiv a b g)) =
      C c * map (Int.castRingHom ℚ) (coordinateEquiv a b k) := by
  rw [map_homogeneousComponent_boundary, map_coordinateEquiv, map_coordinateEquiv]
  apply scalar_leading_form_coordinateEquiv
  rw [← map_homogeneousComponent_boundary]
  exact htop

theorem exists_uniform_normalized_prefix_linear_contribution
    (curveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ)
    (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (a b : ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
      let I := Ideal.span {map (Int.castRingHom ℚ)
        (projectiveEquiv a b (homogenize d g))}
      ∀ (active : Finset (Option (Ideal (MvPolynomial (Fin 4) Qbar))))
        (terminalDegree : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → ℕ)
        (terminalCut : Option (Ideal (MvPolynomial (Fin 4) Qbar)) →
          MvPolynomial (Fin 4) ℚ),
      (∀ o ∈ active, (terminalCut o).IsHomogeneous (terminalDegree o) ∧
        terminalCut o ∉ I) →
      ∀ (u : IntVector 3) (m : ℕ)
        (cell : Option (Ideal (MvPolynomial (Fin 4) Qbar)) → Finset (IntVector 3))
        (B : ℕ), 1 ≤ B →
      (∀ o ∈ active, ∀ z ∈ cell o, ∀ j,
        |integralAffineMap u z m j| ≤ (B : ℤ)) →
      ((quantitativePrefixPersistentRationalLinearPointUnion
        I active terminalCut u m cell).card : ℝ) ≤
        ((∑ o ∈ active, d * terminalDegree o : ℕ) : ℝ) +
          A * (B : ℝ) ^ (1 + ε) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_homogenized_prefix_linear_contribution
    curveCount hd (coordinateEquiv a b k) (coordinateEquiv_isHomogeneous a b hk)
    (absolutelyIrreducible_coordinateEquiv a b k hirr) ε hε
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop
  simpa only [integral_projectiveEquiv_homogenize] using
    hbound (coordinateEquiv a b g) c hc
      ((totalDegree_integral_coordinateEquiv_le a b g).trans hdegree)
      (scalar_top_coordinateEquiv a b g k c htop)

end CubicTenVariables.FixedLeadingSurfaceNormalizedLinePrefix
