import CubicTenVariables.FixedLeadingSurfaceResidualLineContribution
import CubicTenVariables.FixedLeadingSurfaceCoefficientReduction

/-!
# The literal persistent-prefix line remainder

The actual rational line union is bounded by the proved Bézout degree
ledger plus the uniform fixed-leading line contribution. Membership in
every affine section follows by dehomogenizing the actual surface
equation. For the principal homogenized surface, its prime, homogeneous,
dimension and degree certificates are proved from the fixed leading form.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceResidualLinePrefix

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingSurfaceCoordinateTransport FixedLeadingSurfaceSingularCount
open FixedLeadingSurfaceResidualLineContribution FixedLeadingSurfaceCoefficientReduction
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous surface equation belongs to every projective
section; its dehomogenization is the literal integral affine equation. -/
theorem affine_equation_mem_rational_section
    {d : ℕ} (g : MvPolynomial (Fin 3) ℤ) (hdegree : g.totalDegree ≤ d)
    (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hsource : map (Int.castRingHom ℚ) (homogenize d g) ∈ I)
    (G : MvPolynomial (Fin 4) ℚ) :
    map (Int.castRingHom ℚ) g ∈ rationalAffineChartIntersectionIdeal I G := by
  have hmem := Ideal.mem_map_of_mem (standardDehomogenizationHom ℚ 3)
    (show map (Int.castRingHom ℚ) (homogenize d g) ∈ I ⊔ Ideal.span {G} from
      (show I ≤ I ⊔ Ideal.span {G} from le_sup_left) hsource)
  rw [map_homogenize, standardDehomogenizationHom_homogenize d _
    ((Finset.sup_mono (support_map_subset _ _)).trans hdegree)] at hmem
  exact hmem

/-- The point union and degree ledger are the existing literal prefix
objects. The constant precedes every auxiliary cut and cell family. -/
theorem exists_uniform_prefix_linear_contribution
    (curveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ)
    (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
      ∀ (I : Ideal (MvPolynomial (Fin 4) ℚ)), I.IsPrime →
        I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ) →
        HasProjectiveDimensionDegree I 2 d →
        map (Int.castRingHom ℚ) (homogenize d g) ∈ I →
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
  classical
  obtain ⟨A, hA, hbound⟩ :=
    exists_uniform_residual_linear_contribution curveCount hd k hk hirr ε hε
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop I hprime hhom hdim hsource
    active terminalDegree terminalCut hterminal u m cell B hB hbox
  let J := fun o : {o // o ∈ active} ↦
    rationalAffineChartIntersectionIdeal I (terminalCut o.1)
  let X := fun o : {o // o ∈ active} ↦
    quantitativePrefixPersistentAffineCell u m cell o.1
  have hsurface : ∀ o, map (Int.castRingHom ℚ) g ∈ J o :=
    fun o ↦ affine_equation_mem_rational_section g hdegree I hsource (terminalCut o.1)
  have hboxX : ∀ o, ∀ z ∈ X o, ∀ j, |z j| ≤ (B : ℤ) := by
    intro o z hz j
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hbox o.1 o.2 w hw j
  have hcount := hbound g c hc hdegree htop {o // o ∈ active} J X hsurface B hB hboxX
  have hledger : (∑ o : {o // o ∈ active},
      ((rationalLinearAffineComponents (J o)).card : ℝ)) ≤
      ((∑ o ∈ active, d * terminalDegree o : ℕ) : ℝ) := by
    have h := card_quantitativePrefixPersistent_rationalOccurrences_le_degreeSum
      I hprime hhom hdim active terminalDegree terminalCut hterminal
    rw [card_rationalLinearOccurrence] at h
    exact_mod_cast h
  rw [quantitativePrefixPersistentRationalLinearPointUnion_eq_underlying]
  exact hcount.trans (add_le_add hledger le_rfl)

/-- Principal-surface specialization. The defining ideal, chart equation,
and projective surface certificates are all supplied by the actual g.
Only properness and the displayed degrees of the actual terminal cuts
remain as cut data. -/
theorem exists_uniform_homogenized_prefix_linear_contribution
    (curveCount : Literature.HeathBrown2002FixedTernaryPrimitiveCount)
    {d : ℕ} (hd : 2 ≤ d) (k : MvPolynomial (Fin 3) ℤ)
    (hk : k.IsHomogeneous d)
    (hirr : IsAbsolutelyIrreducible (map (Int.castRingHom ℚ) k))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 → g.totalDegree ≤ d →
        map (Int.castRingHom ℚ) (homogeneousComponent d g) =
          C c * map (Int.castRingHom ℚ) k →
      let I := Ideal.span {map (Int.castRingHom ℚ) (homogenize d g)}
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
  obtain ⟨A, hA, hbound⟩ :=
    exists_uniform_prefix_linear_contribution curveCount hd k hk hirr ε hε
  refine ⟨A, hA, ?_⟩
  intro g c hc hdegree htop
  dsimp only
  obtain ⟨_hne, hFhom, hprime, hdim⟩ :=
    homogenized_surface_certificate (by omega : 0 < d) g hdegree
      (irreducible_actual_top k g c hirr hc htop)
  have hhom : (Ideal.span {map (Int.castRingHom ℚ) (homogenize d g)}).IsHomogeneous
      (homogeneousSubmodule (Fin 4) ℚ) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨d, hFhom.map _⟩
  exact hbound g c hc hdegree htop _ hprime hhom hdim
    (Ideal.subset_span (Set.mem_singleton _))

/-- The exact degree sum has the two-cap bound used by the survivor
construction. This bound is proved from its actual number of active
labels and individual terminal-cut degrees. -/
theorem degreeSum_le_twoCap
    {α : Type*} [DecidableEq α] (active : Finset α)
    (terminalDegree : α → ℕ) (d Lroot Lterminal : ℕ)
    (hroot : active.card ≤ d * Lroot)
    (hterminal : ∀ o ∈ active, terminalDegree o ≤ Lterminal) :
    (∑ o ∈ active, d * terminalDegree o) ≤ d ^ 2 * Lroot * Lterminal := by
  calc
    _ ≤ ∑ _o ∈ active, d * Lterminal := by
      apply Finset.sum_le_sum
      intro o ho
      exact Nat.mul_le_mul_left d (hterminal o ho)
    _ = active.card * (d * Lterminal) := by simp
    _ ≤ (d * Lroot) * (d * Lterminal) := Nat.mul_le_mul_right _ hroot
    _ = _ := by ring

end CubicTenVariables.FixedLeadingSurfaceResidualLinePrefix
