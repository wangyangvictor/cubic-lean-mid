import CubicTenVariables.GaussTerminalBound

/-!
A smooth point in the literal section-singularity fiber is an actual
Gauss-graph generator. Consequently every closed irreducible subset of
that section fiber meeting the ambient smooth locus lies in the closed
Gauss fiber. The polynomial equation is retained throughout; no
homogeneity, generic smoothness, or properness input is needed for this
direction of comparison.
-/

noncomputable section
namespace CubicTenVariables.GaussSectionComparison
open MvPolynomial HessianTheorem11
open TerminalSectionIncidence AffineProductGeometry

/-- Literal proportionality and an inverse scalar give an actual graph
generator, before taking its closure. -/
theorem mem_gaussFiber_of_section_mem_of_gradient_ne_zero {n : ℕ}
    (F : GeometricPolynomial n) (v : GeometricPoint n) (hv : v ≠ 0)
    (x : GeometricPoint n) (hx : x ∈ sectionSingularFiber F v)
    (hg : gradient F x ≠ 0) : x ∈ GaussTerminalBound.fiber F v := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    ((minors_iff_mem_span v (gradient F x) hv).mp hx.2.2)
  have ha0 : a ≠ 0 := by
    intro hz
    apply hg
    rw [← ha, hz, zero_smul]
  change join x v ∈ geometricClosure
    (polynomialMap (GaussGraph.parametrization F) '' GaussGraph.source F)
  apply subset_geometricClosure
  rw [GaussGraph.image_eq_literal]
  refine ⟨x, hx.1, a⁻¹, ?_⟩
  rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

/-- Every nonempty ambient-smooth open of a closed irreducible section
subset is dense, so closedness of the actual Gauss fiber gives the full
subset conclusion. -/
theorem subset_gaussFiber_of_meets_smooth {n : ℕ}
    (F : GeometricPolynomial n) (v : GeometricPoint n) (hv : v ≠ 0)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (hsub : Z ⊆ sectionSingularFiber F v)
    (hne : ∃ x ∈ Z, gradient F x ≠ 0) : Z ⊆ GaussTerminalBound.fiber F v := by
  let O := Z \ BibleHyperplanes.singularCone F
  have hopen : RelativelyOpenSet Z O :=
    ⟨BibleHyperplanes.singularCone F, BibleHyperplanes.singularCone_closed F, rfl⟩
  have hnonempty : O.Nonempty := by
    obtain ⟨x, hx, hg⟩ := hne
    exact ⟨x, hx, hg⟩
  have hdense := hopen.dense_of_nonempty hZ hiZ hnonempty
  have hO : O ⊆ GaussTerminalBound.fiber F v := by
    intro x hx
    exact mem_gaussFiber_of_section_mem_of_gradient_ne_zero F v hv x
      (hsub hx.1) hx.2
  rw [← hdense]
  exact geometricClosure_subset_closed hO (GaussTerminalBound.fiber_closed F v)

/-- The exact component dichotomy needed in the geometric terminal bound:
either the whole component lies in the Gauss fiber, or the ambient
gradient vanishes at every point of it. -/
theorem subset_gaussFiber_or_gradient_zero {n : ℕ}
    (F : GeometricPolynomial n) (v : GeometricPoint n) (hv : v ≠ 0)
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hiZ : GeometricallyIrreducible Z) (hsub : Z ⊆ sectionSingularFiber F v) :
    Z ⊆ GaussTerminalBound.fiber F v ∨ ∀ x ∈ Z, gradient F x = 0 := by
  by_cases hne : ∃ x ∈ Z, gradient F x ≠ 0
  · exact Or.inl (subset_gaussFiber_of_meets_smooth F v hv Z hZ hiZ hsub hne)
  · exact Or.inr (by simpa only [not_exists, not_and, not_not] using hne)

end CubicTenVariables.GaussSectionComparison
