import CubicTenVariables.FiniteIncidenceDepth
import CubicTenVariables.TerminalBadParameterClosed

/-! The incidence containment needed for singular support implies the
terminal depth comparison with the already constructed section bad loci.
Only that literal incidence containment is assumed; singular-support
existence and finite-field trace estimates are not claimed. -/

noncomputable section
namespace CubicTenVariables.ConormalTerminalComparison
open HessianTheorem11
open TerminalFiberCoordinates FiniteIncidenceDepth TerminalSectionIncidence
open TerminalIntegralClosureModels

theorem pointFiber_subset_section {n : ℕ} (F : GeometricPolynomial n)
    (C : Set (GeometricPoint (n+n)))
    (hC : ∀ y ∈ C,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence F) (v : GeometricPoint n) :
    pointFiber C v ⊆ sectionSingularFiber F v := by
  intro x hx
  have h := hC (polynomialMap (fixedNormalSection v) x) hx
  simpa only [pointProjection_section, normalProjection_section] using h

theorem depth_subset_section_badNormals {n : ℕ} (F : GeometricPolynomial n)
    (C : Set (GeometricPoint (n+n)))
    (hC : ∀ y ∈ C,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence F) (t : ℕ) :
    FiberJumpDimension.largeFiberParameters (normalProjection n) C (t+1) ⊆
      TerminalBadNormals.badNormals F t := by
  rw [largeFiberParameters_eq_pointFiber]
  intro v hv
  exact hv.trans (affineDimension_mono (pointFiber_subset_section F C hC v))

/-- Outside the actual t-th section closure, the actual conormal fiber
has affine dimension at most t. Empty fibers are included. -/
theorem pointFiber_dimension_le {n : ℕ} (F : RationalPolynomial n)
    (hF : F.IsHomogeneous 3) (C : Set (GeometricPoint (n+n)))
    (hC : ∀ y ∈ C,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        affineSectionSingularIncidence (geometricPolynomial F))
    (t : ℕ) (v : GeometricPoint n) (hv : v ∉ sectionClosure F t) :
    affineDimension (pointFiber C v) ≤ (t : Dimension) := by
  have hnot : ¬ ((t+1 : ℕ) : Dimension) ≤ affineDimension (pointFiber C v) := by
    intro hlarge
    have hbad : v ∈ TerminalBadNormals.badNormals (geometricPolynomial F) t :=
      hlarge.trans (affineDimension_mono (pointFiber_subset_section _ C hC v))
    apply hv
    rw [TerminalBadParameterClosed.sectionClosure_eq_badNormals_union_origin F hF t]
    exact Or.inl hbad
  by_cases hne : (pointFiber C v).Nonempty
  · obtain ⟨d, hd⟩ := ReducedComponentDimension.finite_dimension (pointFiber C v) hne
    rw [hd] at hnot ⊢
    have hlt : d < t+1 := by exact_mod_cast lt_of_not_ge hnot
    exact_mod_cast (Nat.le_of_lt_succ hlt)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, affineDimension_empty]
    exact bot_le

end CubicTenVariables.ConormalTerminalComparison
