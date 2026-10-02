import TranslatedDepthSeven.ProjectiveCurveSeparatorBridgeInternal

/-! The actual, possibly nonreduced affine coordinate charts of a proper
projective curve section are finite-dimensional. No radical is inserted. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ProjectiveCurveSectionChartFinite
open MvPolynomial TranslatedDepthSeven Published

variable {K : Type*} [Field K]

/-- An eventual homogeneous Hilbert bound makes the literal dehomogeneous
quotient finite, without requiring the section to be prime or reduced. -/
theorem finite_of_eventual_hilbert_bound {n d : ℕ}
    (T : Ideal (MvPolynomial (Option (Fin n)) K)) (k₀ : ℕ)
    (hbound : ∀ k ≥ k₀,
      Module.finrank K (quotientHomogeneousComponent K (Option (Fin n)) T k) ≤ d) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸
      T.map multivariateDehomogenization.toRingHom) := by
  obtain ⟨v, hv⟩ := exists_affineQuotient_spanningFamily_of_eventual_bounded_hilbert
    (T.map multivariateDehomogenization.toRingHom) k₀
    (fun k hk => (finrank_affine_dehomogenization_le_projective T).trans (hbound k hk))
  rw [Module.finite_def, ← hv]
  exact Submodule.fg_span (Set.finite_range v)

/-- Every coordinate chart of a proper hyperplane section of a prime curve
has finite coordinate algebra. The displayed variable equivalence selects
the chart sent to `none`. The quotient is not replaced by its radical. -/
theorem finite_curve_hyperplane_chart {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N+1)) K))
    (hI : I.IsPrime) (hdegree : HasProjectiveDimensionDegree I 1 d)
    (L : MvPolynomial (Fin (N+1)) K) (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (e : Fin (N+1) ≃ Option (Fin N)) :
    Module.Finite K (MvPolynomial (Fin N) K ⧸
      ((I ⊔ Ideal.span {L}).map (renameEquiv K e)).map
        multivariateDehomogenization.toRingHom) := by
  obtain ⟨k₀, hb⟩ := eventual_finrank_projectiveCurve_hypersurface_le_over
    I hI hdegree L hLhom hL
  apply finite_of_eventual_hilbert_bound _ k₀ (d := d)
  intro k hk
  rw [← finrank_quotientHomogeneousComponent_map_renameEquiv K e (I ⊔ Ideal.span {L}) k]
  simpa only [Nat.mul_one] using hb k hk

end CubicTenVariables.ProjectiveCurveSectionChartFinite
