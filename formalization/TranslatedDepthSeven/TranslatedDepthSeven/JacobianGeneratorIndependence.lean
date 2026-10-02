import TranslatedDepthSeven.DepthSevenJacobianCharts

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

universe u

variable {k : Type u} [Field k]

def polynomialGradientAt {N : ℕ} (z : Fin N → k)
    (f : MvPolynomial (Fin N) k) : Fin N → k :=
  fun j ↦ MvPolynomial.eval z (MvPolynomial.pderiv j f)

/-- At a common zero, the gradient of every member of the generated ideal
lies in the linear span of the gradients of the displayed generators. -/
theorem polynomialGradientAt_mem_span_of_mem_idealSpan
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) k))
    (z : Fin N → k)
    (hz : z ∈ finiteAffineCommonZeroLocus equations)
    {f : MvPolynomial (Fin N) k}
    (hf : f ∈ Ideal.span (equations : Set (MvPolynomial (Fin N) k))) :
    polynomialGradientAt z f ∈
      Submodule.span k (polynomialGradientAt z '' (equations : Set _)) := by
  let S := Submodule.span k
    (polynomialGradientAt z '' (equations : Set (MvPolynomial (Fin N) k)))
  have hboth : ∀ g ∈ Ideal.span
      (equations : Set (MvPolynomial (Fin N) k)),
      MvPolynomial.eval z g = 0 ∧ polynomialGradientAt z g ∈ S := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        exact ⟨hz g hg, Submodule.subset_span ⟨g, hg, rfl⟩⟩
    | zero =>
        refine ⟨by simp, ?_⟩
        change (0 : Fin N → k) ∈ S
        exact S.zero_mem
    | add g h _ _ hg hh =>
        refine ⟨by simp [hg.1, hh.1], ?_⟩
        have heq : polynomialGradientAt z (g + h) =
            polynomialGradientAt z g + polynomialGradientAt z h := by
          funext j
          simp [polynomialGradientAt]
        rw [heq]
        exact S.add_mem hg.2 hh.2
    | smul a g _ hg =>
        refine ⟨by simp [hg.1], ?_⟩
        change polynomialGradientAt z (a * g) ∈ S
        have heq : polynomialGradientAt z (a * g) =
            (MvPolynomial.eval z a) • polynomialGradientAt z g := by
          funext j
          simp [polynomialGradientAt, hg.1]
        rw [heq]
        exact S.smul_mem _ hg.2
  exact (hboth f hf).2

/-- Two finite families generating the same ideal have exactly the same
Jacobian row span at every common zero. -/
theorem polynomialGradientSpan_eq_of_idealSpan_eq
    {N : ℕ} (E₁ E₂ : Finset (MvPolynomial (Fin N) k))
    (z : Fin N → k)
    (hz₁ : z ∈ finiteAffineCommonZeroLocus E₁)
    (hz₂ : z ∈ finiteAffineCommonZeroLocus E₂)
    (hspan : Ideal.span (E₁ : Set (MvPolynomial (Fin N) k)) =
      Ideal.span (E₂ : Set (MvPolynomial (Fin N) k))) :
    Submodule.span k (polynomialGradientAt z '' (E₁ : Set _)) =
      Submodule.span k (polynomialGradientAt z '' (E₂ : Set _)) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨f, hf, rfl⟩
    apply polynomialGradientAt_mem_span_of_mem_idealSpan E₂ z hz₂
    rw [← hspan]
    exact Ideal.subset_span hf
  · rintro _ ⟨f, hf, rfl⟩
    apply polynomialGradientAt_mem_span_of_mem_idealSpan E₁ z hz₁
    rw [hspan]
    exact Ideal.subset_span hf

theorem range_finiteEquationJacobianRowAt_eq_gradientImage
    {N : ℕ} (E : Finset (MvPolynomial (Fin N) k)) (z : Fin N → k) :
    Set.range (finiteEquationJacobianRowAt E z) =
      polynomialGradientAt z '' (E : Set _) := by
  ext v
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.1, f.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

/-- The rank-at-most-six locus is independent of the chosen finite
generating family, at common zeroes of the generated ideal. -/
theorem rankAtMostSix_iff_of_idealSpan_eq
    {N : ℕ} (E₁ E₂ : Finset (MvPolynomial (Fin N) k))
    (z : Fin N → k)
    (hz₁ : z ∈ finiteAffineCommonZeroLocus E₁)
    (hz₂ : z ∈ finiteAffineCommonZeroLocus E₂)
    (hspan : Ideal.span (E₁ : Set (MvPolynomial (Fin N) k)) =
      Ideal.span (E₂ : Set (MvPolynomial (Fin N) k))) :
    IsDepthSevenJacobianRankAtMostSix E₁ z ↔
      IsDepthSevenJacobianRankAtMostSix E₂ z := by
  rw [isDepthSevenJacobianRankAtMostSix_iff_finrank_le,
    isDepthSevenJacobianRankAtMostSix_iff_finrank_le,
    range_finiteEquationJacobianRowAt_eq_gradientImage,
    range_finiteEquationJacobianRowAt_eq_gradientImage,
    polynomialGradientSpan_eq_of_idealSpan_eq E₁ E₂ z hz₁ hz₂ hspan]

end

end TranslatedDepthSeven
