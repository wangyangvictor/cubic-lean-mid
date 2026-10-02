import TranslatedDepthSeven.DepthSevenNormalizedJacobianPartition

/-!
# A common fixed exceptional-height cutoff

Increasing the height bound enlarges the literal exceptional locus, hence
shrinks the translated count, its normalized form, and each fixed Jacobian
chart cell. These statements justify taking maxima of fixed cutoff exponents
before choosing epsilon or any translated parameters.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Monotonicity uses the same section matrix and geometric component. -/
theorem memDepthSevenExceptionalLocus_mono_height
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {H₁ H₂ : ℕ} (hH : H₁ ≤ H₂)
    {x : Projectivization ℚ (Fin 13 → ℚ)}
    (hx : MemDepthSevenExceptionalLocus equations H₁ x) :
    MemDepthSevenExceptionalLocus equations H₂ x := by
  obtain ⟨c, hc₁, hc₄, A, hA, hheight, P, hP, hexceptional, hxP⟩ := hx
  exact ⟨c, hc₁, hc₄, A, hA, hheight.trans hH, P, hP, hexceptional, hxP⟩

/-- The rounded height bound is monotone in its fixed natural exponent. -/
theorem exceptionalHeightCutoff_mono
    (p : Parameters) {CF₁ CF₂ : ℕ} (hCF : CF₁ ≤ CF₂) :
    ⌈p.H ^ CF₁⌉₊ ≤ ⌈p.H ^ CF₂⌉₊ := by
  apply Nat.ceil_mono
  exact pow_le_pow_right₀ (by linarith [p.five_le_H]) hCF

/-- The original translated point set decreases with the cutoff. -/
theorem depthSevenTranslatedPointFinset_antitone_cutoff
    (p : Parameters) (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {CF₁ CF₂ : ℕ} (hCF : CF₁ ≤ CF₂) :
    depthSevenTranslatedPointFinset p equations CF₂ ⊆
      depthSevenTranslatedPointFinset p equations CF₁ := by
  intro x hx
  obtain ⟨hbox, hres, hzero, hne, hlinear, hexceptional⟩ :=
    (mem_depthSevenTranslatedPointFinset_iff p equations CF₂ x).mp hx
  apply (mem_depthSevenTranslatedPointFinset_iff p equations CF₁ x).mpr
  refine ⟨hbox, hres, hzero, hne, hlinear, ?_⟩
  exact fun h ↦ hexceptional
    (memDepthSevenExceptionalLocus_mono_height equations
      (exceptionalHeightCutoff_mono p hCF) h)

/-- No assumption about the chosen base point is needed for this inclusion. -/
theorem depthSevenNormalizedDisplacementFinset_antitone_cutoff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {CF₁ CF₂ : ℕ} (hCF : CF₁ ≤ CF₂) :
    depthSevenNormalizedDisplacementFinset p x₀ equations CF₂ ⊆
      depthSevenNormalizedDisplacementFinset p x₀ equations CF₁ := by
  classical
  intro z hz
  obtain ⟨hbox, htranslated, hzero, hne, hlinear, hexceptional⟩ :=
    Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨hbox, htranslated, hzero, hne, hlinear, ?_⟩
  exact fun h ↦ hexceptional
    (memDepthSevenExceptionalLocus_mono_height equations
      (exceptionalHeightCutoff_mono p hCF) h)

/-- The Jacobian label does not depend on the exceptional-height cutoff. -/
theorem depthSevenNormalizedJacobianChartCell_antitone_cutoff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (C : IntegralDepthSevenJacobianChartIndex equations)
    {CF₁ CF₂ : ℕ} (hCF : CF₁ ≤ CF₂) :
    depthSevenNormalizedJacobianChartCell p x₀ equations CF₂ C ⊆
      depthSevenNormalizedJacobianChartCell p x₀ equations CF₁ C := by
  intro z hz
  obtain ⟨hz, hlabel⟩ :=
    (mem_depthSevenNormalizedJacobianChartCell_iff
      p x₀ equations CF₂ C z).mp hz
  exact (mem_depthSevenNormalizedJacobianChartCell_iff
    p x₀ equations CF₁ C z).mpr
      ⟨depthSevenNormalizedDisplacementFinset_antitone_cutoff
        p x₀ equations hCF hz, hlabel⟩

/-- The low-rank locus has the same cutoff monotonicity. -/
theorem depthSevenNormalizedRankAtMostSixFinset_antitone_cutoff
    (p : Parameters) (x₀ : IntVector 13)
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    {CF₁ CF₂ : ℕ} (hCF : CF₁ ≤ CF₂) :
    depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF₂ ⊆
      depthSevenNormalizedRankAtMostSixFinset p x₀ equations CF₁ := by
  classical
  intro z hz
  obtain ⟨hz, hrank⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr
    ⟨depthSevenNormalizedDisplacementFinset_antitone_cutoff
      p x₀ equations hCF hz, hrank⟩

end

end TranslatedDepthSeven
