import HessianTheorem11.ReducedComponentDimension

/-! Strict dimension drop for a proper closed subset of an irreducible affine
set, proved from quotient rings and the non-zero-divisor Krull-dimension bound.
This has no external geometric premise. -/

noncomputable section
namespace HessianTheorem11.ReducedStrictDimension
open MvPolynomial

theorem proper_closed {σ : Type} [Fintype σ]
    (A B : Set (σ → GeometricField)) (hA : AlgebraicallyClosedSet A)
    (_hB : AlgebraicallyClosedSet B) (hi : GeometricallyIrreducible B)
    (hAB : A ⊂ B) : affineDimension A < affineDimension B := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := ReducedComponentDimension.finite_dimension A hne
    obtain ⟨b, hb⟩ := ReducedComponentDimension.finite_dimension B hi.nonempty
    obtain ⟨x, hxB, hxA⟩ := Set.exists_of_ssubset hAB
    have hex : ∃ p ∈ vanishingIdeal GeometricField A, eval x p ≠ 0 := by
      by_contra h
      push_neg at h
      exact hxA (hA ▸ h)
    obtain ⟨p, hpA, hpx⟩ := hex
    let I := vanishingIdeal GeometricField B
    let J := vanishingIdeal GeometricField A
    letI : I.IsPrime := hi
    have hpI : p ∉ I := fun h => hpx (h x hxB)
    let f := Ideal.Quotient.factor (show I ≤ J from vanishingIdeal_anti_mono hAB.subset)
    have hp0 : Ideal.Quotient.mk I p ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hpI
    have hz : f (Ideal.Quotient.mk I p) = 0 := by
      rw [Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpA
    have hdim := ringKrullDim_succ_le_of_surjective f
      (Ideal.Quotient.factor_surjective _) (mem_nonZeroDivisors_of_ne_zero hp0) hz
    change affineDimension A + 1 ≤ affineDimension B at hdim
    rw [ha, hb] at hdim
    have hn : a + 1 ≤ b := by exact_mod_cast hdim
    rw [ha, hb]
    exact_mod_cast (show a < b by omega)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, affineDimension_empty]
    exact lt_of_lt_of_le (show (⊥ : Dimension) < 0 from WithBot.bot_lt_coe 0)
      (affineDimension_nonneg_of_nonempty hi.nonempty)

end HessianTheorem11.ReducedStrictDimension
