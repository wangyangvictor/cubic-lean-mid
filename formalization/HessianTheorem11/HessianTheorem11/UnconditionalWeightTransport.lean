import HessianTheorem11.RationalDescent

/-! Quantitative support bounds depend on the actual weighted filtration,
not on its splitting or the indexing of a basis. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightOptimization
open MvPolynomial PolynomialRestriction PolynomialWeightTransport RationalDescent
variable {K : Type*} [Field K] {n m : ℕ}

theorem lowerBound_restrict (B : Matrix (Fin n) (Fin m) K)
    (v : Fin n → ℤ) (w : Fin m → ℤ)
    (hentry : ∀ i j, B i j ≠ 0 → v i ≤ w j)
    (F : MvPolynomial (Fin n) K) (a : ℤ)
    (hF : HasWeightLowerBound F v a) :
    HasWeightLowerBound (restrict B F) w a := by
  classical
  intro e he
  have expansion : restrict B F =
      ∑ d ∈ F.support, restrict B (monomial d (coeff d F)) := by
    simpa only [restrict, map_sum] using congrArg (restrict B) F.as_sum
  rw [expansion] at he
  obtain ⟨d, hd, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  exact (hF d hd).trans
    (lowerBound_restrict_monomial B v w hentry d (coeff d F) e he)

theorem transition_weights_of_flags
    (B C : Matrix (Fin n) (Fin n) K) (v w : Fin n → ℤ)
    (hB : Function.Injective B.mulVec)
    (hflags : weightFlag B v = weightFlag C w)
    (i j : Fin n) (hne : frameTransition B C hB i j ≠ 0) : v i ≤ w j := by
  by_contra hnot
  apply hne
  apply inverse_coordinate_zero_of_mem_weightFlag B hB v (w j)
  · rw [hflags]
    exact Submodule.subset_span ⟨j, le_rfl, rfl⟩
  · omega

theorem lowerBound_of_same_flag
    (F : MvPolynomial (Fin n) K) (B C : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → ℤ) (hB : Function.Injective B.mulVec)
    (hflags : weightFlag B v = weightFlag C w) (a : ℤ)
    (hF : HasWeightLowerBound (restrict B F) v a) :
    HasWeightLowerBound (restrict C F) w a := by
  have hp := lowerBound_restrict (frameTransition B C hB) v w
    (transition_weights_of_flags B C v w hB hflags) (restrict B F) a hF
  rwa [restrict_restrict, matrix_mul_frameTransition] at hp

theorem lowerBound_iff_minimumWeight (F : MvPolynomial (Fin n) K)
    (hF : F.support.Nonempty) (w : Fin n → ℤ) (a : ℤ) :
    HasWeightLowerBound F w a ↔ a ≤ minimumWeight F w := by
  classical
  simp only [minimumWeight, dif_pos hF, HasWeightLowerBound, Finset.le_inf'_iff]

theorem minimumWeight_of_same_flag
    (F : MvPolynomial (Fin n) K) (B C : Matrix (Fin n) (Fin n) K)
    (v w : Fin n → ℤ) (hB : Function.Injective B.mulVec)
    (hC : Function.Injective C.mulVec)
    (hflags : weightFlag B v = weightFlag C w)
    (hBF : (restrict B F).support.Nonempty) (hCF : (restrict C F).support.Nonempty) :
    minimumWeight (restrict B F) v = minimumWeight (restrict C F) w := by
  apply le_antisymm
  · apply (lowerBound_iff_minimumWeight _ hCF _ _).mp
    apply lowerBound_of_same_flag F B C v w hB hflags
    exact (lowerBound_iff_minimumWeight _ hBF _ _).mpr le_rfl
  · apply (lowerBound_iff_minimumWeight _ hBF _ _).mp
    apply lowerBound_of_same_flag F C B w v hC hflags.symm
    exact (lowerBound_iff_minimumWeight _ hCF _ _).mpr le_rfl

end HessianTheorem11.UnconditionalWeightOptimization
