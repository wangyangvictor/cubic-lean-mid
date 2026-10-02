import TranslatedDepthSeven.BoundedAffineProjectionMatricesInternal
import TranslatedDepthSeven.BoundedSimultaneousPrimitiveCoordinateInternal

/-!
# A fixed matrix menu for simultaneous source--boundary projections

The distinguished normalization rows retain their existing bound
`(D+1)^N`.  The common primitive row supplied by
`exists_bounded_nat_simultaneous_linearCombination_primitive_element` has
entries at most `(2*D*D+1)^(N+1)`.  Placing both bounds in one integer box
gives a finite menu chosen before either variety or coefficient field.
-/

namespace TranslatedDepthSeven
noncomputable section

open MvPolynomial Matrix StandardAG

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

/-- Fixed integer box large enough for a distinguished normalization and
one primitive row common to two extensions of degree at most `D`. -/
def boundedIntegralSimultaneousAffineProjectionMatrices (N r D : ℕ) :
    Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) :=
  Fintype.piFinset fun _ : Fin (r + 2) ↦
    Fintype.piFinset fun _ : Fin (N + 1) ↦
      Finset.Icc
        (-(max ((D + 1) ^ N) ((2 * D * D + 1) ^ (N + 1)) : ℕ) : ℤ)
        ((max ((D + 1) ^ N) ((2 * D * D + 1) ^ (N + 1)) : ℕ) : ℤ)

/-- Inserting a common bounded primitive row into a matrix from the
distinguished normalization menu lands in the fixed simultaneous menu. -/
theorem primitiveAffineProjectionMatrix_mem_boundedIntegralSimultaneousAffineProjectionMatrices
    {N r D : ℕ} (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralDistinguishedNormalizationMatrices N r D)
    (c : Fin (N + 1) → ℕ)
    (hc : ∀ j, c j ≤ (2 * D * D + 1) ^ (N + 1)) :
    primitiveAffineProjectionMatrix A c ∈
      boundedIntegralSimultaneousAffineProjectionMatrices N r D := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  have hentry (k : Fin (r + 1)) :
      -(((D + 1) ^ N : ℕ) : ℤ) ≤ A k j ∧
        A k j ≤ (((D + 1) ^ N : ℕ) : ℤ) :=
    Finset.mem_Icc.mp
      (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hA k) j)
  dsimp only [primitiveAffineProjectionMatrix]
  generalize Equiv.swap (0 : Fin (r + 2)) 1 i = k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cases_zero]
    have hh : (c j : ℤ) ≤ (((2 * D * D + 1) ^ (N + 1) : ℕ) : ℤ) := by
      exact_mod_cast hc j
    have hmax : (((2 * D * D + 1) ^ (N + 1) : ℕ) : ℤ) ≤
        ((max ((D + 1) ^ N) ((2 * D * D + 1) ^ (N + 1)) : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_max_right ((D + 1) ^ N)
        ((2 * D * D + 1) ^ (N + 1))
    constructor <;> omega
  · simp only [Fin.cases_succ]
    obtain ⟨hl, hu⟩ := hentry k
    have hmax : (((D + 1) ^ N : ℕ) : ℤ) ≤
        ((max ((D + 1) ^ N) ((2 * D * D + 1) ^ (N + 1)) : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_max_left ((D + 1) ^ N)
        ((2 * D * D + 1) ^ (N + 1))
    constructor <;> omega

end
end TranslatedDepthSeven
