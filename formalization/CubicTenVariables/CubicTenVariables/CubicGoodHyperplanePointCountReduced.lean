import CubicTenVariables.CubicGoodHyperplanePointCount
import CubicTenVariables.CubicSurfacePointCountReduced

/-! The certified hyperplane induction with the isolated-conjugate surface
remainder in place of the broad surface-amplification premise. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace CubicTenVariables.CubicGoodHyperplanePointCountReduced

open MvPolynomial Literature
open CubicGoodHyperplanePointCount

/-- The reduced cubic-surface theorem supplies the four-variable base. -/
theorem surface_base
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (weil : SmoothCubicWeil) : UniformAffineCubicBound 4 := by
  obtain ⟨C,hC,hbound⟩ :=
    CubicSurfacePointCountReduced.exists_uniform_affine_bound isolated weil
  refine ⟨6, by decide, C, hC, ?_⟩
  intro K _ _ h6 F hF hGI hNC
  have h23 : (2 : K) * (3 : K) ≠ 0 := by
    rw [show (2 : K) * (3 : K) = 6 by norm_num]
    exact h6
  simpa only [show 4 - 1 = 3 by decide, show 4 - 3 = 1 by decide, pow_one] using
    hbound K F hF (mul_ne_zero_iff.mp h23).1 (mul_ne_zero_iff.mp h23).2 hGI hNC

/-- A common exceptional integer and constant for dimensions four through
nine, obtained solely by the existing certified hyperplane induction. -/
theorem exists_uniform_base_bound_through_nine
    (isolated : CubicSurfacePointCountReduced.IsolatedConjugateCubicSurfacePointCount)
    (weil : SmoothCubicWeil) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ m : ℕ, m ≤ 9 → 4 ≤ m →
        ∀ (K : Type) [Field K] [Fintype K], (N : K) ≠ 0 →
          ∀ Q : MvPolynomial (Fin m) K, Q.IsHomogeneous 3 →
            GeometricallyIntegralForm Q → GeometricallyNonconicalCubic Q →
            |(affineZeroCount Q : ℝ) - (Fintype.card K : ℝ) ^ (m-1)| ≤
              C * ((Fintype.card K : ℝ) - 1) *
                (Fintype.card K : ℝ) ^ (m-3) := by
  have h4 := surface_base isolated weil
  have h5 := succ_bound 0 h4
  have h6 := succ_bound 1 h5
  have h7 := succ_bound 2 h6
  have h8 := succ_bound 3 h7
  have h9 := succ_bound 4 h8
  obtain ⟨N4,hN4,C4,hC4,b4⟩ := h4
  obtain ⟨N5,hN5,C5,hC5,b5⟩ := h5
  obtain ⟨N6,hN6,C6,hC6,b6⟩ := h6
  obtain ⟨N7,hN7,C7,hC7,b7⟩ := h7
  obtain ⟨N8,hN8,C8,hC8,b8⟩ := h8
  obtain ⟨N9,hN9,C9,hC9,b9⟩ := h9
  let N := N4*N5*N6*N7*N8*N9
  let C := C4+C5+C6+C7+C8+C9
  refine ⟨N, by dsimp only [N]; positivity, C,
    by dsimp only [C]; linarith, ?_⟩
  intro m hm9 hm4 K _ _ hNK Q hQ hQI hQN
  have hprod :
      (N4 : K)*(N5 : K)*(N6 : K)*(N7 : K)*(N8 : K)*(N9 : K) ≠ 0 := by
    simpa only [N, Nat.cast_mul] using hNK
  have hp8 : (N4 : K)*(N5 : K)*(N6 : K)*(N7 : K)*(N8 : K) ≠ 0 :=
    (mul_ne_zero_iff.mp hprod).1
  have hN9K : (N9 : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have hp7 : (N4 : K)*(N5 : K)*(N6 : K)*(N7 : K) ≠ 0 :=
    (mul_ne_zero_iff.mp hp8).1
  have hN8K : (N8 : K) ≠ 0 := (mul_ne_zero_iff.mp hp8).2
  have hp6 : (N4 : K)*(N5 : K)*(N6 : K) ≠ 0 :=
    (mul_ne_zero_iff.mp hp7).1
  have hN7K : (N7 : K) ≠ 0 := (mul_ne_zero_iff.mp hp7).2
  have hp5 : (N4 : K)*(N5 : K) ≠ 0 := (mul_ne_zero_iff.mp hp6).1
  have hN6K : (N6 : K) ≠ 0 := (mul_ne_zero_iff.mp hp6).2
  have hN4K : (N4 : K) ≠ 0 := (mul_ne_zero_iff.mp hp5).1
  have hN5K : (N5 : K) ≠ 0 := (mul_ne_zero_iff.mp hp5).2
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  have hcases : m=4 ∨ m=5 ∨ m=6 ∨ m=7 ∨ m=8 ∨ m=9 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (b4 K hN4K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C4 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))
  · exact (b5 K hN5K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C5 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))
  · exact (b6 K hN6K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C6 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))
  · exact (b7 K hN7K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C7 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))
  · exact (b8 K hN8K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C8 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))
  · exact (b9 K hN9K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show C9 ≤ C by dsimp only [C]; linarith) (sub_nonneg.mpr hq1))
        (by positivity))

end CubicTenVariables.CubicGoodHyperplanePointCountReduced
