import CubicTenVariables.CubicGoodHyperplaneUniformity
import CubicTenVariables.CubicNormalSectionCoordinates
import CubicTenVariables.CubicHyperplaneInductionStep
import CubicTenVariables.CubicSurfacePointCountOfAmplification

/-! Cubic point counts by repeated certified hyperplane sections.

The four-variable base is the explicit cubic-surface estimate.  The
internally proved uniform normal certificate and the literal variance
identity propagate the estimate by one variable.  The positive exceptional
integer remains visible; it is later multiplied into the exceptional integer
already permitted by the arithmetic theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicGoodHyperplanePointCount
open MvPolynomial Literature ProjectiveFourierIdentity
open CubicSlicingNumerics ProjectiveLinearSectionVariance
open ProjectivePolynomialSectionVariance
open CubicNonconicalHyperplaneCertificate
open SmoothCubicProjectivePointCount HessianTheorem11.PolynomialRestriction

/-- A field-independent affine cubic estimate in exactly `n` variables,
away from one positive integer. -/
def UniformAffineCubicBound (n : ℕ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ (K : Type) [Field K] [Fintype K], (N : K) ≠ 0 →
      ∀ F : MvPolynomial (Fin n) K, F.IsHomogeneous 3 →
        GeometricallyIntegralForm F → GeometricallyNonconicalCubic F →
        |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (n - 1)| ≤
          C * ((Fintype.card K : ℝ) - 1) *
            (Fintype.card K : ℝ) ^ (n - 3)

/-- The exact homogeneous-cone identity converts an affine estimate for a
section in `r+4` variables into the projective estimate used by variance. -/
theorem projective_bound_of_affine_bound
    {K : Type} [Field K] [Fintype K] (r : ℕ)
    (Q : MvPolynomial (Fin (r+4)) K) (hQ : Q.IsHomogeneous 3) (C : ℝ)
    (h : |(affineZeroCount Q : ℝ) - (Fintype.card K : ℝ) ^ (r+3)| ≤
      C * ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ (r+1)) :
    |(Nat.card (zeroPoints Q) : ℝ) -
        projectiveMainTerm (Fintype.card K) (r+2)| ≤
      C * (Fintype.card K : ℝ) ^ (r+1) := by
  have hq1 : (1 : ℝ) < Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hcone := real_affine_cone_card Q hQ (by decide)
  rw [cone_error (r+2) hcone, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card K - 1 by linarith)] at h
  have hmul : ((Fintype.card K : ℝ) - 1) *
        |(Nat.card (zeroPoints Q) : ℝ) -
          projectiveMainTerm (Fintype.card K) (r+2)| ≤
      ((Fintype.card K : ℝ) - 1) *
        (C * (Fintype.card K : ℝ) ^ (r+1)) := by
    convert h using 1 <;> ring
  exact le_of_mul_le_mul_left hmul
    (show (0 : ℝ) < Fintype.card K - 1 by linarith)

private def oneNormalEquiv (n : ℕ) : Fin n ≃ Fin (1 * n) :=
  Fin.castOrderIso (one_mul n).symm

private theorem eval_rename_one
    {K : Type} [Field K] (n : ℕ) (P : MvPolynomial (Fin n) K)
    (γ : Fin 1 → Fin n → K) :
    eval (normalTupleCoordinates γ) (rename (oneNormalEquiv n) P) =
      eval (γ 0) P := by
  rw [eval_rename]
  apply congrArg (fun f : MvPolynomial (Fin n) K →+* K => f P)
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp only [eval_X, Function.comp_apply, normalTupleCoordinates]
    change γ (finProdFinEquiv.symm (oneNormalEquiv n i)).1
      (finProdFinEquiv.symm (oneNormalEquiv n i)).2 = γ 0 i
    rw [show (finProdFinEquiv.symm (oneNormalEquiv n i)).1 = 0 from
      Subsingleton.elim _ _]
    congr 1
    apply Fin.ext
    simpa [oneNormalEquiv] using Nat.mod_eq_of_lt i.isLt

/-- The explicit surface amplification premise and smooth cubic Weil input
give the four-variable base of the induction. -/
theorem surface_base (ampl : CubicSurfacePointCountAmplification)
    (weil : SmoothCubicWeil) : UniformAffineCubicBound 4 := by
  refine ⟨6, by decide, 23328, by norm_num, ?_⟩
  intro K _ _ h6 F hF hGI hNC
  have h23 : (2 : K) * (3 : K) ≠ 0 := by
    rw [show (2 : K) * (3 : K) = 6 by norm_num]
    exact h6
  simpa only [show 4 - 1 = 3 by decide, show 4 - 3 = 1 by decide, pow_one] using
    CubicSurfacePointCountOfAmplification.affine_bound ampl weil F hF
      (mul_ne_zero_iff.mp h23).1 (mul_ne_zero_iff.mp h23).2 hGI hNC

/-- One certified hyperplane step raises a uniform estimate from `r+4` to
`r+5` variables.  The certificate's exceptional integer is multiplied into
the previous one; small finite fields relative to its degree are absorbed by
the elementary crude bound. -/
theorem succ_bound (r : ℕ) :
    UniformAffineCubicBound (r+4) → UniformAffineCubicBound (r+5) := by
  rintro ⟨N, hN, C, hC, hbound⟩
  obtain ⟨A, hA, D, hcert⟩ :=
    CubicGoodHyperplaneUniformity.exists_absolute_certificate (r+1)
  refine ⟨N * A, Nat.mul_pos hN hA,
    max (12 * (D : ℝ)) (C + 5), ?_, ?_⟩
  · exact le_trans hC (le_trans (by linarith) (le_max_right _ _))
  · intro K _ _ hNA F hF hGI hNC
    have hprod : (N : K) * (A : K) ≠ 0 := by
      simpa only [Nat.cast_mul] using hNA
    have hNK : (N : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hAK : (A : K) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hmain := CubicHyperplaneInductionStep.affine_bound_of_large_field_certificates
      r F (fun hz => hGI.1 hz) hF D C
    apply hmain
    intro _hlarge
    obtain ⟨Δ, hΔ, hdegree, hgood⟩ := hcert K F hAK (by
      simpa only [show r + 1 + 4 = r + 5 by omega] using hF) (by
      simpa only [show r + 1 + 4 = r + 5 by omega] using hGI) (by
      simpa only [show r + 1 + 4 = r + 5 by omega] using hNC)
    let Δ' : MvPolynomial (Fin (1 * (r+5))) K := rename (oneNormalEquiv (r+5)) Δ
    refine ⟨Δ', ?_, (totalDegree_rename_le _ _).trans hdegree, ?_⟩
    · intro hz
      apply hΔ
      apply rename_injective (oneNormalEquiv (r+5)) (oneNormalEquiv (r+5)).injective
      simpa only [map_zero, Δ'] using hz
    · intro γ hγ
      have hu : eval (γ 0) Δ ≠ 0 := by
        rw [← eval_rename_one (r+5) Δ γ]
        exact hγ
      obtain ⟨hinj, hrange, hQhom, _hQdeg, hQGI, hQNC⟩ := hgood (γ 0) hu
      have haff := hbound K hNK (restrict (frame (γ 0)) F)
        (by simpa only [show r + 1 + 4 = r + 5 by omega] using hQhom)
        (by simpa only [show r + 1 + 4 = r + 5 by omega] using hQGI)
        (by simpa only [show r + 1 + 4 = r + 5 by omega] using hQNC)
      have haff' :
          |(affineZeroCount (restrict (frame (γ 0)) F) : ℝ) -
              (Fintype.card K : ℝ) ^ (r+3)| ≤
            C * ((Fintype.card K : ℝ) - 1) *
              (Fintype.card K : ℝ) ^ (r+1) := by
        simpa only [show r + 4 - 1 = r + 3 by omega,
          show r + 4 - 3 = r + 1 by omega] using haff
      have hproj := projective_bound_of_affine_bound r
        (restrict (frame (γ 0)) F) hQhom C haff'
      rw [CubicNormalSectionCoordinates.projective_frame_card_one_row
        F hF (by decide) γ hinj hrange] at hproj
      exact hproj

/-- A single exceptional integer and constant cover every nonconical cubic
base dimension from four through nine. -/
theorem exists_uniform_base_bound_through_nine
    (ampl : CubicSurfacePointCountAmplification) (weil : SmoothCubicWeil) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ m : ℕ, m ≤ 9 → 4 ≤ m →
        ∀ (K : Type) [Field K] [Fintype K], (N : K) ≠ 0 →
          ∀ Q : MvPolynomial (Fin m) K, Q.IsHomogeneous 3 →
            GeometricallyIntegralForm Q → GeometricallyNonconicalCubic Q →
            |(affineZeroCount Q : ℝ) - (Fintype.card K : ℝ) ^ (m-1)| ≤
              C * ((Fintype.card K : ℝ) - 1) *
                (Fintype.card K : ℝ) ^ (m-3) := by
  have h4 := surface_base ampl weil
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
  refine ⟨N, by dsimp only [N]; positivity, C, by dsimp only [C]; linarith, ?_⟩
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
  have hp6 : (N4 : K)*(N5 : K)*(N6 : K) ≠ 0 := (mul_ne_zero_iff.mp hp7).1
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
        (mul_le_mul_of_nonneg_right (show C4 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))
  · exact (b5 K hN5K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C5 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))
  · exact (b6 K hN6K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C6 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))
  · exact (b7 K hN7K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C7 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))
  · exact (b8 K hN8K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C8 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))
  · exact (b9 K hN9K Q hQ hQI hQN).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show C9 ≤ C by dsimp only [C]; linarith)
          (sub_nonneg.mpr hq1)) (by positivity))

end CubicTenVariables.CubicGoodHyperplanePointCount
