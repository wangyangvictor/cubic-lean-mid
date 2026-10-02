import CubicTenVariables.CubicSurfaceSlicingGeneral

/-! One literal hyperplane-induction step for cubic point counts.

The geometric input is a nonzero bounded-degree polynomial in the actual
normal coefficients.  Every normal in its principal open must have the
displayed point-count bound.  The variance identity then raises the bound
by one ambient dimension.  Small fields are absorbed internally.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.CubicHyperplaneInductionStep
open MvPolynomial Literature ProjectiveFourierIdentity
open ProjectiveLinearSectionVariance ProjectivePolynomialSectionVariance
open SmoothCubicProjectivePointCount CubicSlicingNumerics

/-- The scalar numerical induction.  A cubic in `r+5` variables has
projective dimension `r+3`; its hyperplane section has dimension `r+2`. -/
theorem hyperplane_slicing_bound (r : ℕ) {q N M C : ℝ} (hq : 2 ≤ q)
    (hsize : N ≤ 6 * q ^ (r + 3))
    (hvariance : (N - q * M) ^ 2 ≤ 2 * N * (q - 1))
    (hsection : |M - projectiveMainTerm q (r + 2)| ≤ C * q ^ (r + 1)) :
    |N - projectiveMainTerm q (r + 3)| ≤ (C + 5) * q ^ (r + 2) := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqm1 : 0 ≤ q - 1 := by linarith
  have hv12 : (N - q * M) ^ 2 ≤ 12 * q ^ (r + 4) := by
    calc
      _ ≤ 2 * N * (q - 1) := hvariance
      _ ≤ 2 * (6 * q ^ (r + 3)) * (q - 1) := by gcongr
      _ ≤ 12 * q ^ (r + 3) * q := by
        nlinarith [pow_nonneg hq0 (r + 3)]
      _ = 12 * q ^ (r + 4) := by rw [pow_succ]; ring
  have hv : |N - q * M| ≤ 4 * q ^ (r + 2) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    have hpow : q ^ (r + 4) ≤ q ^ (2 * r + 4) := by
      exact pow_le_pow_right₀ hq1 (by omega)
    have hsquare : (4 * q ^ (r + 2)) ^ 2 = 16 * q ^ (2 * r + 4) := by
      rw [mul_pow, ← pow_mul]
      norm_num
      congr 1
      omega
    rw [hsquare]
    nlinarith
  have hsplit : projectiveMainTerm q (r + 3) =
      q * projectiveMainTerm q (r + 2) + 1 := by
    apply mul_left_cancel₀ (show q - 1 ≠ 0 by linarith)
    calc
      (q - 1) * projectiveMainTerm q (r + 3) = q ^ (r + 4) - 1 := by
        nlinarith [cone_mainTerm q (r + 3)]
      _ = q * q ^ (r + 3) - 1 := by rw [pow_succ]; ring
      _ = q * (1 + (q - 1) * projectiveMainTerm q (r + 2)) - 1 := by
        rw [cone_mainTerm q (r + 2)]
      _ = (q - 1) * (q * projectiveMainTerm q (r + 2) + 1) := by ring
  have htriangle : |N - projectiveMainTerm q (r + 3)| ≤
      |N - q * M| + q * |M - projectiveMainTerm q (r + 2)| + 1 := by
    rw [show N - projectiveMainTerm q (r + 3) =
        (N - q * M) + q * (M - projectiveMainTerm q (r + 2)) - 1 by
      rw [hsplit]; ring]
    have h := (abs_sub ((N - q * M) +
      q * (M - projectiveMainTerm q (r + 2))) 1).trans
      (add_le_add (abs_add_le (N - q * M)
        (q * (M - projectiveMainTerm q (r + 2)))) (le_refl _))
    simpa only [abs_mul, abs_of_nonneg hq0, abs_one] using h
  calc
    _ ≤ |N - q * M| + q * |M - projectiveMainTerm q (r + 2)| + 1 := htriangle
    _ ≤ 4 * q ^ (r + 2) + q * (C * q ^ (r + 1)) + q ^ (r + 2) := by
      gcongr
      exact one_le_pow₀ hq1
    _ = (C + 5) * q ^ (r + 2) := by rw [pow_succ]; ring

variable {K : Type} [Field K] [Fintype K]

/-- A majority principal open of good hyperplanes propagates the
projective estimate by one dimension. -/
theorem projective_bound_of_hyperplane_counts (r : ℕ)
    (F : MvPolynomial (Fin (r + 5)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin (1 * (r + 5))) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin 1 → Fin (r + 5) → K,
      eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) -
        projectiveMainTerm (Fintype.card K) (r + 2)| ≤
          C * (Fintype.card K : ℝ) ^ (r + 1)) :
    |(Nat.card (zeroPoints F) : ℝ) -
      projectiveMainTerm (Fintype.card K) (r + 3)| ≤
        (C + 5) * (Fintype.card K : ℝ) ^ (r + 2) := by
  obtain ⟨γ, hγ, hvariance⟩ := exists_polynomial_nonvanishing_section
    (n := r + 5) (k := 1) (D := D) (by omega) (polynomialPoints F) Δ hΔ hdegree hq
  simp only [card_polynomialPoints, sectionCount_polynomialPoints, pow_one] at hvariance
  rw [show Nat.card K = Fintype.card K from Nat.card_eq_fintype_card] at hvariance
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  exact hyperplane_slicing_bound r hq2
    (CubicSurfaceSlicingGeneral.crude_bound (r + 1) F hFne hF)
    hvariance (hsections γ hγ)

/-- The same step in affine-cone coordinates. -/
theorem affine_bound_of_hyperplane_counts (r : ℕ)
    (F : MvPolynomial (Fin (r + 5)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin (1 * (r + 5))) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin 1 → Fin (r + 5) → K,
      eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) -
        projectiveMainTerm (Fintype.card K) (r + 2)| ≤
          C * (Fintype.card K : ℝ) ^ (r + 1)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (r + 4)| ≤
      (C + 5) * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ (r + 2) := by
  have h := projective_bound_of_hyperplane_counts r F hFne hF
    D Δ hΔ hdegree hq C hsections
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  rw [cone_error (r + 3) (real_affine_cone_card F hF (by omega)), abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) *
        ((C + 5) * (Fintype.card K : ℝ) ^ (r + 2)) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
    _ = _ := by ring

/-- Small fields require no good hyperplane. -/
theorem small_field_affine_bound (r : ℕ)
    (F : MvPolynomial (Fin (r + 5)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (T : ℝ) (hsmall : (Fintype.card K : ℝ) ≤ T) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (r + 4)| ≤
      (6 * T) * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ (r + 2) := by
  simpa only [show r + 1 + 4 = r + 5 by omega,
    show r + 1 + 3 = r + 4 by omega,
    show r + 1 + 1 = r + 2 by omega] using
    CubicSurfaceSlicingGeneral.small_field_affine_bound (r + 1) F hFne hF T hsmall

/-- One bounded-degree certificate for large fields gives a single
constant valid over all field sizes. -/
theorem affine_bound_of_large_field_certificates (r : ℕ)
    (F : MvPolynomial (Fin (r + 5)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (C : ℝ)
    (hcert : 2 * D < Nat.card K →
      ∃ Δ : MvPolynomial (Fin (1 * (r + 5))) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
        ∀ γ : Fin 1 → Fin (r + 5) → K,
          eval (normalTupleCoordinates γ) Δ ≠ 0 →
          |(Nat.card (linearSectionPoints F γ) : ℝ) -
            projectiveMainTerm (Fintype.card K) (r + 2)| ≤
              C * (Fintype.card K : ℝ) ^ (r + 1)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (r + 4)| ≤
      max (12 * (D : ℝ)) (C + 5) * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ (r + 2) := by
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  by_cases hlarge : 2 * D < Nat.card K
  · obtain ⟨Δ, hΔ, hdegree, hsections⟩ := hcert hlarge
    apply (affine_bound_of_hyperplane_counts r F hFne hF D Δ hΔ hdegree
      hlarge C hsections).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (12 * (D : ℝ)) (C + 5))
        (sub_nonneg.mpr hq1)) (by positivity)
  · have hsmall : (Fintype.card K : ℝ) ≤ 2 * (D : ℝ) := by
      exact_mod_cast (show Fintype.card K ≤ 2 * D by
        simpa only [Nat.card_eq_fintype_card] using Nat.le_of_not_gt hlarge)
    have h := small_field_affine_bound r F hFne hF (2 * (D : ℝ)) hsmall
    rw [show (6 : ℝ) * (2 * (D : ℝ)) = 12 * D by ring] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (12 * (D : ℝ)) (C + 5))
        (sub_nonneg.mpr hq1)) (by positivity)

end CubicTenVariables.CubicHyperplaneInductionStep
