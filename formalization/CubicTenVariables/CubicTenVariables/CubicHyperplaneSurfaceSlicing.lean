import CubicTenVariables.SmoothCubicProjectivePointCount
import CubicTenVariables.ProjectiveLinearSectionCoordinates

/-! Nine-variable cubic counts from actual surface-section counts.
The certificate is an explicit hypothesis, including its nonvanishing on
more than half of all tuples. No assertion that all hyperplane sections
admit smooth surface sections is made. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicHyperplaneSurfaceSlicing
open MvPolynomial Literature ProjectiveFourierIdentity
open ProjectiveLinearSectionVariance ProjectivePolynomialSectionVariance
open ProjectiveLinearSectionCoordinates SmoothCubicProjectivePointCount
open CubicSlicingNumerics

theorem surface_slicing_bound {q N M C : ℝ} (hq : 2 ≤ q)
    (hN : 0 ≤ N) (hsize : N ≤ 6 * q ^ 7)
    (hvariance : (N - q ^ 5 * M) ^ 2 ≤ 2 * N * (q ^ 5 - 1))
    (hsection : |M - projectiveMainTerm q 2| ≤ C * q) :
    |N - projectiveMainTerm q 7| ≤ (C + 5) * q ^ 6 := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hfive : 0 ≤ q ^ 5 - 1 := sub_nonneg.mpr (one_le_pow₀ hq1)
  have hv12 : (N - q ^ 5 * M) ^ 2 ≤ 12 * q ^ 12 := by
    calc
      _ ≤ 2 * N * (q ^ 5 - 1) := hvariance
      _ ≤ 2 * (6 * q ^ 7) * (q ^ 5 - 1) := by gcongr
      _ ≤ 12 * q ^ 12 := by nlinarith [pow_nonneg hq0 7]
  have hv : |N - q ^ 5 * M| ≤ 4 * q ^ 6 := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    have hsquare : (4 * q ^ 6) ^ 2 = 16 * q ^ 12 := by ring
    rw [hsquare]
    nlinarith [pow_nonneg hq0 12]
  have hpi4 : projectiveMainTerm q 4 ≤ q ^ 6 := by
    calc
      _ ≤ 2 * q ^ 4 := projectiveMainTerm_le_two hq 4
      _ ≤ q * q ^ 4 := by gcongr
      _ = q ^ 5 := by ring
      _ ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by decide : 5 ≤ 6)
  have hsplit : projectiveMainTerm q 7 =
      q ^ 5 * projectiveMainTerm q 2 + projectiveMainTerm q 4 := by
    norm_num [projectiveMainTerm, Finset.sum_range_succ]
    ring
  have htriangle : |N - projectiveMainTerm q 7| ≤
      |N - q ^ 5 * M| + q ^ 5 * |M - projectiveMainTerm q 2| +
        projectiveMainTerm q 4 := by
    rw [show N - projectiveMainTerm q 7 =
        (N - q ^ 5 * M) + q ^ 5 * (M - projectiveMainTerm q 2) -
          projectiveMainTerm q 4 by rw [hsplit]; ring]
    have h := (abs_sub ((N - q ^ 5 * M) + q ^ 5 * (M - projectiveMainTerm q 2))
      (projectiveMainTerm q 4)).trans
        (add_le_add (abs_add_le (N - q ^ 5 * M)
          (q ^ 5 * (M - projectiveMainTerm q 2))) (le_refl _))
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg hq0 5),
      abs_of_nonneg (projectiveMainTerm_nonneg hq0 4)] using h
  calc
    _ ≤ |N - q ^ 5 * M| + q ^ 5 * |M - projectiveMainTerm q 2| +
        projectiveMainTerm q 4 := htriangle
    _ ≤ 4 * q ^ 6 + q ^ 5 * (C * q) + q ^ 6 := by gcongr
    _ = _ := by ring

variable {K : Type} [Field K] [Fintype K]

theorem nine_variable_crude_bound (F : MvPolynomial (Fin 9) K)
    (hFne : F ≠ 0) (hF : F.IsHomogeneous 3) :
    (Nat.card (zeroPoints F) : ℝ) ≤ 6 * (Fintype.card K : ℝ) ^ 7 := by
  classical
  have hSZ := card_affine_polynomial_zeros_le_degree_mul
    (m := 8) (D := 3) F hFne hF.totalDegree_le
  have hA : (affineZeroCount F : ℝ) ≤ 3 * (Fintype.card K : ℝ) ^ 8 := by
    rw [affineZeroCount_eq_filter_card]
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hSZ)
  have hcone := real_affine_cone_card F hF (by decide)
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hN : (0 : ℝ) ≤ Nat.card (zeroPoints F) := Nat.cast_nonneg _
  have hhalf : (Fintype.card K : ℝ) / 2 ≤ (Fintype.card K : ℝ) - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hhalf hN
  have h : (Fintype.card K : ℝ) * (Nat.card (zeroPoints F) : ℝ) ≤
      (Fintype.card K : ℝ) * (6 * (Fintype.card K : ℝ) ^ 7) := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

/-- This interface counts the actual surface-section points, so it also
accepts a separately proved singular-surface estimate. -/
theorem projective_bound_of_surface_counts
    (F : MvPolynomial (Fin 9) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 45) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin 5 → Fin 9 → K, eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) - projectiveMainTerm (Fintype.card K) 2| ≤
        C * (Fintype.card K : ℝ)) :
    |(Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) 7| ≤
      (C + 5) * (Fintype.card K : ℝ) ^ 6 := by
  obtain ⟨γ, hγ, hvariance⟩ := exists_polynomial_nonvanishing_section
    (n := 9) (k := 5) (D := D) (by decide) (polynomialPoints F) Δ hΔ hdegree hq
  simp only [card_polynomialPoints, sectionCount_polynomialPoints] at hvariance
  rw [show Nat.card K = Fintype.card K from Nat.card_eq_fintype_card] at hvariance
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  exact surface_slicing_bound hq2 (Nat.cast_nonneg _)
    (nine_variable_crude_bound F hFne hF) hvariance (hsections γ hγ)

theorem affine_bound_of_surface_counts
    (F : MvPolynomial (Fin 9) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 45) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin 5 → Fin 9 → K, eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) - projectiveMainTerm (Fintype.card K) 2| ≤
        C * (Fintype.card K : ℝ)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 8| ≤
      (C + 5) * ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ 6 := by
  have h := projective_bound_of_surface_counts F hFne hF D Δ hΔ hdegree hq C hsections
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  rw [cone_error 7 (real_affine_cone_card F hF (by decide)), abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) * ((C + 5) * (Fintype.card K : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
    _ = _ := by ring

/-- An explicit geometric certificate only for the smooth-surface branch. -/
def SmoothSurfaceSections (F : MvPolynomial (Fin 9) K)
    (Δ : MvPolynomial (Fin 45) K) : Prop :=
  ∀ γ : Fin 5 → Fin 9 → K, eval (normalTupleCoordinates γ) Δ ≠ 0 →
    ∃ e : (Fin 4 → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ),
      sectionPolynomial F γ e ≠ 0 ∧ ProjectivelySmooth (sectionPolynomial F γ e)

theorem affine_bound_of_smooth_surfaces (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 9) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin 45) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K)
    (hsections : SmoothSurfaceSections F Δ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 8| ≤
      15 * ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ 6 := by
  rw [show (15 : ℝ) = 10 + 5 by norm_num]
  apply affine_bound_of_surface_counts F hFne hF D Δ hΔ hdegree hq 10
  intro γ hγ
  obtain ⟨e, hGne, hGsmooth⟩ := hsections γ hγ
  have hcount := projective_error_sq weil 2 (by decide) (by decide)
    (sectionPolynomial F γ e) hGne (sectionPolynomial_isHomogeneous F hF γ e) hGsmooth
  rw [projective_sectionPolynomial_card F hF (by decide) γ e] at hcount
  apply abs_le_of_sq_le_sq _ (by positivity)
  convert hcount using 1 <;> ring

end CubicTenVariables.CubicHyperplaneSurfaceSlicing
