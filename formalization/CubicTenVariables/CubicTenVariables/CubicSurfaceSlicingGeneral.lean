import CubicTenVariables.CubicHyperplaneSurfaceSlicing

/-! The surface-section counting step in every ambient dimension.
The hypothesis concerns actual section point counts and an explicit
nonzero bounded-degree polynomial. Existence of the good-section
certificate and the singular-surface estimate are not asserted here. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.CubicSurfaceSlicingGeneral
open MvPolynomial Literature ProjectiveFourierIdentity
open ProjectiveLinearSectionVariance ProjectivePolynomialSectionVariance
open SmoothCubicProjectivePointCount CubicSlicingNumerics

theorem surface_slicing_bound (k : ℕ) {q N M C : ℝ} (hq : 2 ≤ q)
    (hsize : N ≤ 6 * q ^ (k + 2))
    (hvariance : (N - q ^ k * M) ^ 2 ≤ 2 * N * (q ^ k - 1))
    (hsection : |M - projectiveMainTerm q 2| ≤ C * q) :
    |N - projectiveMainTerm q (k + 2)| ≤ (C + 5) * q ^ (k + 1) := by
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hk : 0 ≤ q ^ k - 1 := sub_nonneg.mpr (one_le_pow₀ hq1)
  have hv12 : (N - q ^ k * M) ^ 2 ≤ 12 * (q ^ (k + 1)) ^ 2 := by
    calc
      _ ≤ 2 * N * (q ^ k - 1) := hvariance
      _ ≤ 2 * (6 * q ^ (k + 2)) * (q ^ k - 1) := by gcongr
      _ ≤ 2 * (6 * q ^ (k + 2)) * q ^ k := by gcongr; linarith
      _ = _ := by simp only [pow_add, pow_one]; ring
  have hv : |N - q ^ k * M| ≤ 4 * q ^ (k + 1) := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    nlinarith [sq_nonneg (q ^ (k + 1))]
  let R : ℝ := ∑ i ∈ Finset.range k, q ^ i
  have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => pow_nonneg hq0 _)
  have hR : R ≤ q ^ (k + 1) := by
    have hle : R ≤ projectiveMainTerm q k := by
      simp only [R, projectiveMainTerm, Finset.sum_range_succ]
      exact le_add_of_nonneg_right (pow_nonneg hq0 k)
    calc
      R ≤ projectiveMainTerm q k := hle
      _ ≤ 2 * q ^ k := projectiveMainTerm_le_two hq k
      _ ≤ q * q ^ k := by gcongr
      _ = q ^ (k + 1) := by ring
  have hsplit : projectiveMainTerm q (k + 2) = q ^ k * projectiveMainTerm q 2 + R := by
    simp only [projectiveMainTerm, show k + 2 + 1 = k + 3 by omega,
      Finset.sum_range_add, pow_add, ← Finset.mul_sum, R]
    norm_num [Finset.sum_range_succ]
    ring
  have htriangle : |N - projectiveMainTerm q (k + 2)| ≤
      |N - q ^ k * M| + q ^ k * |M - projectiveMainTerm q 2| + R := by
    rw [show N - projectiveMainTerm q (k + 2) =
      (N - q ^ k * M) + q ^ k * (M - projectiveMainTerm q 2) - R by rw [hsplit]; ring]
    have h := (abs_sub ((N - q ^ k * M) + q ^ k * (M - projectiveMainTerm q 2)) R).trans
      (add_le_add (abs_add_le (N - q ^ k * M)
        (q ^ k * (M - projectiveMainTerm q 2))) (le_refl _))
    simpa only [abs_mul, abs_of_nonneg (pow_nonneg hq0 k), abs_of_nonneg hR0] using h
  calc
    _ ≤ |N - q ^ k * M| + q ^ k * |M - projectiveMainTerm q 2| + R := htriangle
    _ ≤ 4 * q ^ (k + 1) + q ^ k * (C * q) + q ^ (k + 1) := by gcongr
    _ = _ := by ring

variable {K : Type} [Field K] [Fintype K]

theorem crude_bound (k : ℕ) (F : MvPolynomial (Fin (k + 4)) K)
    (hFne : F ≠ 0) (hF : F.IsHomogeneous 3) :
    (Nat.card (zeroPoints F) : ℝ) ≤ 6 * (Fintype.card K : ℝ) ^ (k + 2) := by
  classical
  have hSZ := card_affine_polynomial_zeros_le_degree_mul
    (m := k + 3) (D := 3) F hFne hF.totalDegree_le
  have hA : (affineZeroCount F : ℝ) ≤ 3 * (Fintype.card K : ℝ) ^ (k + 3) := by
    rw [affineZeroCount_eq_filter_card]
    exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using hSZ)
  have hcone := real_affine_cone_card F hF (by decide)
  have hq : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hN : (0 : ℝ) ≤ Nat.card (zeroPoints F) := Nat.cast_nonneg _
  have hhalf : (Fintype.card K : ℝ) / 2 ≤ (Fintype.card K : ℝ) - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hhalf hN
  have hpow : (Fintype.card K : ℝ) ^ (k + 3) =
      (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ (k + 2) := by ring
  rw [hpow] at hA
  have h : (Fintype.card K : ℝ) * (Nat.card (zeroPoints F) : ℝ) ≤
      (Fintype.card K : ℝ) * (6 * (Fintype.card K : ℝ) ^ (k + 2)) := by nlinarith
  exact le_of_mul_le_mul_left h (by linarith)

/-- The same surface bound gives the required projective exponent for
every number of variables at least four. -/
theorem projective_bound_of_surface_counts (k : ℕ)
    (F : MvPolynomial (Fin (k + 4)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin (k * (k + 4))) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin k → Fin (k + 4) → K,
      eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) - projectiveMainTerm (Fintype.card K) 2| ≤
        C * (Fintype.card K : ℝ)) :
    |(Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) (k + 2)| ≤
      (C + 5) * (Fintype.card K : ℝ) ^ (k + 1) := by
  obtain ⟨γ, hγ, hvariance⟩ := exists_polynomial_nonvanishing_section
    (n := k + 4) (k := k) (D := D) (by omega) (polynomialPoints F) Δ hΔ hdegree hq
  simp only [card_polynomialPoints, sectionCount_polynomialPoints] at hvariance
  rw [show Nat.card K = Fintype.card K from Nat.card_eq_fintype_card] at hvariance
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  exact surface_slicing_bound k hq2
    (crude_bound k F hFne hF) hvariance (hsections γ hγ)

/-- Literal affine-cone form, with error (C+5)(q-1)q^(n-3).
This is the uniform numerical assembly needed for all cone-base sizes. -/
theorem affine_bound_of_surface_counts (k : ℕ)
    (F : MvPolynomial (Fin (k + 4)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (Δ : MvPolynomial (Fin (k * (k + 4))) K) (hΔ : Δ ≠ 0)
    (hdegree : Δ.totalDegree ≤ D) (hq : 2 * D < Nat.card K) (C : ℝ)
    (hsections : ∀ γ : Fin k → Fin (k + 4) → K,
      eval (normalTupleCoordinates γ) Δ ≠ 0 →
      |(Nat.card (linearSectionPoints F γ) : ℝ) - projectiveMainTerm (Fintype.card K) 2| ≤
        C * (Fintype.card K : ℝ)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (k + 3)| ≤
      (C + 5) * ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ (k + 1) := by
  have h := projective_bound_of_surface_counts k F hFne hF D Δ hΔ hdegree hq C hsections
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  rw [cone_error (k + 2) (real_affine_cone_card F hF (by decide)), abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) * ((C + 5) * (Fintype.card K : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
    _ = _ := by ring

/-- Small fields are absorbed by the polynomial zero bound; no good
surface section is required for these fields. -/
theorem small_field_affine_bound (k : ℕ)
    (F : MvPolynomial (Fin (k + 4)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (T : ℝ) (hsmall : (Fintype.card K : ℝ) ≤ T) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (k + 3)| ≤
      (6 * T) * ((Fintype.card K : ℝ) - 1) * (Fintype.card K : ℝ) ^ (k + 1) := by
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hq0 : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hN0 : (0 : ℝ) ≤ Nat.card (zeroPoints F) := by positivity
  have hN := crude_bound k F hFne hF
  have hpi := projectiveMainTerm_le_two hq2 (k + 2)
  have hpi0 := projectiveMainTerm_nonneg hq0 (k + 2)
  have he : |(Nat.card (zeroPoints F) : ℝ) -
      projectiveMainTerm (Fintype.card K) (k + 2)| ≤
      6 * (Fintype.card K : ℝ) ^ (k + 2) := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hq0 (k + 2)]
  have hpow : 6 * (Fintype.card K : ℝ) ^ (k + 2) ≤
      (6 * T) * (Fintype.card K : ℝ) ^ (k + 1) := by
    calc
      _ = (6 * (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ (k + 1) := by ring
      _ ≤ _ := by gcongr
  rw [cone_error (k + 2) (real_affine_cone_card F hF (by decide)), abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card K - 1 by linarith)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) * ((6 * T) * (Fintype.card K : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (he.trans hpow) (by linarith)
    _ = _ := by ring

/-- A certificate of degree at most D for every sufficiently large field
gives one displayed constant valid for every field size. The same C and D
may be fixed before an entire coefficient family. -/
theorem affine_bound_of_large_field_certificates (k : ℕ)
    (F : MvPolynomial (Fin (k + 4)) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (D : ℕ) (C : ℝ)
    (hcert : 2 * D < Nat.card K →
      ∃ Δ : MvPolynomial (Fin (k * (k + 4))) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
        ∀ γ : Fin k → Fin (k + 4) → K, eval (normalTupleCoordinates γ) Δ ≠ 0 →
          |(Nat.card (linearSectionPoints F γ) : ℝ) - projectiveMainTerm (Fintype.card K) 2| ≤
            C * (Fintype.card K : ℝ)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ (k + 3)| ≤
      max (12 * (D : ℝ)) (C + 5) * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ (k + 1) := by
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  by_cases hlarge : 2 * D < Nat.card K
  · obtain ⟨Δ, hΔ, hdegree, hsections⟩ := hcert hlarge
    apply (affine_bound_of_surface_counts k F hFne hF D Δ hΔ hdegree hlarge C hsections).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right (12 * (D : ℝ)) (C + 5))
        (sub_nonneg.mpr hq1)) (by positivity)
  · have hsmall : (Fintype.card K : ℝ) ≤ 2 * (D : ℝ) := by
      exact_mod_cast (show Fintype.card K ≤ 2 * D by
        simpa only [Nat.card_eq_fintype_card] using Nat.le_of_not_gt hlarge)
    have h := small_field_affine_bound k F hFne hF (2 * (D : ℝ)) hsmall
    rw [show (6 : ℝ) * (2 * (D : ℝ)) = 12 * D by ring] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (12 * (D : ℝ)) (C + 5))
        (sub_nonneg.mpr hq1)) (by positivity)

end CubicTenVariables.CubicSurfaceSlicingGeneral
