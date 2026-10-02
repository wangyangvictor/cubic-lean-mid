import CubicTenVariables.SmoothCubicProjectivePointCount
import CubicTenVariables.ProjectiveLinearSectionCoordinates
import CubicTenVariables.PolynomialCertificateDescent

/-! Vertical ten-variable point-count reduction through actual smooth cubic
threefold sections. The existence of the displayed discriminant polynomial
is NOT proved or declared as a global axiom here. The final theorem names
that precise remaining geometric antecedent and the concrete Weil input.
All counting, coordinate changes, and numerical deductions are proved. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace CubicTenVariables.CubicSmoothSectionReduction
open MvPolynomial Literature ProjectiveFourierIdentity
open ProjectiveLinearSectionVariance ProjectivePolynomialSectionVariance
open ProjectiveLinearSectionCoordinates SmoothCubicProjectivePointCount
open CubicSlicingNumerics

variable {K : Type} [Field K] [Fintype K]

/-- A literal supplied polynomial guarantees that its nonvanishing tuples
cut out smooth cubic threefolds. The equation of the section is the actual
restriction of F to the common kernel; no point-count comparison is assumed. -/
def SmoothThreefoldSections (F : MvPolynomial (Fin 10) K)
    (Δ : MvPolynomial (Fin 50) K) : Prop :=
  ∀ γ : Fin 5 → Fin 10 → K, eval (normalTupleCoordinates γ) Δ ≠ 0 →
    ∃ e : (Fin 5 → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ),
      sectionPolynomial F γ e ≠ 0 ∧ ProjectivelySmooth (sectionPolynomial F γ e)

/-- Large-field slicing, with the geometric guarantee stated independently
of the actual variance, smooth-cubic point count, and resulting estimate. -/
theorem large_field_projective_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (Δ : MvPolynomial (Fin 50) K) (hΔ : Δ ≠ 0) (hdegree : Δ.totalDegree ≤ 720)
    (hq : 1440 < Nat.card K) (hsections : SmoothThreefoldSections F Δ) :
    |(Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) 8| ≤
      15 * (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  obtain ⟨γ, hγ, hvariance⟩ := exists_polynomial_nonvanishing_section
    (n := 10) (k := 5) (D := 720) (by decide) (polynomialPoints F) Δ hΔ hdegree hq
  simp only [card_polynomialPoints, sectionCount_polynomialPoints] at hvariance
  rw [show Nat.card K = Fintype.card K from Nat.card_eq_fintype_card] at hvariance
  obtain ⟨e, hGne, hGsmooth⟩ := hsections γ hγ
  have hG := sectionPolynomial_isHomogeneous F hF γ e
  have hcount := projective_error_sq weil 3 (by decide) (by decide)
    (sectionPolynomial F γ e) hGne hG hGsmooth
  rw [projective_sectionPolynomial_card F hF (by decide) γ e] at hcount
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    have h : 2 ≤ Fintype.card K := Fintype.one_lt_card
    exact_mod_cast h
  exact projective_slicing_bound hq2 (Nat.cast_nonneg _)
    (ten_variable_crude_bound F hFne hF) hvariance hcount

/-- A single uniform constant covers small fields without any section
existence requirement and large fields with a supplied discriminant. -/
theorem projective_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hsections : 1440 < Nat.card K →
      ∃ Δ : MvPolynomial (Fin 50) K,
        Δ ≠ 0 ∧ Δ.totalDegree ≤ 720 ∧ SmoothThreefoldSections F Δ) :
    |(Nat.card (zeroPoints F) : ℝ) - projectiveMainTerm (Fintype.card K) 8| ≤
      330000 * (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  have hq2 : (2 : ℝ) ≤ Fintype.card K := by
    have h : 2 ≤ Fintype.card K := Fintype.one_lt_card
    exact_mod_cast h
  by_cases hsmall : Nat.card K ≤ 1440
  · have hsmall' : (Fintype.card K : ℝ) ≤ 1440 := by
      rw [Nat.card_eq_fintype_card] at hsmall
      exact_mod_cast hsmall
    exact small_field_projective_bound hq2 hsmall' (Nat.cast_nonneg _)
      (ten_variable_crude_bound F hFne hF)
  · have hlarge : 1440 < Nat.card K := Nat.lt_of_not_ge hsmall
    obtain ⟨Δ, hΔ, hdegree, hsmooth⟩ := hsections hlarge
    exact (large_field_projective_bound weil F hFne hF Δ hΔ hdegree hlarge hsmooth).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (15 : ℝ) ≤ 330000)
        (Real.rpow_nonneg (by positivity) _))

/-- The exact affine-cone estimate used by the ambient ten-variable branch.
The only antecedents beyond the polynomial itself are the explicit numerical
Weil premise and the stated smooth-section discriminant existence assertion. -/
theorem affine_bound (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hsections : 1440 < Nat.card K →
      ∃ Δ : MvPolynomial (Fin 50) K,
        Δ ≠ 0 ∧ Δ.totalDegree ≤ 720 ∧ SmoothThreefoldSections F Δ) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      330000 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  have h := projective_bound weil F hFne hF hsections
  have hq1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast (show 1 ≤ Fintype.card K from Fintype.card_pos)
  have hcone := cone_error 8 (real_affine_cone_card F hF (by decide))
  rw [hcone, abs_mul, abs_of_nonneg (sub_nonneg.mpr hq1)]
  calc
    _ ≤ ((Fintype.card K : ℝ) - 1) *
        (330000 * (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hq1)
    _ = _ := by ring

/-- The geometric certificate may have coefficients in the algebraic
closure. Coefficient descent preserves the degree and certifies exactly
the base-field tuples needed by the counting argument. -/
theorem affine_bound_of_geometric_certificate (weil : SmoothCubicWeil)
    (F : MvPolynomial (Fin 10) K) (hFne : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hsections : 1440 < Nat.card K →
      ∃ P : MvPolynomial (Fin 50) (AlgebraicClosure K),
        P ≠ 0 ∧ P.totalDegree ≤ 720 ∧
        ∀ γ : Fin 5 → Fin 10 → K,
          eval (algebraMap K (AlgebraicClosure K) ∘ normalTupleCoordinates γ) P ≠ 0 →
          ∃ e : (Fin 5 → K) ≃ₗ[K] LinearMap.ker (Matrix.mulVecLin γ),
            sectionPolynomial F γ e ≠ 0 ∧
              ProjectivelySmooth (sectionPolynomial F γ e)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ) ^ 9| ≤
      330000 * ((Fintype.card K : ℝ) - 1) *
        (Fintype.card K : ℝ) ^ ((13 : ℝ) / 2) := by
  apply affine_bound weil F hFne hF
  intro hq
  obtain ⟨P, hP, hdegree, hgood⟩ := hsections hq
  obtain ⟨Δ, hΔ, hdegreeΔ, hnonvanishing⟩ :=
    PolynomialCertificateDescent.exists_nonzero_polynomial_certificate (K := K) P hP
  refine ⟨Δ, hΔ, hdegreeΔ.trans hdegree, ?_⟩
  intro γ hγ
  exact hgood γ (hnonvanishing (normalTupleCoordinates γ) hγ)

end CubicTenVariables.CubicSmoothSectionReduction
