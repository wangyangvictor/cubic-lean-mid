import CubicTenVariables.Literature.SurfacePointCountAmplification
import CubicTenVariables.CubicSurfacePotentialGoodness

/-! A complete numerical cubic-surface reduction, conditional on the explicit
surface-only classical amplification premise. Geometrically singular surfaces
use the internally proved finite-extension projection bound. Smooth surfaces
use the separately displayed numerical SmoothCubicWeil premise. This does not
formalize the étale-cohomological realization of either literature input. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CubicSurfacePointCountOfAmplification
open MvPolynomial HessianTheorem11 Literature ProjectiveFourierIdentity
variable {K : Type} [Field K] [Fintype K]

/-- All geometrically singular cases, including conjugate singular points,
are covered by adjoining one actual point and applying the classical input. -/
theorem singular_projective_bound (ampl : CubicSurfacePointCountAmplification)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hI : GeometricallyIntegralForm F) (hNC : GeometricallyNonconicalCubic F)
    (hs : ∃ x : Fin 4 → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F) :
    |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        23328 * (Fintype.card K : ℝ) := by
  obtain ⟨B,hB,h⟩ := CubicSurfacePotentialGoodness.exists_uniform_projective_potential_bound
  exact ampl K F hF h2 h3 hI ⟨B,zero_le_one.trans hB,h K F hF h2 h3 hI hNC hs⟩

/-- Exact cone conversion, with an arbitrary supplied projective bound. -/
theorem affine_bound_of_projective_bound
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (C : ℝ)
    (hp : |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        C * (Fintype.card K : ℝ)) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      C * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq : 0 ≤ q-1 := by
    have hh : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := K))
    dsimp only [q]
    linarith
  have hc := SmoothCubicProjectivePointCount.real_affine_cone_card F hF (by decide)
  have he : (affineZeroCount F : ℝ) - q^3 =
      (q-1) * ((Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)) := by
    change (affineZeroCount F : ℝ) = 1 + (q-1)*(Nat.card (zeroPoints F) : ℝ) at hc
    rw [hc]
    ring
  change |(affineZeroCount F : ℝ) - q^3| ≤ C*(q-1)*q
  rw [he,abs_mul,abs_of_nonneg hq]
  calc
    (q-1)*|(Nat.card (zeroPoints F) : ℝ) - (q^2+q+1)| ≤ (q-1)*(C*q) :=
      mul_le_mul_of_nonneg_left hp hq
    _ = C*(q-1)*q := by ring

/-- Affine form of the singular-surface result; no smooth Weil input is used. -/
theorem singular_affine_bound (ampl : CubicSurfacePointCountAmplification)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hI : GeometricallyIntegralForm F) (hNC : GeometricallyNonconicalCubic F)
    (hs : ∃ x : Fin 4 → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      23328 * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) :=
  affine_bound_of_projective_bound F hF 23328
    (singular_projective_bound ampl F hF h2 h3 hI hNC hs)

/-- A single explicit constant covers every integral nonconical cubic
surface: smooth and geometrically singular. The two literature premises
are displayed separately. -/
theorem projective_bound (ampl : CubicSurfacePointCountAmplification)
    (weil : SmoothCubicWeil) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hI : GeometricallyIntegralForm F) (hNC : GeometricallyNonconicalCubic F) :
    |(Nat.card (zeroPoints F) : ℝ) -
      ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
        23328 * (Fintype.card K : ℝ) := by
  classical
  by_cases hsmooth : ProjectivelySmooth F
  · have hsq := SmoothCubicProjectivePointCount.projective_error_sq
      weil 2 (by decide) (by decide) F hI.1 hF hsmooth
    have hm : CubicSlicingNumerics.projectiveMainTerm (Fintype.card K) 2 =
        (Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1 := by
      simp [CubicSlicingNumerics.projectiveMainTerm, Finset.sum_range_succ] <;> ring
    rw [hm] at hsq
    have hb : |(Nat.card (zeroPoints F) : ℝ) -
        ((Fintype.card K : ℝ)^2 + (Fintype.card K : ℝ) + 1)| ≤
          10 * (Fintype.card K : ℝ) := by
      apply abs_le_of_sq_le_sq _ (by positivity)
      nlinarith [hsq]
    exact hb.trans (mul_le_mul_of_nonneg_right (by norm_num : (10 : ℝ) ≤ 23328) (by positivity))
  · have hs : ∃ x : Fin 4 → AlgebraicClosure K, x ≠ 0 ∧ x ∈ geometricSingularCone F := by
      by_contra! h
      apply hsmooth
      intro x hx
      by_contra hne
      exact h x hne hx
    exact singular_projective_bound ampl F hF h2 h3 hI hNC hs

/-- Uniform affine cubic-surface estimate, with the literal cone main term. -/
theorem affine_bound (ampl : CubicSurfacePointCountAmplification)
    (weil : SmoothCubicWeil) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hI : GeometricallyIntegralForm F) (hNC : GeometricallyNonconicalCubic F) :
    |(affineZeroCount F : ℝ) - (Fintype.card K : ℝ)^3| ≤
      23328 * ((Fintype.card K : ℝ)-1) * (Fintype.card K : ℝ) :=
  affine_bound_of_projective_bound F hF 23328 (projective_bound ampl weil F hF h2 h3 hI hNC)

end CubicTenVariables.CubicSurfacePointCountOfAmplification
