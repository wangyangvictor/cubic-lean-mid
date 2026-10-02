import CubicTenVariables.IntegralShearHypersurfaceCount
import CubicTenVariables.GoodSurfaceFibreFiniteLeadingForms

/-!
# Uniform counts for the actual finite leading-form family

One suitable integral shear and one surface constant for each member of a
finite leading-form menu suffice for a single four-variable bound. The
constant is chosen before the lower coefficients, the leading scalar, and
the height. The second theorem applies this reduction to the actual
simultaneous source--boundary projection equations, including all integral
translations and positive progression moduli.

The surface estimates in the hypotheses are still unproved. This assembly
does not invoke Salberger or supply a new counting input implicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace CubicTenVariables.FiniteLeadingFormSurfaceCountAssembly

open MvPolynomial TranslatedDepthSeven Published
open IntegralShearHypersurfaceCount GoodSurfaceFibreFiniteLeadingForms
open GoodSurfaceFibreSimultaneousBoundaryProjection
open GoodSurfaceFibreAffineFourStaticProjection
open scoped BigOperators

/-- Finite aggregation of the exact sheared surface bounds. In particular,
the shear coefficients need no bound uniform over all degree-`d` forms. -/
theorem finite_leadingFormMenu_affineFour_count
    (d : ℕ) (epsilon : ℝ)
    (menu : Finset (MvPolynomial (Fin 4) ℚ))
    (hlocal : ∀ H ∈ menu, ∃ (a : Fin 3 → ℤ) (C : ℝ), 0 < C ∧
      rationalSpecializeFirstCoordinate 0
        (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H) ≠ 0 ∧
      ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart g
          (MvPolynomial.C c * rationalSpecializeFirstCoordinate 0
            (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
            C * B ^ (1 + epsilon)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 4) ℤ) (H : MvPolynomial (Fin 4) ℚ),
        H ∈ menu → ∀ c : ℚ, c ≠ 0 →
          IsTopHomogeneousPart f (MvPolynomial.C c * H) d →
          ∀ B : ℝ, 1 ≤ B →
            ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
              C * B ^ (2 + epsilon) := by
  classical
  let Form := {H : MvPolynomial (Fin 4) ℚ // H ∈ menu}
  have hEach : ∀ H : Form, ∃ D : ℝ, 0 < D ∧
      ∀ (f : MvPolynomial (Fin 4) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart f (MvPolynomial.C c * H.1) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
            D * B ^ (2 + epsilon) := by
    intro H
    obtain ⟨a, C, hC, hnonzero, hsurface⟩ := hlocal H.1 H.2
    refine ⟨(5 * C) * firstCoordinateShearBoxFactor a ^ (2 + epsilon), ?_, ?_⟩
    · have hK : 0 < firstCoordinateShearBoxFactor a := by
        linarith [one_le_firstCoordinateShearBoxFactor a]
      exact mul_pos (mul_pos (by norm_num) hC) (Real.rpow_pos_of_pos hK _)
    · intro f c hc htop B hB
      exact affineFour_bound_of_sheared_scalar_leading_surface_bound
        d epsilon C hC.le a H.1 hnonzero hsurface f c hc htop B hB
  choose D hD hbound using hEach
  let C : ℝ := 1 + ∑ H : Form, D H
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ H : Form, D H :=
      Finset.sum_nonneg fun H _ => (hD H).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro f H hH c hc htop B hB
  let H' : Form := ⟨H, hH⟩
  have hDsum : D H' ≤ ∑ G : Form, D G :=
    Finset.single_le_sum (fun G _ => (hD G).le) (Finset.mem_univ H')
  have hDC : D H' ≤ C := by
    dsimp only [C]
    linarith
  exact (hbound H' f c hc htop B hB).trans
    (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (by linarith) _))

/-- The fixed saturated boundary, rather than the varying affine equation,
controls the choice of the common constant. Every source equation below is
the literal output of the existing finite projection menu. -/
theorem fixed_saturatedBoundary_dynamic_count_of_surface_bounds
    (d : ℕ) (epsilon : ℝ)
    (boundary : Ideal (MvPolynomial (Fin 10) ℚ))
    (hprime : boundary.IsPrime)
    (hgeometric : GeometricallyPrimeMvPolynomialIdeal boundary)
    (hlocal : ∀ H : MvPolynomial (Fin 4) ℚ,
      H.IsHomogeneous d → IsAbsolutelyIrreducible H →
      ∃ (a : Fin 3 → ℤ) (C : ℝ), 0 < C ∧
        rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H) ≠ 0 ∧
        ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
          IsTopHomogeneousPart g
            (MvPolynomial.C c * rationalSpecializeFirstCoordinate 0
              (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) H)) d →
          ∀ B : ℝ, 1 ≤ B →
            ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
              C * B ^ (1 + epsilon)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Ideal (MvPolynomial (Fin 10) ℚ))
        (_hIB : projectiveBoundaryIdeal (affineIdealProjectiveClosure J) ≤ boundary)
        (w : SimultaneousSourceSaturatedBoundaryMenuProjection J boundary d)
        (base : IntVector 4) (m : ℕ), 0 < m →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints
            (integralAffineTransform base m
              (affineChartProjectionEquation w.sourceEquation)) B).card : ℝ) ≤
                C * B ^ (2 + epsilon) := by
  obtain ⟨menu, _hcard, hforms, htopMenu⟩ :=
    exists_finite_saturatedBoundary_dynamic_topPart_menu d boundary hprime hgeometric
  obtain ⟨C, hC, hcount⟩ := finite_leadingFormMenu_affineFour_count d epsilon menu
    (fun H hH => hlocal H (hforms H hH).1 (hforms H hH).2)
  refine ⟨C, hC, ?_⟩
  intro J hIB w base m hm B hB
  obtain ⟨H, hH, c, hc, htop⟩ := htopMenu J hIB w base m hm
  exact hcount _ H hH c hc htop B hB

end CubicTenVariables.FiniteLeadingFormSurfaceCountAssembly
