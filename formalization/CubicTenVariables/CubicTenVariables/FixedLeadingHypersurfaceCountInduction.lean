import CubicTenVariables.FixedLeadingFormGoodSurfaceCountReduction

/-!
# Iterated parallel slicing for a fixed homogeneous leading equation

A single homogeneous equation is fixed before its lower coefficients and
leading scalar vary. One fixed integral shear at each dimension reduces its
count to ternary surfaces. No family of saturated central boundaries enters
this counting induction. Existence of the integral shears is a separate
geometric argument supplied explicitly to the final theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace CubicTenVariables.FixedLeadingHypersurfaceCountInduction

open MvPolynomial TranslatedDepthSeven Published
open FixedLeadingFormGoodSurfaceCountReduction FixedLeadingFormIntegralShear
open IntegralShearHypersurfaceCount AffineFourCountByParallelSlices
open HessianTheorem11.PolynomialRestriction

/-- Only the fixed leading equation, rather than every form of its degree,
may enter the counting constant. -/
def FixedRationalLeadingHypersurfaceBounds (n d : ℕ) (ε : ℝ) : Prop :=
  ∀ k : MvPolynomial (Fin n) ℚ,
    k.IsHomogeneous d → IsAbsolutelyIrreducible k →
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : MvPolynomial (Fin n) ℤ) (c : ℚ), c ≠ 0 →
        IsTopHomogeneousPart g (MvPolynomial.C c * k) d →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
            C * B ^ ((n : ℝ) - 2 + ε)

theorem surface_base {d : ℕ} {ε : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d ε) :
    FixedRationalLeadingHypersurfaceBounds 3 d ε := by
  intro k hk hirr
  simpa only [Nat.cast_ofNat, show (3 : ℝ) - 2 = 1 by norm_num] using
    rational_surface_bound_of_integral_surface_bounds hsurface k hk hirr

/-- One fixed good shear lifts the exponent by one through literal
parallel affine slices; all lower coefficients and scalars remain uniform. -/
theorem successor_of_integral_shear
    {n d : ℕ} {ε : ℝ}
    (hprevious : FixedRationalLeadingHypersurfaceBounds n d ε)
    (hshear : ∀ k : MvPolynomial (Fin (n + 1)) ℚ,
      k.IsHomogeneous d → IsAbsolutelyIrreducible k →
      ∃ a : Fin n → ℤ, IsAbsolutelyIrreducible
        (rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k))) :
    FixedRationalLeadingHypersurfaceBounds (n + 1) d ε := by
  intro k hk hirr
  obtain ⟨a, ha⟩ := hshear k hk hirr
  let K := rationalSpecializeFirstCoordinate 0
    (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k)
  have hKhom : K.IsHomogeneous d := by
    dsimp only [K]
    rw [← restrict_graphFrame_eq_shear_slice]
    exact homogeneous_restrict _ _ hk
  obtain ⟨C₀, hC₀, hcount⟩ := hprevious K hKhom ha
  let β : ℝ := ((n + 1 : ℕ) : ℝ) - 2 + ε
  let C₁ := (5 * C₀) * firstCoordinateShearBoxFactor a ^ β
  have hfactor : 0 < firstCoordinateShearBoxFactor a := by
    linarith [one_le_firstCoordinateShearBoxFactor a]
  refine ⟨C₁, mul_pos (mul_pos (by norm_num) hC₀)
    (Real.rpow_pos_of_pos hfactor _), ?_⟩
  intro g c hc htop B hB
  apply affineHypersurface_bound_of_firstCoordinateShear a g B (5 * C₀) β hB
  have hscaled : 1 ≤ firstCoordinateShearBoxFactor a * B :=
    one_le_mul_of_one_le_of_one_le (one_le_firstCoordinateShearBoxFactor a) hB
  have hsheared := isTopHomogeneousPart_firstCoordinateShearPolynomialEquiv a htop
  have hsection : rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) (C c * k)) = C c * K := by
    simp [K, firstCoordinateShearPolynomialEquiv_apply, rationalSpecializeFirstCoordinate]
  have hslices : ∀ t : ℤ, |(t : ℝ)| ≤ firstCoordinateShearBoxFactor a * B →
      ((affineHypersurfaceIntegerPoints
        (integralSpecializeFirstCoordinate t (firstCoordinateShearPolynomialEquiv a g))
        (firstCoordinateShearBoxFactor a * B)).card : ℝ) ≤
      C₀ * (firstCoordinateShearBoxFactor a * B) ^ ((n : ℝ) - 2 + ε) := by
    intro t _ht
    apply hcount _ c hc _ _ hscaled
    have hs := isTopHomogeneousPart_integralSpecializeFirstCoordinate t hsheared
      (show rationalSpecializeFirstCoordinate 0
        (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) (C c * k)) ≠ 0 from
        by rw [hsection]; exact mul_ne_zero (C_ne_zero.mpr hc) ha.ne_zero)
    rwa [hsection] at hs
  have h := affineHypersurface_card_le_of_parallelSlice_bounds
    (firstCoordinateShearPolynomialEquiv a g) (firstCoordinateShearBoxFactor a * B)
      C₀ ((n : ℝ) - 2 + ε) hscaled hC₀.le hslices
  have he : (n : ℝ) - 2 + ε + 1 = β := by dsimp [β]; push_cast; ring
  simpa only [he] using h

/-- Repeated fixed shears reduce every dimension at least three to the
same scalar-uniform ternary surface theorem. -/
theorem all_dimensions_of_integral_shears
    {d : ℕ} {ε : ℝ}
    (hsurface : FixedIntegralLeadingSurfaceBounds d ε)
    (hshear : ∀ n : ℕ, 3 ≤ n →
      ∀ k : MvPolynomial (Fin (n + 1)) ℚ,
        k.IsHomogeneous d → IsAbsolutelyIrreducible k →
        ∃ a : Fin n → ℤ, IsAbsolutelyIrreducible
          (rationalSpecializeFirstCoordinate 0
            (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k))) :
    ∀ n : ℕ, 3 ≤ n → FixedRationalLeadingHypersurfaceBounds n d ε := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact surface_base hsurface
  | succ n hn ih => exact successor_of_integral_shear ih (hshear n hn)

end CubicTenVariables.FixedLeadingHypersurfaceCountInduction
