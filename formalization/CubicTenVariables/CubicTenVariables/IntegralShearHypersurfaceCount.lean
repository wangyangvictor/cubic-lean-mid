import CubicTenVariables.IntegralFirstCoordinateShear
import CubicTenVariables.AffineFourCountByParallelSlices

/-!
# Integer-point counts under a slicing shear

The shear used to choose a slicing hyperplane is an exact integral change
of coordinates. Its inverse enlarges the box by the explicit factor
`1 + sum |a_i|`. This gives a count transfer with no index loss or extra
residue classes. Choosing suitable uniformly bounded coefficients and
proving the surface estimate remain separate obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace CubicTenVariables.IntegralShearHypersurfaceCount

open TranslatedDepthSeven Published MvPolynomial
open AffineFourCountByParallelSlices
open scoped BigOperators

/-- The exact row-sum bound needed for the first-coordinate shear. -/
def firstCoordinateShearBoxFactor {n : ℕ} (a : Fin n → ℤ) : ℝ :=
  1 + ∑ i, |(a i : ℝ)|

theorem one_le_firstCoordinateShearBoxFactor {n : ℕ} (a : Fin n → ℤ) :
    1 ≤ firstCoordinateShearBoxFactor a := by
  have hsum : 0 ≤ ∑ i, |(a i : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold firstCoordinateShearBoxFactor
  linarith

@[simp] theorem firstCoordinateShearBoxFactor_neg {n : ℕ} (a : Fin n → ℤ) :
    firstCoordinateShearBoxFactor (-a) = firstCoordinateShearBoxFactor a := by
  simp [firstCoordinateShearBoxFactor]

theorem firstCoordinateShear_mem_realBox {n : ℕ}
    (a : Fin n → ℤ) (x : IntVector (n + 1)) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ i, |(x i : ℝ)| ≤ B) :
    ∀ i, |(firstCoordinateShear (R := ℤ) a x i : ℝ)| ≤
      firstCoordinateShearBoxFactor a * B := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |((x 0 + ∑ j, a j * x j.succ : ℤ) : ℝ)| ≤ _
    push_cast
    calc
      |(x 0 : ℝ) + ∑ j, (a j : ℝ) * (x j.succ : ℝ)|
          ≤ |(x 0 : ℝ)| + |∑ j, (a j : ℝ) * (x j.succ : ℝ)| := abs_add_le _ _
      _ ≤ B + ∑ j, |(a j : ℝ) * (x j.succ : ℝ)| :=
        add_le_add (hx 0) (Finset.abs_sum_le_sum_abs _ _)
      _ = B + ∑ j, |(a j : ℝ)| * |(x j.succ : ℝ)| := by simp only [abs_mul]
      _ ≤ B + ∑ j, |(a j : ℝ)| * B := by
        exact add_le_add le_rfl (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hx j.succ) (abs_nonneg _))
      _ = firstCoordinateShearBoxFactor a * B := by
        rw [← Finset.sum_mul]
        simp only [firstCoordinateShearBoxFactor]
        ring
  · change |(x j.succ : ℝ)| ≤ _
    exact (hx j.succ).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (one_le_firstCoordinateShearBoxFactor a) hB)

/-- The inverse integral shear injects the original zero set into the
transformed zero set in its explicitly enlarged box. -/
theorem affineHypersurface_card_le_firstCoordinateShear {n : ℕ}
    (a : Fin n → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ)
    (B : ℝ) (hB : 0 ≤ B) :
    (affineHypersurfaceIntegerPoints f B).card ≤
      (affineHypersurfaceIntegerPoints
        (firstCoordinateShearPolynomialEquiv a f)
        (firstCoordinateShearBoxFactor a * B)).card := by
  classical
  apply Finset.card_le_card_of_injOn (firstCoordinateShear (-a))
  · intro x hx
    have hxspec := (mem_affineHypersurfaceIntegerPoints_iff f B x).mp hx
    apply (mem_affineHypersurfaceIntegerPoints_iff _ _ _).mpr
    refine ⟨?_, ?_⟩
    · simpa only [firstCoordinateShearBoxFactor_neg] using
        firstCoordinateShear_mem_realBox (-a) x B hB hxspec.1
    · rw [eval_firstCoordinateShearPolynomialEquiv,
        firstCoordinateShear_neg_right]
      exact hxspec.2
  · exact fun _ _ _ _ h => firstCoordinateShear_injective (-a) h

/-- A bound for the sheared equation transfers back with only the explicit
constant `K^alpha`, and with the same exponent of the original height. -/
theorem affineHypersurface_bound_of_firstCoordinateShear {n : ℕ}
    (a : Fin n → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ)
    (B C alpha : ℝ) (hB : 1 ≤ B)
    (hcount : ((affineHypersurfaceIntegerPoints
      (firstCoordinateShearPolynomialEquiv a f)
      (firstCoordinateShearBoxFactor a * B)).card : ℝ) ≤
        C * (firstCoordinateShearBoxFactor a * B) ^ alpha) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      (C * firstCoordinateShearBoxFactor a ^ alpha) * B ^ alpha := by
  have hB0 : 0 ≤ B := by linarith
  have hK : 0 ≤ firstCoordinateShearBoxFactor a :=
    (by linarith [one_le_firstCoordinateShearBoxFactor a])
  have hcard : ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      ((affineHypersurfaceIntegerPoints
        (firstCoordinateShearPolynomialEquiv a f)
        (firstCoordinateShearBoxFactor a * B)).card : ℝ) := by
    exact_mod_cast affineHypersurface_card_le_firstCoordinateShear a f B hB0
  calc
    ((affineHypersurfaceIntegerPoints f B).card : ℝ)
        ≤ C * (firstCoordinateShearBoxFactor a * B) ^ alpha := hcard.trans hcount
    _ = (C * firstCoordinateShearBoxFactor a ^ alpha) * B ^ alpha := by
      rw [Real.mul_rpow hK hB0]
      ring

/-- Only the one leading form shared by the parallel slices needs a
uniform surface estimate. The lower-degree coefficients may vary freely.
In particular this reduction does not require uniformity over all leading
forms of the same degree. -/
theorem affineFour_bound_of_sheared_fixed_leading_surface_bound
    (d : ℕ) (epsilon C : ℝ) (hC : 0 ≤ C)
    (a : Fin 3 → ℤ)
    (f : MvPolynomial (Fin 4) ℤ) (h : MvPolynomial (Fin 4) ℚ)
    (htop : IsTopHomogeneousPart f h d)
    (hnonzero : rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) h) ≠ 0)
    (hsurface : ∀ g : MvPolynomial (Fin 3) ℤ,
      IsTopHomogeneousPart g
        (rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) h)) d →
      ∀ B : ℝ, 1 ≤ B →
        ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
          C * B ^ (1 + epsilon))
    (B : ℝ) (hB : 1 ≤ B) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      ((5 * C) * firstCoordinateShearBoxFactor a ^ (2 + epsilon)) *
        B ^ (2 + epsilon) := by
  apply affineHypersurface_bound_of_firstCoordinateShear a f B
    (5 * C) (2 + epsilon) hB
  have hscaled : 1 ≤ firstCoordinateShearBoxFactor a * B := by
    calc
      1 ≤ B := hB
      _ ≤ firstCoordinateShearBoxFactor a * B := by
        simpa using mul_le_mul_of_nonneg_right
          (one_le_firstCoordinateShearBoxFactor a) (by linarith : 0 ≤ B)
  have hshear := isTopHomogeneousPart_firstCoordinateShearPolynomialEquiv a htop
  have hcount := affineHypersurface_card_le_of_parallelSlice_bounds
    (firstCoordinateShearPolynomialEquiv a f)
    (firstCoordinateShearBoxFactor a * B) C (1 + epsilon) hscaled hC (by
      intro t _ht
      exact hsurface
        (integralSpecializeFirstCoordinate t (firstCoordinateShearPolynomialEquiv a f))
        (isTopHomogeneousPart_integralSpecializeFirstCoordinate t hshear hnonzero)
        (firstCoordinateShearBoxFactor a * B) hscaled)
  simpa only [show (1 + epsilon) + 1 = 2 + epsilon by ring] using hcount

/-- Uniformity over nonzero scalar multiples is sufficient for the finite
leading-form menus arising from saturated boundary projections. One shear
and one surface constant serve every scalar and every lower-degree part. -/
theorem affineFour_bound_of_sheared_scalar_leading_surface_bound
    (d : ℕ) (epsilon C : ℝ) (hC : 0 ≤ C)
    (a : Fin 3 → ℤ) (k : MvPolynomial (Fin 4) ℚ)
    (hnonzero : rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k) ≠ 0)
    (hsurface : ∀ (g : MvPolynomial (Fin 3) ℤ) (c : ℚ), c ≠ 0 →
      IsTopHomogeneousPart g
        (MvPolynomial.C c * rationalSpecializeFirstCoordinate 0
          (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k)) d →
      ∀ B : ℝ, 1 ≤ B →
        ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
          C * B ^ (1 + epsilon))
    (f : MvPolynomial (Fin 4) ℤ) (c : ℚ) (hc : c ≠ 0)
    (htop : IsTopHomogeneousPart f (MvPolynomial.C c * k) d)
    (B : ℝ) (hB : 1 ≤ B) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      ((5 * C) * firstCoordinateShearBoxFactor a ^ (2 + epsilon)) *
        B ^ (2 + epsilon) := by
  have hsection : rationalSpecializeFirstCoordinate 0
      (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ))
        (MvPolynomial.C c * k)) =
      MvPolynomial.C c * rationalSpecializeFirstCoordinate 0
        (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) k) := by
    simp [firstCoordinateShearPolynomialEquiv_apply,
      rationalSpecializeFirstCoordinate]
  apply affineFour_bound_of_sheared_fixed_leading_surface_bound d epsilon C hC
    a f (MvPolynomial.C c * k) htop ?_ ?_ B hB
  · rw [hsection]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hc) hnonzero
  · intro g hg R hR
    rw [hsection] at hg
    exact hsurface g c hc hg R hR

/-- A suitable integral shear followed by parallel slicing gives the
four-variable bound. The surface constant is chosen before the equations;
the coordinate cost is displayed rather than hidden in an existential. -/
theorem affineFour_bound_of_sheared_uniform_surface_bound
    (d : ℕ) (epsilon C : ℝ) (hC : 0 ≤ C)
    (hsurface : ∀ (g : MvPolynomial (Fin 3) ℤ)
      (k : MvPolynomial (Fin 3) ℚ),
      IsTopHomogeneousPart g k d → IsAbsolutelyIrreducible k →
      ∀ B : ℝ, 1 ≤ B →
        ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
          C * B ^ (1 + epsilon))
    (a : Fin 3 → ℤ)
    (f : MvPolynomial (Fin 4) ℤ) (h : MvPolynomial (Fin 4) ℚ)
    (htop : IsTopHomogeneousPart f h d)
    (hintegral : IsAbsolutelyIrreducible
      (rationalSpecializeFirstCoordinate 0
        (firstCoordinateShearPolynomialEquiv (fun i => (a i : ℚ)) h)))
    (B : ℝ) (hB : 1 ≤ B) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      ((5 * C) * firstCoordinateShearBoxFactor a ^ (2 + epsilon)) *
        B ^ (2 + epsilon) := by
  exact affineFour_bound_of_sheared_fixed_leading_surface_bound d epsilon C hC
    a f h htop hintegral.ne_zero
    (fun g hg R hR => hsurface g _ hg hintegral R hR) B hB

end CubicTenVariables.IntegralShearHypersurfaceCount
