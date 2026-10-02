import CubicTenVariables.AffineHypersurfaceParallelSliceTopPart
import TranslatedDepthSeven.IntegerBoxCount

/-!
# The dimension-correct parallel-slice count

A four-variable affine hypersurface is counted by its literal three-variable
parallel slices. When the restriction of its leading form to the slicing
hyperplane is absolutely irreducible, every slice has that same leading
form and degree. A coefficient-uniform surface estimate then gives the
required threefold exponent, with no exceptional parameter set.

The coefficient-uniform surface estimate and the choice of a suitable
bounded slicing direction are not proved here. They remain separate tasks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace CubicTenVariables.AffineFourCountByParallelSlices

open TranslatedDepthSeven Published MvPolynomial
open scoped BigOperators

theorem mem_affineHypersurfaceIntegerPoints_iff
    {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (B : ℝ) (x : IntVector n) :
    x ∈ affineHypersurfaceIntegerPoints f B ↔
      (∀ i, |(x i : ℝ)| ≤ B) ∧ eval x f = 0 := by
  classical
  simp only [affineHypersurfaceIntegerPoints, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_integerSupNormBox_iff]
    intro i
    have hx : ((x i).natAbs : ℝ) ≤ (⌈B⌉₊ : ℝ) := by
      calc
        ((x i).natAbs : ℝ) = |(x i : ℝ)| := by simp
        _ ≤ B := h.1 i
        _ ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
    exact_mod_cast hx

/-- Deleting the fixed first coordinate injects a literal integer-point
fibre into the integer points of the specialized polynomial. -/
theorem affineHypersurface_firstCoordinate_fibre_card_le
    {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ) (B : ℝ) (t : ℤ) :
    ((affineHypersurfaceIntegerPoints f B).filter fun x => x 0 = t).card ≤
      (affineHypersurfaceIntegerPoints
        (integralSpecializeFirstCoordinate t f) B).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun x i => x i.succ)
  · intro x hx
    obtain ⟨hx, ht⟩ := Finset.mem_filter.mp hx
    have hxspec := (mem_affineHypersurfaceIntegerPoints_iff f B x).mp hx
    apply (mem_affineHypersurfaceIntegerPoints_iff _ _ _).mpr
    refine ⟨fun i => hxspec.1 i.succ, ?_⟩
    rw [eval_integralSpecializeFirstCoordinate]
    have heq : Fin.cases t (fun i => x i.succ) = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ht.symm
      · rfl
    rw [heq]
    exact hxspec.2
  · intro x hx y hy hxy
    have hxt := (Finset.mem_filter.mp hx).2
    have hyt := (Finset.mem_filter.mp hy).2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hxt.trans hyt.symm
    · exact congrFun hxy j

/-- Counting by the actual first coordinate loses at most `5B` for `B≥1`.
The estimate is uniform in all coefficients of the polynomial. -/
theorem affineHypersurface_card_le_of_parallelSlice_bounds
    {n : ℕ} (f : MvPolynomial (Fin (n + 1)) ℤ)
    (B C alpha : ℝ) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hslices : ∀ t : ℤ, |(t : ℝ)| ≤ B →
      ((affineHypersurfaceIntegerPoints
        (integralSpecializeFirstCoordinate t f) B).card : ℝ) ≤
          C * B ^ alpha) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      (5 * C) * B ^ (alpha + 1) := by
  classical
  let S := affineHypersurfaceIntegerPoints f B
  let Y := S.image (fun x => x 0)
  have hYS : Y ⊆ Finset.Icc (-(⌈B⌉₊ : ℤ)) (⌈B⌉₊ : ℤ) := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hxbox := (Finset.mem_filter.mp hx).1
    have hz := (mem_integerSupNormBox_iff x).mp hxbox 0
    rw [Finset.mem_Icc]
    omega
  have hYcard : Y.card ≤ 2 * ⌈B⌉₊ + 1 := by
    have h := Finset.card_le_card hYS
    rw [Int.card_Icc] at h
    omega
  have hceil : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one (by linarith)
  have hYreal : (Y.card : ℝ) ≤ 5 * B := by
    have hcast : (Y.card : ℝ) ≤ 2 * (⌈B⌉₊ : ℝ) + 1 := by exact_mod_cast hYcard
    linarith
  have hcard := Finset.card_eq_sum_card_image (fun x : IntVector (n + 1) => x 0) S
  have hcardR : (S.card : ℝ) =
      ∑ t ∈ Y, ((S.filter fun x => x 0 = t).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (S.card : ℝ) =
        ∑ t ∈ Y, ((S.filter fun x => x 0 = t).card : ℝ) := hcardR
    _ ≤ ∑ _t ∈ Y, C * B ^ alpha := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨x, hx, hxt⟩ := Finset.mem_image.mp ht
      have htB : |(t : ℝ)| ≤ B := by
        rw [← hxt]
        exact ((mem_affineHypersurfaceIntegerPoints_iff f B x).mp hx).1 0
      have hfibre : ((S.filter fun x => x 0 = t).card : ℝ) ≤
          ((affineHypersurfaceIntegerPoints
            (integralSpecializeFirstCoordinate t f) B).card : ℝ) := by
        exact_mod_cast affineHypersurface_firstCoordinate_fibre_card_le f B t
      exact hfibre.trans (hslices t htB)
    _ = (Y.card : ℝ) * (C * B ^ alpha) := by simp
    _ ≤ (5 * B) * (C * B ^ alpha) :=
      mul_le_mul_of_nonneg_right hYreal (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
    _ = (5 * C) * B ^ (alpha + 1) := by
      rw [Real.rpow_add (by linarith : 0 < B), Real.rpow_one]
      ring

/-- The exact four-to-three-coordinate reduction needed for the n=10
Salberger route, for a coordinate direction with integral leading section.
The only counting premise is a uniform estimate for three-variable
polynomials; all four-variable counting is proved here. -/
theorem affineFour_card_le_of_uniform_surface_bound
    (d : ℕ) (epsilon C : ℝ) (hC : 0 ≤ C)
    (hsurface : ∀ (g : MvPolynomial (Fin 3) ℤ)
      (k : MvPolynomial (Fin 3) ℚ),
      IsTopHomogeneousPart g k d → IsAbsolutelyIrreducible k →
      ∀ B : ℝ, 1 ≤ B →
        ((affineHypersurfaceIntegerPoints g B).card : ℝ) ≤
          C * B ^ (1 + epsilon))
    (f : MvPolynomial (Fin 4) ℤ) (h : MvPolynomial (Fin 4) ℚ)
    (htop : IsTopHomogeneousPart f h d)
    (hintegral : IsAbsolutelyIrreducible
      (rationalSpecializeFirstCoordinate 0 h))
    (B : ℝ) (hB : 1 ≤ B) :
    ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
      (5 * C) * B ^ (2 + epsilon) := by
  have hnonzero : rationalSpecializeFirstCoordinate 0 h ≠ 0 := by
    exact hintegral.ne_zero
  have hcount := affineHypersurface_card_le_of_parallelSlice_bounds
    f B C (1 + epsilon) hB hC (by
      intro t _ht
      exact hsurface (integralSpecializeFirstCoordinate t f)
        (rationalSpecializeFirstCoordinate 0 h)
        (isTopHomogeneousPart_integralSpecializeFirstCoordinate t htop hnonzero)
        hintegral B hB)
  simpa only [show (1 + epsilon) + 1 = 2 + epsilon by ring] using hcount

end CubicTenVariables.AffineFourCountByParallelSlices
