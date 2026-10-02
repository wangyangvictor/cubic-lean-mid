import TranslatedDepthSeven.BoundedPrimitivePlaneDirection

/-!
# Incidence retained by primitive normalization on a rational line

The bounded-direction construction retains a rational scalar relation.
This file proves that the relation preserves every homogeneous equation
vanishing on the displayed two-vector span.  All assertions concern actual
polynomial evaluations; no geometric incidence assertion is an input.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

theorem eval_map_integralTwoVectorRestriction {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n)
    (a : Fin 2 → ℚ) :
    eval a (map (Int.castRingHom ℚ) (integralTwoVectorRestriction f v w)) =
      eval (fun i ↦ a 0 * (v i : ℚ) + a 1 * (w i : ℚ))
        (map (Int.castRingHom ℚ) f) := by
  rw [← eval₂_eq_eval_map, ← eval₂_eq_eval_map]
  change (aeval a) (integralTwoVectorRestriction f v w) =
    (aeval fun i ↦ a 0 * (v i : ℚ) + a 1 * (w i : ℚ)) f
  unfold integralTwoVectorRestriction
  rw [comp_aeval_apply]
  congr 1
  ext i
  simp [mul_comm]

/-- A zero integral restriction vanishes at every rational point of its
span, not only at integral combinations of its two defining vectors. -/
theorem eval_rationalTwoVectorCombination_eq_zero_of_restriction_eq_zero
    {n : ℕ} (f : MvPolynomial (Fin n) ℤ) (v w : IntVector n)
    (hzero : integralTwoVectorRestriction f v w = 0) (a b : ℚ) :
    eval (fun i ↦ a * (v i : ℚ) + b * (w i : ℚ))
      (map (Int.castRingHom ℚ) f) = 0 := by
  have h := eval_map_integralTwoVectorRestriction f v w ![a, b]
  simp only [hzero, map_zero, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h
  exact h.symm

/-- Primitive normalization preserves every original homogeneous equation
that vanishes on the selected rational line. -/
theorem eval_eq_zero_of_proportional_twoVectorCombination
    {n d : ℕ} (f : MvPolynomial (Fin n) ℤ) (v w h : IntVector n)
    (hf : f.IsHomogeneous d)
    (hzero : integralTwoVectorRestriction f v w = 0)
    (a b : ℤ) (r : ℚ)
    (hscale : ∀ i, (h i : ℚ) = r * ((a * v i + b * w i : ℤ) : ℚ)) :
    eval h f = 0 := by
  let fQ := map (Int.castRingHom ℚ) f
  have hfQ : fQ.IsHomogeneous d := hf.map _
  have hcomb :
      eval (fun i ↦ ((a * v i + b * w i : ℤ) : ℚ)) fQ = 0 := by
    simpa only [Int.cast_add, Int.cast_mul] using
      eval_rationalTwoVectorCombination_eq_zero_of_restriction_eq_zero
        f v w hzero (a : ℚ) (b : ℚ)
  have hscaled := eval_smul_of_isHomogeneous fQ
    (fun i ↦ ((a * v i + b * w i : ℤ) : ℚ)) r d hfQ
  have hresult : eval (fun i ↦ (h i : ℚ)) fQ = 0 := by
    simpa only [← hscale, hcomb, mul_zero] using hscaled
  rw [show eval (fun i ↦ (h i : ℚ)) fQ = ((eval h f : ℤ) : ℚ) from
    (MvPolynomial.map_eval (Int.castRingHom ℚ) h f).symm] at hresult
  exact_mod_cast hresult

end

end TranslatedDepthSeven
