import TranslatedDepthSeven.SmoothSurfaceResidueExponent

/-!
# Controlling the cost of discarding bad reductions

The bad rows at each modulus are counted from a literal finite incidence
relation. A product bound for each individual row controls the total
logarithmic cost across moduli. Primality is not needed for this numerical
step; it belongs to the proof that the product bound holds in an application.
-/

namespace TranslatedDepthSeven
noncomputable section

set_option maxHeartbeats 1000000

/-- Interchange the sums over rows and moduli, paying at most `1 / L` for
each inverse modulus. Only individual row bounds are assumed. -/
theorem weighted_badReduction_incidence_le
    {α β : Type*} (X : Finset α) (P : Finset β)
    (bad : α → β → Prop) [DecidableRel bad]
    (w r : β → ℝ) (L A : ℝ) (hL : 0 < L)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hr : ∀ p ∈ P, L ≤ r p)
    (hrow : ∀ x ∈ X, (∑ p ∈ P.filter (bad x), w p) ≤ A) :
    (∑ p ∈ P, ((X.filter fun x => bad x p).card : ℝ) * w p / r p) ≤
      (X.card : ℝ) * A / L := by
  have hcount (p : β) : ((X.filter fun x => bad x p).card : ℝ) * w p / r p =
      ∑ x ∈ X, if bad x p then w p / r p else 0 := by
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul, mul_div_assoc]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ x ∈ X, A / L := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← Finset.sum_filter]
      calc
        _ ≤ ∑ p ∈ P.filter (bad x), w p / L := by
          apply Finset.sum_le_sum
          intro p hp
          exact div_le_div_of_nonneg_left (hw p (Finset.mem_filter.mp hp).1) hL
            (hr p (Finset.mem_filter.mp hp).1)
        _ = (∑ p ∈ P.filter (bad x), w p) / L := by rw [Finset.sum_div]
        _ ≤ A / L := div_le_div_of_nonneg_right (hrow x hx) hL.le
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc]

/-- Suppose each row has a product of bad moduli at most `H ^ C`, and
all available moduli are at least `log H`. Then their inverse-modulus
weighted logarithmic cost is at most `C` per row. The same statement
therefore applies to any finite set of auxiliary primes. -/
theorem log_badReduction_incidence_le_of_row_products
    {α : Type*} (X : Finset α) (P : Finset ℕ)
    (bad : α → ℕ → Prop) [DecidableRel bad]
    (H C : ℝ) (hH : 1 < H)
    (hp : ∀ p ∈ P, 0 < p)
    (hlarge : ∀ p ∈ P, Real.log H ≤ (p : ℝ))
    (hproduct : ∀ x ∈ X,
      (∏ p ∈ P.filter (bad x), (p : ℝ)) ≤ H ^ C) :
    (∑ p ∈ P, ((X.filter fun x => bad x p).card : ℝ) * Real.log (p : ℝ) /
      (p : ℝ)) ≤ C * (X.card : ℝ) := by
  have hlogH : 0 < Real.log H := Real.log_pos hH
  have hrow (x : α) (hx : x ∈ X) :
      (∑ p ∈ P.filter (bad x), Real.log (p : ℝ)) ≤ C * Real.log H := by
    have hpos (p : ℕ) (hpmem : p ∈ P.filter (bad x)) : (0 : ℝ) < p := by
      exact_mod_cast hp p (Finset.mem_filter.mp hpmem).1
    have hprodpos : (0 : ℝ) < ∏ p ∈ P.filter (bad x), (p : ℝ) :=
      Finset.prod_pos hpos
    have hlog := Real.log_le_log hprodpos (hproduct x hx)
    rw [Real.log_prod (fun p hpmem => (hpos p hpmem).ne'),
      Real.log_rpow (by linarith : 0 < H)] at hlog
    exact hlog
  have hbound := weighted_badReduction_incidence_le X P bad
    (fun p => Real.log (p : ℝ)) (fun p => (p : ℝ))
    (Real.log H) (C * Real.log H) hlogH
    (fun p hpmem => Real.log_nonneg (by exact_mod_cast hp p hpmem)) hlarge hrow
  convert hbound using 1
  field_simp

/-- The explicit bad-column term in the smooth determinant exponent,
summed with `log p`, is at most `sqrt 2 * C * s^(3/2)`. This is the
precise cost when the class-count denominator is the modulus `p`.
It does not assert a point-count estimate for the residue surface. -/
theorem smoothSurface_discard_log_loss_le_of_row_products
    {α : Type*} (X : Finset α) (P : Finset ℕ)
    (bad : α → ℕ → Prop) [DecidableRel bad]
    (H C : ℝ) (hH : 1 < H)
    (hp : ∀ p ∈ P, 0 < p)
    (hlarge : ∀ p ∈ P, Real.log H ≤ (p : ℝ))
    (hproduct : ∀ x ∈ X,
      (∏ p ∈ P.filter (bad x), (p : ℝ)) ≤ H ^ C) :
    (∑ p ∈ P, (Real.sqrt 2 * ((X.filter fun x => bad x p).card : ℝ) *
      Real.sqrt (X.card : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) ≤
      Real.sqrt 2 * C * ((X.card : ℝ) * Real.sqrt (X.card : ℝ)) := by
  have hbound := mul_le_mul_of_nonneg_left
    (log_badReduction_incidence_le_of_row_products X P bad H C hH hp hlarge hproduct)
    (show 0 ≤ Real.sqrt 2 * Real.sqrt (X.card : ℝ) by positivity)
  calc
    _ = (Real.sqrt 2 * Real.sqrt (X.card : ℝ)) *
        ∑ p ∈ P, ((X.filter fun x => bad x p).card : ℝ) * Real.log (p : ℝ) /
          (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpmem
      ring
    _ ≤ _ := by
      convert hbound using 1
      ring

end
end TranslatedDepthSeven
