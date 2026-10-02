import TranslatedDepthSeven.HypersurfaceSmoothPrimeReservoir
import TranslatedDepthSeven.BadReductionIncidenceLoss

/-!
# Actual hypersurface gradients control bad-reduction incidence

The bad-prime set is defined by simultaneous vanishing of the three actual
affine partial derivatives of a fixed integral equation. At a point with
nonzero integer gradient, its product divides the absolute value of any
nonzero partial. Polynomial height bounds therefore supply the row-product
input to the weighted incidence estimate internally.

No equation-of-the-point hypothesis is needed for this stronger gradient
statement. It applies in particular to points on the fixed hypersurface.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- A prime is bad at the displayed point exactly when all three actual
partials of the first-chart equation vanish modulo that prime. -/
def hypersurfaceAffineGradientBadReduction
    (F : MvPolynomial (Fin 4) ℤ) (x : Fin 3 → ℤ) (p : ℕ) : Prop :=
  ∀ v : Fin 3,
    (MvPolynomial.eval x
      (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) :
        ZMod p) = 0

/-- Every bad prime divides a chosen nonzero integral partial, and the
distinct-prime product is bounded by its absolute value. -/
theorem hypersurface_badPrimeProduct_le_partial_natAbs
    (F : MvPolynomial (Fin 4) ℤ) (x : Fin 3 → ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : Fin 3)
    (hv : MvPolynomial.eval x
      (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) :
    letI : DecidablePred (hypersurfaceAffineGradientBadReduction F x) :=
      Classical.decPred _
    (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p) ≤
      (MvPolynomial.eval x
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F))).natAbs := by
  classical
  let J := MvPolynomial.eval x
    (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F))
  have hdiv : primeProduct (P.filter (hypersurfaceAffineGradientBadReduction F x)) ∣
      J.natAbs := by
    apply primeProduct_dvd_of_each_dvd hP (Finset.filter_subset _ _)
    intro p hp
    have hbad := (Finset.mem_filter.mp hp).2 v
    exact Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd J p).mp hbad)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hdiv

/-- The exponent and height threshold are chosen from the fixed equation
before the prime family and the point. No row-product estimate is supplied. -/
theorem exists_hypersurface_badPrimeProduct_height_bound
    (F : MvPolynomial (Fin 4) ℤ) :
    ∃ A H₀ : ℕ, 2 ≤ A ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → ∀ x : Fin 3 → ℤ,
      (∀ i, (x i).natAbs ≤ H) →
      (∃ v, MvPolynomial.eval x
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      letI : DecidablePred (hypersurfaceAffineGradientBadReduction F x) :=
        Classical.decPred _
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p) ≤ H ^ A := by
  classical
  obtain ⟨A, C, hA, hC, hheight⟩ := exists_hypersurface_gradient_certificate_height F 1
  refine ⟨A, max 2 C, hA, Nat.le_max_left _ _, ?_⟩
  intro H hH P hP x hx hgrad
  obtain ⟨v, hv⟩ := hgrad
  exact (hypersurface_badPrimeProduct_le_partial_natAbs F x P hP v hv).trans
    ((hheight H ((Nat.le_max_right _ _).trans hH)).2 x hx v)

/-- The actual bad-gradient incidence bound on every sufficiently large
integral box. The same fixed `A` controls the bad-prime product of every
point and the summed logarithmic incidence cost. -/
theorem exists_hypersurface_badReduction_incidence_bound
    (F : MvPolynomial (Fin 4) ℤ) :
    ∃ A H₀ : ℕ, 2 ≤ A ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ)) →
      ∀ X : Finset (Fin 3 → ℤ),
      (∀ x ∈ X, ∀ i, (x i).natAbs ≤ H) →
      (∀ x ∈ X, ∃ v, MvPolynomial.eval x
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      letI : DecidableRel (hypersurfaceAffineGradientBadReduction F) :=
        fun _ _ => Classical.propDecidable _
      (∀ x ∈ X,
        (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p) ≤ H ^ A) ∧
      (∑ p ∈ P,
        ((X.filter fun x => hypersurfaceAffineGradientBadReduction F x p).card : ℝ) *
          Real.log (p : ℝ) / (p : ℝ)) ≤ (A : ℝ) * X.card ∧
      (∑ p ∈ P,
        (Real.sqrt 2 *
          ((X.filter fun x => hypersurfaceAffineGradientBadReduction F x p).card : ℝ) *
          Real.sqrt (X.card : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) ≤
        Real.sqrt 2 * A * ((X.card : ℝ) * Real.sqrt (X.card : ℝ)) := by
  classical
  obtain ⟨A, H₀, hA, hH₀, hproduct⟩ := exists_hypersurface_badPrimeProduct_height_bound F
  refine ⟨A, H₀, hA, hH₀, ?_⟩
  intro H hH P hP hlarge X hbox hgrad
  have hprod (x : Fin 3 → ℤ) (hx : x ∈ X) :
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p) ≤ H ^ A :=
    hproduct H hH P hP x (hbox x hx) (hgrad x hx)
  have hprodR (x : Fin 3 → ℤ) (hx : x ∈ X) :
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), (p : ℝ)) ≤
        (H : ℝ) ^ (A : ℝ) := by
    rw [Real.rpow_natCast]
    have hcast : ((∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F x), p : ℕ) : ℝ) ≤
        ((H ^ A : ℕ) : ℝ) := by exact_mod_cast hprod x hx
    simpa only [Nat.cast_prod, Nat.cast_pow] using hcast
  have hHone : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  exact ⟨hprod,
    log_badReduction_incidence_le_of_row_products X P
      (hypersurfaceAffineGradientBadReduction F) H A hHone
      (fun p hp => (hP p hp).pos) hlarge hprodR,
    smoothSurface_discard_log_loss_le_of_row_products X P
      (hypersurfaceAffineGradientBadReduction F) H A hHone
      (fun p hp => (hP p hp).pos) hlarge hprodR⟩

/-- Column-indexed form of the same bound. The constants precede the
finite index type and the literal coordinate map, which need not be
injective. Repeated physical points are counted with their column
multiplicities on both sides. -/
theorem exists_hypersurface_badReduction_column_bound
    (F : MvPolynomial (Fin 4) ℤ) :
    ∃ A H₀ : ℕ, 2 ≤ A ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Real.log (H : ℝ) ≤ (p : ℝ)) →
      ∀ (ι : Type*) [Fintype ι] (y : ι → Fin 3 → ℤ),
      (∀ j i, (y j i).natAbs ≤ H) →
      (∀ j, ∃ v, MvPolynomial.eval (y j)
        (MvPolynomial.pderiv v (surfaceHypersurfaceFirstChartDehomogenize F)) ≠ 0) →
      letI : DecidableRel (fun j p => hypersurfaceAffineGradientBadReduction F (y j) p) :=
        fun _ _ => Classical.propDecidable _
      (∀ j,
        (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), p) ≤ H ^ A) ∧
      (∑ p ∈ P,
        ((Finset.univ.filter fun j => hypersurfaceAffineGradientBadReduction F (y j) p).card : ℝ) *
          Real.log (p : ℝ) / (p : ℝ)) ≤ (A : ℝ) * Fintype.card ι ∧
      (∑ p ∈ P,
        (Real.sqrt 2 *
          ((Finset.univ.filter fun j => hypersurfaceAffineGradientBadReduction F (y j) p).card : ℝ) *
          Real.sqrt (Fintype.card ι : ℝ) / (p : ℝ)) * Real.log (p : ℝ)) ≤
        Real.sqrt 2 * A * ((Fintype.card ι : ℝ) * Real.sqrt (Fintype.card ι : ℝ)) := by
  classical
  obtain ⟨A, H₀, hA, hH₀, hproduct⟩ := exists_hypersurface_badPrimeProduct_height_bound F
  refine ⟨A, H₀, hA, hH₀, ?_⟩
  intro H hH P hP hlarge ι inst y hbox hgrad
  have hprod (j : ι) :
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), p) ≤ H ^ A :=
    hproduct H hH P hP (y j) (hbox j) (hgrad j)
  have hprodR (j : ι) (_hj : j ∈ (Finset.univ : Finset ι)) :
      (∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), (p : ℝ)) ≤
        (H : ℝ) ^ (A : ℝ) := by
    rw [Real.rpow_natCast]
    have hcast : ((∏ p ∈ P.filter (hypersurfaceAffineGradientBadReduction F (y j)), p : ℕ) : ℝ) ≤
        ((H ^ A : ℕ) : ℝ) := by exact_mod_cast hprod j
    simpa only [Nat.cast_prod, Nat.cast_pow] using hcast
  have hHone : (1 : ℝ) < H := by exact_mod_cast (show 1 < H by omega)
  refine ⟨hprod, ?_, ?_⟩
  · simpa only [Finset.card_univ] using
      log_badReduction_incidence_le_of_row_products Finset.univ P
        (fun j => hypersurfaceAffineGradientBadReduction F (y j)) H A hHone
        (fun p hp => (hP p hp).pos) hlarge hprodR
  · simpa only [Finset.card_univ] using
      smoothSurface_discard_log_loss_le_of_row_products Finset.univ P
        (fun j => hypersurfaceAffineGradientBadReduction F (y j)) H A hHone
        (fun p hp => (hP p hp).pos) hlarge hprodR

end
end TranslatedDepthSeven
