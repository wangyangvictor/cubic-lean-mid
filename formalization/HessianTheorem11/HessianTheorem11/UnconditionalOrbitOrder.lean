import HessianTheorem11.UnconditionalOrbitTargetWeights

/-! Every coefficient of a target equation pulled back to an existing
orbit curve is the evaluation of its literal weight component. The full
target ideal can consequently be tested on one finite degree cutoff. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial ReducedWeightCurve UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

def finiteCurveHom (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ) :
    MvPolynomial (DegreeIndex n d) K →+* Polynomial K :=
  (eval₂Hom Polynomial.C (fun e => Polynomial.C (coeff e F) *
    Polynomial.X ^ (monomialWeight w e).toNat)).comp (rename Subtype.val).toRingHom

@[simp] theorem finiteCurveHom_apply (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (P : MvPolynomial (DegreeIndex n d) K) : finiteCurveHom F w P = finiteCurveTest F w P := rfl

theorem coeff_finiteCurveTest [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (k : ℕ) :
    (finiteCurveTest F w P).coeff k =
      eval (coefficientVector F) (weightPart P (coefficientWeights w) (k : ℤ)) := by
  classical
  let cw := coefficientWeights (d := d) w
  let s := P.support.image (exponentWeight cw)
  have he : finiteCurveTest F w P =
      ∑ a ∈ s, finiteCurveTest F w (weightPart P cw a) := by
    have h := congrArg (finiteCurveHom F w) (sum_weightParts_one P cw)
    simpa only [map_sum,finiteCurveHom_apply] using h.symm
  rw [he,Polynomial.finset_sum_coeff,Finset.sum_eq_single (k : ℤ)]
  · rw [finiteCurveTest_weightPart_of_nonnegative F hF w hW P (k : ℤ) (by omega)]
    simp
  · intro a ha hne
    by_cases hneg : a < 0
    · rw [(finiteCurveTest_weightPart_of_negative F hF w hW P a hneg).2]
      simp
    · rw [finiteCurveTest_weightPart_of_nonnegative F hF w hW P a (by omega)]
      have hak : k ≠ a.toNat := by omega
      simp [Polynomial.coeff_monomial,Ne.symm hak]
  · intro hnot
    rw [weightPart_zero_outside P cw (k : ℤ) hnot]
    simp [finiteCurveTest,curveTest]

theorem all_ideal_pullbacks_dvd_iff_bounded
    (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (S : Set (MvPolynomial (Fin n) K)) (N m : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    (∀ P ∈ vanishingIdeal K (finiteTarget (d := d) S),
      Polynomial.X ^ m ∣ finiteCurveTest F w P) ↔
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N,
      Polynomial.X ^ m ∣ finiteCurveTest F w P.val) := by
  constructor
  · intro h P
    exact h P.val P.property.1
  · intro h P hP
    let J : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ m}
    have hle : vanishingIdeal K (finiteTarget (d := d) S) ≤
        J.comap (finiteCurveHom F w) := by
      rw [← hgen]
      apply Ideal.span_le.mpr
      intro Q hQ
      exact Ideal.mem_span_singleton.mpr (h ⟨Q,hQ⟩)
    exact Ideal.mem_span_singleton.mp (hle hP)

/-- All target-ideal pullbacks vanish to order at least m exactly when
the finitely bounded equations have no nonzero evaluation in weights <m. -/
theorem all_ideal_pullbacks_dvd_iff_weight_components [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (S : Set (MvPolynomial (Fin n) K)) (N m : ℕ)
    (hgen : Ideal.span (boundedIdeal (finiteTarget (d := d) S) N :
      Set (MvPolynomial (DegreeIndex n d) K)) = vanishingIdeal K (finiteTarget (d := d) S)) :
    (∀ P ∈ vanishingIdeal K (finiteTarget (d := d) S),
      Polynomial.X ^ m ∣ finiteCurveTest F w P) ↔
    (∀ P : boundedIdeal (finiteTarget (d := d) S) N, ∀ k : ℕ, k < m →
      eval (coefficientVector F) (weightPart P.val (coefficientWeights w) (k : ℤ)) = 0) := by
  rw [all_ideal_pullbacks_dvd_iff_bounded F w S N m hgen]
  simp_rw [Polynomial.X_pow_dvd_iff,coeff_finiteCurveTest F hF w hW]

end HessianTheorem11.UnconditionalOrbitIdeal
