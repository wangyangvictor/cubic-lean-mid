import HessianTheorem11.UnconditionalOrbitRepresentation
import HessianTheorem11.UnconditionalOrbitPolynomialWeights

/-! Actual weight components of the bounded invariant target ideal, and
their literal scalar behavior along the polynomial orbit curve. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction ReducedRelative ReducedWeightCurve
open UnconditionalOrbitWeights
variable {K : Type*} [Field K] {n d : ℕ}

def coefficientWeights (w : Fin n → ℤ) : DegreeIndex n d → ℤ :=
  fun e => monomialWeight w e.val

theorem finiteCoefficientMatrix_diagonal (w : Fin n → ℤ) (t : K) (ht : t ≠ 0) :
    finiteCoefficientMatrix (d := d) (diagonalWeight w t) =
      Matrix.diagonal (fun e : DegreeIndex n d => t ^ coefficientWeights w e) := by
  classical
  ext e m
  change coeff e.val (restrict (diagonalWeight w t) (monomial m.val 1)) = _
  rw [restrict_diagonal_monomial w t ht,one_mul]
  by_cases hem : e = m
  · subst m
    simp [coefficientWeights]
  · have hm : m.val ≠ e.val := fun h => hem (Subtype.ext h.symm)
    simp [coeff_monomial,hm,Matrix.diagonal_apply,hem]

/-- Projecting a bounded target equation onto any actual weight preserves
both membership in its ideal and the same degree cutoff. -/
theorem target_weightPart_mem [Infinite K]
    (S : Set (MvPolynomial (Fin n) K)) (hS : slInvariant S)
    (hhom : ∀ G ∈ S, G.IsHomogeneous d) (N : ℕ)
    (w : Fin n → ℤ) (hw : ∑ i, w i=0)
    (P : boundedIdeal (finiteTarget (d := d) S) N) (a : ℤ) :
    weightPart P.val (coefficientWeights w) a ∈ boundedIdeal (finiteTarget (d := d) S) N := by
  apply weightPart_mem
  intro t ht
  rw [← finiteCoefficientMatrix_diagonal w t ht]
  exact restrict_mem_boundedIdeal (finiteCoefficientMatrix (diagonalWeight w t))
    (finiteTarget S) N (finiteTarget_invariant S hS hhom (diagonalWeight w t)
      (diagonalWeight_det w hw t ht)) P.property

theorem diagonalScale_weightPart {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ K) (w : σ → ℤ) (a : ℤ) (t : K) :
    diagonalScale (weightPart P w a) w t = t ^ a • weightPart P w a := by
  ext e
  simp only [coeff_diagonalScale,coeff_weightPart,coeff_smul,smul_eq_mul]
  by_cases he : exponentWeight w e = a
  · simp [he,mul_comm]
  · simp [he]

theorem eval_weightPart_curve (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (a : ℤ) (t : K) (ht : t ≠ 0) :
    eval (coefficientVector (d := d) (curve F w t)) (weightPart P (coefficientWeights w) a) =
      t ^ a * eval (coefficientVector F) (weightPart P (coefficientWeights w) a) := by
  rw [curve_eq_restrict F w hW t ht,coefficientVector_restrict _ F hF,
    finiteCoefficientMatrix_diagonal w t ht,← eval_restrict,
    ← diagonalScale_eq_restrict _ _ t ht,diagonalScale_weightPart]
  change (aeval (coefficientVector F)).toLinearMap
    (t ^ a • weightPart P (coefficientWeights w) a) = _
  rw [map_smul]
  rfl

def finiteCurveTest (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (P : MvPolynomial (DegreeIndex n d) K) : Polynomial K :=
  curveTest F w (rename Subtype.val P)

theorem eval_finiteCurveTest (F : MvPolynomial (Fin n) K) (w : Fin n → ℤ)
    (P : MvPolynomial (DegreeIndex n d) K) (t : K) :
    (finiteCurveTest F w P).eval t = eval (coefficientVector (d := d) (curve F w t)) P := by
  rw [finiteCurveTest,eval_curveTest,eval_rename]
  rfl

/-- For a nonnegative actual orbit curve, a nonnegative weight component
pulls back to a single monomial with its actual evaluation as coefficient. -/
theorem finiteCurveTest_weightPart_of_nonnegative [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (a : ℤ) (ha : 0 ≤ a) :
    finiteCurveTest F w (weightPart P (coefficientWeights w) a) =
      Polynomial.monomial a.toNat
        (eval (coefficientVector F) (weightPart P (coefficientWeights w) a)) := by
  apply sub_eq_zero.mp
  apply polynomial_zero_of_nonzero_values
  intro t ht
  rw [Polynomial.eval_sub,eval_finiteCurveTest,eval_weightPart_curve F hF w hW P a t ht,
    Polynomial.eval_monomial,← zpow_natCast,Int.toNat_of_nonneg ha]
  ring

/-- A negative equation weight cannot contribute to an existing polynomial
orbit curve. Its evaluation and its whole pulled-back polynomial vanish. -/
theorem finiteCurveTest_weightPart_of_negative [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (w : Fin n → ℤ) (hW : HasNonnegativeWeights F w)
    (P : MvPolynomial (DegreeIndex n d) K) (a : ℤ) (ha : a < 0) :
    eval (coefficientVector F) (weightPart P (coefficientWeights w) a) = 0 ∧
      finiteCurveTest F w (weightPart P (coefficientWeights w) a) = 0 := by
  let Q := finiteCurveTest F w (weightPart P (coefficientWeights w) a)
  let c := eval (coefficientVector F) (weightPart P (coefficientWeights w) a)
  have hval (t : K) (ht : t ≠ 0) : Q.eval t = t ^ a * c :=
    (eval_finiteCurveTest F w _ t).trans (eval_weightPart_curve F hF w hW P a t ht)
  have hz : Q * Polynomial.X ^ (-a).toNat - Polynomial.C c = 0 := by
    apply polynomial_zero_of_nonzero_values
    intro t ht
    rw [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
      Polynomial.eval_C,hval t ht,← zpow_natCast,Int.toNat_of_nonneg (by omega : 0 ≤ -a)]
    have hpow : t ^ a * t ^ (-a) = 1 := by rw [← zpow_add₀ ht,add_neg_cancel,zpow_zero]
    calc
      t ^ a * c * t ^ (-a) - c = (t ^ a * t ^ (-a)) * c - c := by ring
      _ = 0 := by rw [hpow,one_mul,sub_self]
  have hc : c = 0 := by
    have h := congrArg (Polynomial.eval (0 : K)) hz
    have hn : (-a).toNat ≠ 0 := by omega
    simpa [hn] using h
  refine ⟨hc,?_⟩
  apply polynomial_zero_of_nonzero_values
  intro t ht
  rw [hval t ht,hc,mul_zero]

end HessianTheorem11.UnconditionalOrbitIdeal
