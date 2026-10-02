import TranslatedDepthSeven.DepthSevenNormalizedJacobianPartition
import TranslatedDepthSeven.DepthSevenJacobianExceptionalLocus

/-!
# Integral and rational presentations of the Jacobian rank locus

The normalized partition uses the literal integral equation family, whereas
the component geometry is performed after extension of coefficients to
`\mathbb Q`.  This file proves that these two descriptions give exactly the
same rank-at-most-six condition.  No ordering of a finite equation family is
used: the proof identifies the spans of the actual gradient rows.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- Extending the displayed integral equations to `\mathbb Q` does not
change the span of their evaluated Jacobian rows. -/
theorem span_rationalizedEquationJacobianRows_eq_integralRows
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℤ))
    (x : IntVector N) :
    Submodule.span ℚ
        (Set.range (finiteEquationJacobianRowAt
          (rationalizedEquationFinset equations)
          (fun i ↦ (x i : ℚ)))) =
      Submodule.span ℚ
        (Set.range (fun i : Fin equations.card ↦
          (((integralJacobianMatrix
            (indexedFinsetFamily equations) x).map
              (Int.castRingHom ℚ)).row i))) := by
  apply congrArg (Submodule.span ℚ)
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨g, hg, hq⟩ := Finset.mem_image.mp q.2
    obtain ⟨i, hi⟩ := Set.ext_iff.mp
      (range_indexedFinsetFamily equations) g |>.mpr hg
    refine ⟨i, ?_⟩
    funext j
    change ((MvPolynomial.eval x
        (MvPolynomial.pderiv j (indexedFinsetFamily equations i)) : ℤ) : ℚ) =
      MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.pderiv j q.1)
    rw [← hq, ← hi, MvPolynomial.pderiv_map]
    exact (eval_map_intCast
      (MvPolynomial.pderiv j (indexedFinsetFamily equations i)) x).symm
  · rintro ⟨i, rfl⟩
    have hi : indexedFinsetFamily equations i ∈ equations := by
      exact Set.ext_iff.mp (range_indexedFinsetFamily equations)
        (indexedFinsetFamily equations i) |>.mp ⟨i, rfl⟩
    let q : {f // f ∈ rationalizedEquationFinset equations} :=
      ⟨MvPolynomial.map (Int.castRingHom ℚ)
          (indexedFinsetFamily equations i),
        Finset.mem_image.mpr ⟨indexedFinsetFamily equations i, hi, rfl⟩⟩
    refine ⟨q, ?_⟩
    funext j
    change MvPolynomial.eval (fun i ↦ (x i : ℚ))
        (MvPolynomial.pderiv j q.1) =
      ((MvPolynomial.eval x
        (MvPolynomial.pderiv j (indexedFinsetFamily equations i)) : ℤ) : ℚ)
    rw [show q.1 = MvPolynomial.map (Int.castRingHom ℚ)
        (indexedFinsetFamily equations i) by rfl,
      MvPolynomial.pderiv_map]
    exact eval_map_intCast
      (MvPolynomial.pderiv j (indexedFinsetFamily equations i)) x

/-- The matrix rank used by the integral normalized partition is the
dimension of the intrinsic rational gradient span. -/
theorem finrank_rationalizedEquationJacobianRows_eq_integralRank
    {N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℤ))
    (x : IntVector N) :
    Module.finrank ℚ
        (Submodule.span ℚ
          (Set.range (finiteEquationJacobianRowAt
            (rationalizedEquationFinset equations)
            (fun i ↦ (x i : ℚ))))) =
      ((integralJacobianMatrix (indexedFinsetFamily equations) x).map
        (Int.castRingHom ℚ)).rank := by
  rw [span_rationalizedEquationJacobianRows_eq_integralRows]
  exact (Matrix.rank_eq_finrank_span_row _).symm

/-- Exact comparison of the two rank-at-most-six predicates used in the
arithmetic and geometric parts of the formalization. -/
theorem rationalized_rankAtMostSix_iff_not_integralRegular
    (equations : Finset (MvPolynomial (Fin 13) ℤ))
    (x : IntVector 13) :
    IsDepthSevenJacobianRankAtMostSix
        (rationalizedEquationFinset equations) (fun i ↦ (x i : ℚ)) ↔
      ¬ IsDepthSevenJacobianRegularAt equations x := by
  rw [isDepthSevenJacobianRankAtMostSix_iff_finrank_le,
    finrank_rationalizedEquationJacobianRows_eq_integralRank]
  unfold IsDepthSevenJacobianRegularAt
  omega

end

end TranslatedDepthSeven
