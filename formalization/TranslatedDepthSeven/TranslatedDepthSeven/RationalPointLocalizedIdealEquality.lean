import TranslatedDepthSeven.LocalizedIdealEquality
import TranslatedDepthSeven.RationalPointResidueField
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Retaining a denominator at a rational point

If two nested polynomial ideals agree in the local ring of a displayed
rational point, finite generation supplies one polynomial denominator which
does not vanish at that point and which clears the larger ideal into the
smaller one.  This is the exact form needed before the finitely many rational
coefficients are cleared to an integral model.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- Evaluation at a point of affine space has prime kernel. -/
instance mvPolynomialEval_ker_isPrime
    {K : Type*} {σ : Type*} [Field K] (z : σ → K) :
    (RingHom.ker (MvPolynomial.eval z)).IsPrime :=
  RingHom.ker_isPrime (MvPolynomial.eval z)

/-- Pointwise form of principal-open shrinking.  The output retains both the
nonzero evaluation and the elementwise clearing identity. -/
theorem exists_nonzeroEvaluation_mul_mem_and_map_away_eq_of_map_atPoint_eq
    {K : Type*} {σ : Type*} [Field K]
    (z : σ → K)
    (I J : Ideal (MvPolynomial σ K))
    (hIJ : I ≤ J) (hJfg : J.FG)
    (hatPoint :
      Ideal.map
          (algebraMap (MvPolynomial σ K)
            (Localization.AtPrime
              (RingHom.ker (MvPolynomial.eval z)))) I =
        Ideal.map
          (algebraMap (MvPolynomial σ K)
            (Localization.AtPrime
              (RingHom.ker (MvPolynomial.eval z)))) J) :
    ∃ u : MvPolynomial σ K,
      MvPolynomial.eval z u ≠ 0 ∧
      (∀ f ∈ J, u * f ∈ I) ∧
      Ideal.map
          (algebraMap (MvPolynomial σ K) (Localization.Away u)) I =
        Ideal.map
          (algebraMap (MvPolynomial σ K) (Localization.Away u)) J := by
  let P : Ideal (MvPolynomial σ K) :=
    RingHom.ker (MvPolynomial.eval z)
  letI : P.IsPrime := RingHom.ker_isPrime (MvPolynomial.eval z)
  obtain ⟨u, huP, hclear, haway⟩ :=
    exists_notMem_mul_mem_and_map_away_eq_of_map_atPrime_eq
      (I := I) (J := J) (P := P) hIJ hJfg (by
        simpa only [P] using hatPoint)
  refine ⟨u, ?_, hclear, haway⟩
  exact fun hu ↦ huP (RingHom.mem_ker.mpr hu)

end

end TranslatedDepthSeven
