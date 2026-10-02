import HessianTheorem11.ReducedHensel
import HessianTheorem11.TextbookFormalGeometry

/-!
The formal implicit-function package is a theorem. The construction substitutes
all prescribed series into a genuine univariate polynomial, proves its simple
root by the derivative substitution identity, and applies Newton lifting in the
proved complete formal power-series ring. No characteristic or algebraic-closure
assumption is needed.
-/

noncomputable section
namespace HessianTheorem11.ReducedFormalImplicit
open MvPolynomial

variable {K σ : Type} [Field K] [DecidableEq σ]

/-- Keep the distinguished variable polynomial and substitute series in all
other variables. -/
def inOneVariable (P : MvPolynomial σ K) (j : σ) (u : σ → PowerSeries K) :
    Polynomial (PowerSeries K) :=
  eval₂ (Polynomial.C.comp PowerSeries.C)
    (Function.update (fun i => Polynomial.C (u i)) j Polynomial.X) P

lemma eval_inOneVariable (P : MvPolynomial σ K) (j : σ)
    (u : σ → PowerSeries K) (z : PowerSeries K) :
    (inOneVariable P j u).eval z =
      eval₂ PowerSeries.C (Function.update u j z) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [inOneVariable]
  | add P Q hP hQ => simp [inOneVariable, eval₂_add] at hP hQ ⊢; rw [hP,hQ]
  | mul_X P i hP =>
    by_cases hi : i = j
    · subst i
      simpa [inOneVariable, eval₂_mul] using congrArg (fun a => a*z) hP
    · simpa [inOneVariable, eval₂_mul, Function.update_of_ne hi] using
        congrArg (fun a => a*u i) hP

lemma derivative_inOneVariable (P : MvPolynomial σ K) (j : σ)
    (u : σ → PowerSeries K) :
    (inOneVariable P j u).derivative = inOneVariable (pderiv j P) j u := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [inOneVariable]
  | add P Q hP hQ =>
    simp only [inOneVariable, eval₂_add, map_add] at hP hQ ⊢
    rw [hP, hQ]
  | mul_X P i hP =>
    dsimp only [inOneVariable] at hP
    by_cases hi : i = j
    · subst i
      simp [inOneVariable, eval₂_mul, hP, mul_comm]
    · simp [inOneVariable, eval₂_mul, Function.update_of_ne hi,
        pderiv_X_of_ne hi, hP, mul_comm]

omit [DecidableEq σ] in
lemma constantCoeff_eval₂ (P : MvPolynomial σ K) (u : σ → PowerSeries K) :
    PowerSeries.constantCoeff (eval₂ PowerSeries.C u P) =
      eval (fun i => PowerSeries.constantCoeff (u i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [eval₂_add, hP, hQ]
  | mul_X P i hP => simp [eval₂_mul, hP]

/-- The entire formerly assumed formal implicit-function interface, proved over
an arbitrary field. -/
theorem formalImplicitFunctionInput (K : Type) [Field K] :
    HessianTheorem11.FormalImplicitFunctionInput K := by
  constructor
  intro σ _ _ P j u hu hP hdP
  letI := powerSeries_isAdicComplete K
  let f := inOneVariable P j u
  have hupdate : Function.update u j 0 = u := by
    exact Function.update_eq_self_iff.mpr hu.symm
  have hroot : f.eval 0 ∈ seriesIdeal K := by
    rw [seriesIdeal, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    change PowerSeries.constantCoeff ((inOneVariable P j u).eval 0) = 0
    rw [eval_inOneVariable, hupdate, constantCoeff_eval₂]
    exact hP
  have hderiv : IsUnit (f.derivative.eval 0) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    change PowerSeries.constantCoeff ((inOneVariable P j u).derivative.eval 0) ≠ 0
    rw [derivative_inOneVariable, eval_inOneVariable, hupdate, constantCoeff_eval₂]
    exact hdP
  obtain ⟨z, hz, hz0⟩ := exists_root_of_isAdicComplete (seriesIdeal K) f 0 hroot
    (hderiv.map (Ideal.Quotient.mk (seriesIdeal K)))
  refine ⟨z, ?_, ?_⟩
  · simpa only [sub_zero, seriesIdeal, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff] using hz0
  · exact (eval_inOneVariable P j u z).symm.trans hz

end HessianTheorem11.ReducedFormalImplicit
