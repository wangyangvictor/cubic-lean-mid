import TranslatedDepthSeven.StandardSmoothHigherJets
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomial approximations in one smooth local coordinate

The checked one-variable jet equivalences imply existence and uniqueness
of polynomial approximations to every finite order.  These are literal
congruences in powers of the rational-point ideal, with no formal
completion theorem assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

def oneVariablePolynomialAlgEquiv (K : Type*) [Field K] :
    MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.renameEquiv K (Equiv.ofUnique (Fin 1) PUnit.{1})).trans
    (MvPolynomial.pUnitAlgEquiv K)

theorem oneVariablePolynomialAlgEquiv_eval_zero
    (P : MvPolynomial (Fin 1) K) :
    (oneVariablePolynomialAlgEquiv K P).eval 0 = MvPolynomial.constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [oneVariablePolynomialAlgEquiv]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
    simp [oneVariablePolynomialAlgEquiv, map_mul,
      MvPolynomial.renameEquiv_apply, MvPolynomial.pUnitAlgEquiv_apply]

theorem oneVariablePolynomialAlgEquiv_map_originIdeal :
    (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) K →+* K)).map
      (oneVariablePolynomialAlgEquiv K).toRingHom =
        Ideal.span {(Polynomial.X : Polynomial K)} := by
  rw [← show RingHom.ker (Polynomial.evalRingHom (0 : K)) =
      Ideal.span {(Polynomial.X : Polynomial K)} by
    simp [Polynomial.ker_evalRingHom]]
  ext P
  rw [Ideal.mem_map_iff_of_surjective (oneVariablePolynomialAlgEquiv K).toRingHom
    (oneVariablePolynomialAlgEquiv K).surjective]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (oneVariablePolynomialAlgEquiv_eval_zero Q).trans hQ
  · intro hP
    refine ⟨(oneVariablePolynomialAlgEquiv K).symm P, ?_, by simp⟩
    change MvPolynomial.constantCoeff _ = 0
    rw [← oneVariablePolynomialAlgEquiv_eval_zero]
    simpa using hP

def smoothCurvePolynomialCoordinate (f : A →ₐ[K] K)
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] :
    Polynomial K →ₐ[K] A :=
  (smoothCoordinateMap f 1).comp (oneVariablePolynomialAlgEquiv K).symm.toAlgHom

theorem exists_smoothCurvePolynomialApproximation
    (f : A →ₐ[K] K) [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    (x : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Polynomial K,
      smoothCurvePolynomialCoordinate f P - x ∈ RingHom.ker f.toRingHom ^ (k + 1) := by
  obtain ⟨q, hq⟩ := (smoothCoordinateJetMap_bijective f 1 k hk).2
    (Ideal.Quotient.mk _ x)
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨oneVariablePolynomialAlgEquiv K Q, ?_⟩
  apply Ideal.Quotient.eq.mp
  change Ideal.Quotient.mk _ ((smoothCoordinateMap f 1)
    ((oneVariablePolynomialAlgEquiv K).symm (oneVariablePolynomialAlgEquiv K Q))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact hq

theorem smoothCurvePolynomialCoordinate_coeff_zero_of_mem
    (f : A →ₐ[K] K) [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    (P : Polynomial K) (k : ℕ) (hk : 1 ≤ k)
    (hP : smoothCurvePolynomialCoordinate f P ∈ RingHom.ker f.toRingHom ^ (k + 1)) :
    ∀ i ≤ k, P.coeff i = 0 := by
  let Q := (oneVariablePolynomialAlgEquiv K).symm P
  have hQ : Q ∈ RingHom.ker
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) K →+* K) ^ (k + 1) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (smoothCoordinateJetMap_bijective f 1 k hk).1
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hP
  have hmap := Ideal.mem_map_of_mem (oneVariablePolynomialAlgEquiv K).toRingHom hQ
  rw [Ideal.map_pow, oneVariablePolynomialAlgEquiv_map_originIdeal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmap
  have hdiv : Polynomial.X ^ (k + 1) ∣ P := by
    change Polynomial.X ^ (k + 1) ∣
      oneVariablePolynomialAlgEquiv K ((oneVariablePolynomialAlgEquiv K).symm P) at hmap
    simpa using hmap
  exact fun i hi ↦ Polynomial.X_pow_dvd_iff.mp hdiv i (by omega)

end

end TranslatedDepthSeven
