import TranslatedDepthSeven.IntegralDistinguishedRowPullbackInternal
import TranslatedDepthSeven.HomogeneousNormalizationRankDegreeEqualityInternal

/-!
# Degree-uniform integral normalization retaining the first coordinate

Each step uses an integral shear with coefficients between zero and the
original degree bound. Pullback increases a row's sum of absolute values
by at most that bound plus one. Thus the complete normalization is given
by integral rows of norm at most `(D+1)^n`, fixed before the source ideal
and even before the characteristic-zero coefficient field.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Matrix Published
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem homogeneousPrime_fin_one_eq_bot_of_X_zero_not_mem
    {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 1) K)) (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin 1) K))
    (hX : X 0 ∉ I) : I = ⊥ := by
  let e := _root_.finSuccEquiv 0
  let E := renameEquiv K e
  let J := I.map E
  letI : I.IsPrime := hprime
  have hJprime : J.IsPrime := by dsimp only [J, E]; infer_instance
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Option (Fin 0)) K) :=
    map_renameEquiv_isHomogeneous e I hhom
  have hJX : X none ∉ J := by
    intro hx
    apply hX
    have hh : E (X 0) ∈ J := by simpa [E, e] using hx
    exact (Ideal.apply_mem_of_equiv_iff (f := E.toRingEquiv)).1 hh
  have hJbot := homogeneousPrime_option_fin_zero_eq_bot J hJprime hJhom hJX
  exact (Ideal.map_eq_bot_iff_of_injective E.injective).mp hJbot

theorem indexedMatrixRowLinearPolynomial_int_identity
    {K : Type*} [Field K] {n : ℕ} (i : Fin n) :
    indexedMatrixRowLinearPolynomial
      ((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom K)) i = X i := by
  classical
  simp [indexedMatrixRowLinearPolynomial, Matrix.map_apply, Matrix.one_apply]

theorem exists_boundedIntegralNormalization_of_eq_bot
    {K : Type*} [Field K] [CharZero K] {n r d D : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) (hbot : I = ⊥) :
    ∃ A : Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ,
      (∀ i, ∑ j, (A i j).natAbs ≤ (D + 1) ^ n) ∧
      (∀ j, A 0 j = if j = 0 then 1 else 0) ∧
      let h := (Ideal.Quotient.mkₐ K I).comp
        (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))
      Function.Injective h ∧ h.Finite := by
  subst I
  have hcount := (homogeneousLinearNormalization_genericRank_eq_projectiveDegree
    (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)) hprime hhom
    (homogeneousLinearNormalizationDataBot (n + 1)) hdegree).1
  change n + 1 = r + 1 at hcount
  have hr : r = n := by omega
  subst r
  refine ⟨1, ?_, ?_, ?_⟩
  · intro i
    have hsum : ∑ j, ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) i j).natAbs = 1 := by
      simp only [Matrix.one_apply, apply_ite Int.natAbs, Int.natAbs_one, Int.natAbs_zero]
      simp
    rw [hsum]
    exact Nat.one_le_pow _ _ (by omega)
  · intro j
    simp [Matrix.one_apply, eq_comm]
  · have hforms := funext (indexedMatrixRowLinearPolynomial_int_identity (K := K) (n := n + 1))
    dsimp only
    rw [hforms, MvPolynomial.aeval_X_left]
    simp only [AlgHom.comp_id]
    exact ⟨(Ideal.Quotient.mk_bijective_iff_eq_bot ⊥).mpr rfl |>.injective,
      AlgHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective K ⊥)⟩

/-- A normalization by actual integral rows, with the source-independent
row bound `(D+1)^n` and the first row exactly the first coordinate. -/
theorem exists_boundedIntegralDistinguishedNormalization
    {K : Type*} [Field K] [CharZero K] (n : ℕ) {r d D : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (hX : X 0 ∉ I) (hdegree : HasProjectiveDimensionDegree I r d) (hdD : d ≤ D) :
    ∃ A : Matrix (Fin (r + 1)) (Fin (n + 1)) ℤ,
      (∀ i, ∑ j, (A i j).natAbs ≤ (D + 1) ^ n) ∧
      (∀ j, A 0 j = if j = 0 then 1 else 0) ∧
      let h := (Ideal.Quotient.mkₐ K I).comp
        (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))
      Function.Injective h ∧ h.Finite := by
  induction n generalizing r d with
  | zero =>
    exact exists_boundedIntegralNormalization_of_eq_bot I hprime hhom hdegree
      (homogeneousPrime_fin_one_eq_bot_of_X_zero_not_mem I hprime hhom hX)
  | succ n ih =>
    by_cases hbot : I = ⊥
    · exact exists_boundedIntegralNormalization_of_eq_bot I hprime hhom hdegree hbot
    obtain ⟨z, hz, hfinite, hPprime, hPhom, hPX, e, hed, hPdegree⟩ :=
      exists_boundedNat_distinguishedFiniteLinearImage I hprime hhom hbot hX hdegree
    let l := distinguishedFinEliminationForms (K := K) z
    let h := (Ideal.Quotient.mkₐ K I).comp (aeval l)
    let P := RingHom.ker h.toRingHom
    obtain ⟨A, hAnorm, hAfirst, hAinjective, hAfinite⟩ :=
      ih P hPprime hPhom hPX hPdegree (hed.trans hdD)
    let B := distinguishedIntegerRowPullback A z
    have hBforms : indexedMatrixRowLinearPolynomial (B.map (Int.castRingHom K)) =
        fun i ↦ aeval l (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K)) i) :=
      funext (indexedMatrixRowLinearPolynomial_distinguishedIntegerRowPullback A z)
    have hBhom : (Ideal.Quotient.mkₐ K I).comp
        (aeval (indexedMatrixRowLinearPolynomial (B.map (Int.castRingHom K)))) =
        (Ideal.kerLiftAlg h).comp ((Ideal.Quotient.mkₐ K P).comp
          (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))) := by
      rw [hBforms]
      exact (kerLift_comp_normalizationHom I l h rfl (r + 1)
        (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K)))).symm
    refine ⟨B, ?_, distinguishedIntegerRowPullback_firstRow A z hAfirst, ?_⟩
    · intro i
      calc
        _ ≤ (D + 1) * ∑ j, (A i j).natAbs :=
          distinguishedIntegerRowPullback_rowNorm_le A z (fun j ↦ (hz j).trans hdD) i
        _ ≤ (D + 1) * (D + 1) ^ n := Nat.mul_le_mul_left _ (hAnorm i)
        _ = (D + 1) ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
    · dsimp only
      rw [hBhom]
      exact ⟨(Ideal.kerLiftAlg_injective h).comp hAinjective,
        AlgHom.Finite.comp (kerLiftAlg_finite_of_finite h hfinite) hAfinite⟩

/-- The normalization datum attached to a verified integral matrix. The
number of parameters and the displayed polynomial forms are literal. -/
def homogeneousLinearNormalizationDataOfIntegralMatrix
    {K : Type*} [Field K] {s n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (A : Matrix (Fin s) (Fin n) ℤ)
    (hinjective : Function.Injective ((Ideal.Quotient.mkₐ K I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))))
    (hfinite : ((Ideal.Quotient.mkₐ K I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))))).Finite) :
    HomogeneousLinearNormalizationData I where
  parameterCount := s
  forms := indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom K))
  forms_isHomogeneous := indexedMatrixRowLinearPolynomial_isHomogeneous _
  injective := hinjective
  finite := hfinite

end
end TranslatedDepthSeven
