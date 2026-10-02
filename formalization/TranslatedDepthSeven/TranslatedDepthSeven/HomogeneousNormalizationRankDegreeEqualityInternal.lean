import TranslatedDepthSeven.HomogeneousNormalizationDegreeBoundInternal
import TranslatedDepthSeven.GenericRankShiftedBinomial
import TranslatedDepthSeven.HilbertAffineChange
import TranslatedDepthSeven.HomogeneousComponentDegreeMassInternal

/-!
# Generic rank equals degree for homogeneous linear normalization

The finite homogeneous module is squeezed between free modules of its
generic rank, with fixed degree shifts. Passing to cumulative Hilbert
polynomials proves the reverse of the existing generic-rank degree bound.
No freeness of the original module or Cohen--Macaulay hypothesis is used.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem homogeneousLinearNormalization_genericRank_eq_projectiveDegree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (D : HomogeneousLinearNormalizationData I)
    (hprojective : HasProjectiveDimensionDegree I r d) :
    D.parameterCount = r + 1 ∧
      (let B := MvPolynomial (Fin D.parameterCount) K
       let A := MvPolynomial (Fin (N + 1)) K ⧸ I
       letI : Algebra B A := D.hom.toRingHom.toAlgebra
       Module.finrank (FractionRing B)
         (LocalizedModule (nonZeroDivisors B) A) = d) := by
  classical
  obtain ⟨hcount, hle⟩ :=
    homogeneousLinearNormalization_genericRank_le_projectiveDegree I hprime D hprojective
  refine ⟨hcount, Nat.le_antisymm hle ?_⟩
  letI : NeZero D.parameterCount := ⟨by omega⟩
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  let δ := Module.finrank (FractionRing B)
    (LocalizedModule (nonZeroDivisors B) A)
  have hδ : 0 < δ :=
    genericRank_pos_of_finite_injective_linearNormalizationFin
      K (Fin (N + 1)) I D.forms hprime D.hom_finite D.hom_injective
  obtain ⟨E, C, hbound⟩ := exists_genericRank_shifted_binomial_squeeze_fin
    K (Fin (N + 1)) I hhom hprime D.forms D.forms_isHomogeneous
    D.hom_finite D.hom_injective
  obtain ⟨_, _, hd, P, hPdeg, hPlc, k₀, hPeval⟩ :=
    hasAffineDimensionDegree_of_homogeneous_hasProjectiveDimensionDegree
      I hhom hprime r d hprojective
  let Q : Polynomial ℚ :=
    Polynomial.C (δ : ℚ) * Polynomial.preHilbertPoly ℚ (r + 1) 0
  have hδne : (δ : ℚ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hQdeg : Q.natDegree = r + 1 := by
    simp only [Q, Polynomial.natDegree_C_mul hδne,
      Polynomial.natDegree_preHilbertPoly]
  have hQlc : Q.leadingCoeff = (δ : ℚ) / (r + 1).factorial := by
    simp only [Q, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_preHilbertPoly, div_eq_mul_inv]
  have hresult := sum_degrees_le_of_shifted_hilbertPolynomial_comparison
    (fun _ : Unit ↦ P) Q (r + 1) δ C k₀ (fun _ : Unit ↦ d)
    hδ (fun _ ↦ hd) (fun _ ↦ hPdeg) (fun _ ↦ hPlc) hQdeg hQlc (by
      intro n hn
      simp only [Fintype.sum_unique]
      rw [← hPeval n hn]
      have hb := (hbound n).2
      change Module.finrank K (quotientTotalDegreeFiltration K (Fin (N + 1)) I n) ≤
        δ * (n + C + D.parameterCount).choose D.parameterCount at hb
      rw [hcount] at hb
      have hQeval : Q.eval ((n + C : ℕ) : ℚ) =
          ((δ * (n + C + (r + 1)).choose (r + 1) : ℕ) : ℚ) := by
        simp only [Q, Polynomial.eval_mul, Polynomial.eval_C]
        rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ (r + 1)
          (k := 0) (n := n + C) (by omega)]
        push_cast
        simp
      rw [hQeval]
      exact_mod_cast hb)
  simpa only [Fintype.sum_unique] using hresult

end
end TranslatedDepthSeven
