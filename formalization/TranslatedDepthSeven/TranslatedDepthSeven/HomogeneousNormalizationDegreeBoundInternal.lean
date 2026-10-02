import TranslatedDepthSeven.ProjectiveDegreeOneSurfaceLinearInternal

/-!
# Degree bounds the generic rank of linear Noether normalization

The independent homogeneous monomials constructed earlier give a lower
bound for the source Hilbert function. Comparing leading coefficients
proves that the generic rank of any finite linear normalization is at most
the projective degree. This works in every projective dimension, including
dimension zero, and makes no assumption of geometric integrality.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 300000

/-- An eventual shifted Hilbert-function lower bound yields the corresponding
inequality between multiplicity and projective degree. -/
theorem multiplicity_le_degree_of_shifted_projectiveHilbert_lower
    (P : Polynomial ℚ) (r d δ E k₀ : ℕ)
    (hd : 0 < d)
    (hPdegree : P.natDegree = r)
    (hPleading : P.leadingCoeff = (d : ℚ) / r.factorial)
    (hlower : ∀ n ≥ k₀,
      ((δ * (n + r).choose r : ℕ) : ℚ) ≤ P.eval ((n + E : ℕ) : ℚ)) :
    δ ≤ d := by
  let S : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (E : ℚ))
  let B : Polynomial ℚ := Polynomial.preHilbertPoly ℚ r 0
  have hlinearDegree :
      (Polynomial.X + Polynomial.C (E : ℚ)).natDegree = 1 :=
    Polynomial.natDegree_X_add_C (E : ℚ)
  have hSdegree : S.natDegree = r := by
    simp only [S, Polynomial.natDegree_comp, hPdegree, hlinearDegree, mul_one]
  have hBdegree : B.natDegree = r :=
    Polynomial.natDegree_preHilbertPoly ℚ r 0
  have hSlc : S.leadingCoeff = (d : ℚ) / r.factorial := by
    dsimp only [S]
    rw [Polynomial.leadingCoeff_comp (by rw [hlinearDegree]; omega),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one, hPleading]
  have hBlc : B.leadingCoeff = (r.factorial : ℚ)⁻¹ :=
    Polynomial.leadingCoeff_preHilbertPoly ℚ r 0
  have hfactorial : (r.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hSne : S ≠ 0 := by
    intro hzero
    have h := hSlc
    rw [hzero, Polynomial.leadingCoeff_zero] at h
    exact (div_ne_zero hdQ hfactorial) h.symm
  have hBne : B ≠ 0 := by
    intro hzero
    have h := hBlc
    rw [hzero, Polynomial.leadingCoeff_zero] at h
    exact (inv_ne_zero hfactorial) h.symm
  have hdegree : S.degree = B.degree := by
    rw [Polynomial.degree_eq_natDegree hSne,
      Polynomial.degree_eq_natDegree hBne, hSdegree, hBdegree]
  have hratio : S.leadingCoeff / B.leadingCoeff = (d : ℚ) := by
    rw [hSlc, hBlc]
    field_simp
  have hlimitQ : Filter.Tendsto
      (fun q : ℚ ↦ S.eval q / B.eval q) Filter.atTop (nhds (d : ℚ)) := by
    simpa only [hratio] using
      Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq S B hdegree
  have hlimitN : Filter.Tendsto
      (fun n : ℕ ↦ S.eval (n : ℚ) / B.eval (n : ℚ))
      Filter.atTop (nhds (d : ℚ)) :=
    hlimitQ.comp tendsto_natCast_atTop_atTop
  have heventual : ∀ᶠ n : ℕ in Filter.atTop,
      (δ : ℚ) ≤ S.eval (n : ℚ) / B.eval (n : ℚ) := by
    filter_upwards [Filter.eventually_ge_atTop k₀] with n hn
    have hB : B.eval (n : ℚ) = ((n + r).choose r : ℚ) := by
      dsimp only [B]
      simpa using
        (Polynomial.preHilbertPoly_eq_choose_sub_add ℚ r
          (k := 0) (n := n) (by omega))
    have hBpos : 0 < B.eval (n : ℚ) := by
      rw [hB]
      exact_mod_cast Nat.choose_pos (by omega : r ≤ n + r)
    have hS : S.eval (n : ℚ) = P.eval ((n + E : ℕ) : ℚ) := by
      simp [S]
    rw [le_div_iff₀ hBpos, hB, hS]
    norm_cast
    simpa [Nat.mul_comm] using hlower n hn
  exact_mod_cast ge_of_tendsto hlimitN heventual

/-- The generic module rank of a finite homogeneous linear normalization
is at most the degree recorded in the source Hilbert polynomial. -/
theorem homogeneousLinearNormalization_genericRank_le_projectiveDegree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hprime : I.IsPrime)
    (D : HomogeneousLinearNormalizationData I)
    (hprojective : HasProjectiveDimensionDegree I r d) :
    D.parameterCount = r + 1 ∧
      (let B := MvPolynomial (Fin D.parameterCount) K
       let A := MvPolynomial (Fin (N + 1)) K ⧸ I
       letI : Algebra B A := D.hom.toRingHom.toAlgebra
       Module.finrank (FractionRing B)
         (LocalizedModule (nonZeroDivisors B) A) ≤ d) := by
  have hdimension := D.ringKrullDim_eq_parameterPolynomial (N + 1) I hprime
  rw [ringKrullDim_mvPolynomial_fin_eq_of_field K D.parameterCount] at hdimension
  have hcount : D.parameterCount = r + 1 := by
    have hdim : (D.parameterCount : WithBot ℕ∞) = (r + 1 : ℕ) := by
      rw [← hdimension]
      simpa only [Nat.cast_add, Nat.cast_one] using hprojective.1
    exact_mod_cast hdim
  refine ⟨hcount, ?_⟩
  letI : I.IsPrime := hprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  obtain ⟨E, hlower⟩ := exists_genericRank_lower_homogeneous_normalizationData
    K (Fin (N + 1)) I D (by omega)
  obtain ⟨_hdim, hd, P, hPdegree, hPlc, k₀, hPeventual⟩ := hprojective
  apply multiplicity_le_degree_of_shifted_projectiveHilbert_lower P r d
    (Module.finrank (FractionRing B)
      (LocalizedModule (nonZeroDivisors B) A)) E k₀ hd hPdegree hPlc
  intro n hn
  have hvalue := hPeventual (n + E) (by omega)
  have hvalue' :
      (Module.finrank K
        (quotientHomogeneousComponent K (Fin (N + 1)) I (n + E)) : ℚ) =
          P.eval ((n + E : ℕ) : ℚ) := by
    simpa only [projectiveHilbertPiece, quotientHomogeneousComponent] using hvalue
  have hl := hlower n
  have hchoose : (D.parameterCount + n - 1).choose n = (n + r).choose r := by
    rw [hcount, show r + 1 + n - 1 = n + r by omega]
    simpa only [Nat.add_sub_cancel] using
      (Nat.choose_symm (by omega : r ≤ n + r))
  rw [hchoose] at hl
  rw [← hvalue']
  exact_mod_cast hl

end

end TranslatedDepthSeven
