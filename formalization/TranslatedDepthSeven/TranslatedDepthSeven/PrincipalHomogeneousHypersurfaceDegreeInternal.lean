import TranslatedDepthSeven.HilbertColonExactSequenceInternal
import TranslatedDepthSeven.PolynomialHilbertDifferenceInternal
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceCertificatesFieldInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal
import TranslatedDepthSeven.ProjectiveConeHilbertShift

/-!
# The exact degree of a principal homogeneous hypersurface

The polynomial-ring Hilbert function is a binomial coefficient. The
checked colon exact sequence therefore identifies the hypersurface
Hilbert polynomial with its degree-shifted difference. In particular the
degree of a prime principal hypersurface is the degree of its equation,
not merely bounded by it. No geometric Bezout statement is used.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem finrank_quotientHomogeneousComponent_bot_fin
    (K : Type*) [Field K] (N n : ℕ) :
    Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) ⊥ n) =
      (N + n).choose n := by
  apply Nat.le_antisymm
  · have h := Submodule.finrank_map_le
      (Ideal.Quotient.mkₐ K (⊥ : Ideal (MvPolynomial (Fin (N + 1)) K))).toLinearMap
      (homogeneousSubmodule (Fin (N + 1)) K n)
    simpa only [finrank_mvPolynomial_homogeneousSubmodule_fin,
      show N + 1 + n - 1 = N + n by omega] using h
  · have h := normalizationData_homogeneousHilbert_lower
      (⊥ : Ideal (MvPolynomial (Fin (N + 1)) K))
      (homogeneousLinearNormalizationDataBot (N + 1)) n
    change (N + 1 + n - 1).choose n ≤ _ at h
    simpa only [show N + 1 + n - 1 = N + n by omega] using h

theorem hasProjectiveDimensionDegree_bot_over_field
    (K : Type*) [Field K] [CharZero K] (N : ℕ) :
    HasProjectiveDimensionDegree (⊥ : Ideal (MvPolynomial (Fin (N + 1)) K)) N 1 := by
  refine ⟨?_, by omega, Polynomial.preHilbertPoly ℚ N 0,
    Polynomial.natDegree_preHilbertPoly _ _ _, ?_, 0, ?_⟩
  · exact (ringKrullDim_eq_of_ringEquiv
      (RingEquiv.quotientBot (MvPolynomial (Fin (N + 1)) K))).trans
        (ringKrullDim_mvPolynomial_fin_eq_of_field K (N + 1))
  · simp only [Polynomial.leadingCoeff_preHilbertPoly, Nat.cast_one, one_div]
  · intro n _
    change (Module.finrank K
      (quotientHomogeneousComponent K (Fin (N + 1)) ⊥ n) : ℚ) = _
    rw [finrank_quotientHomogeneousComponent_bot_fin,
      Polynomial.preHilbertPoly_eq_choose_sub_add ℚ N (k := 0) (n := n) (by omega)]
    simp only [Nat.sub_zero]
    congr 1
    rw [Nat.add_comm N n]
    exact Nat.choose_symm_add

/-- Exact eventual Hilbert polynomial, before any dimension or primeness
assertion about the hypersurface is made. -/
theorem principal_homogeneous_hilbertPolynomial
    {K : Type*} [Field K] {N d : ℕ}
    (G : MvPolynomial (Fin (N + 1)) K)
    (hG : G.IsHomogeneous d) (hGne : G ≠ 0) :
    ∀ n ≥ d,
      (Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1))
        (Ideal.span ({G} : Set _)) n) : ℚ) =
      (Polynomial.preHilbertPoly ℚ N 0 -
        Polynomial.taylor (-(d : ℚ)) (Polynomial.preHilbertPoly ℚ N 0)).eval (n : ℚ) := by
  have hcolon : (⊥ : Ideal (MvPolynomial (Fin (N + 1)) K)).colon
      (Ideal.span ({G} : Set _)) = ⊥ := by
    ext f
    rw [Ideal.mem_colon_singleton, Ideal.mem_bot, Ideal.mem_bot]
    exact mul_eq_zero.trans (or_iff_left hGne)
  intro n hn
  have hrec := finrank_homogeneous_section_add_colon_eq
    (⊥ : Ideal (MvPolynomial (Fin (N + 1)) K))
    (Ideal.IsHomogeneous.bot _) G hG (n - d)
  rw [hcolon, bot_sup_eq, Nat.sub_add_cancel hn] at hrec
  have hrecQ := congrArg (fun a : ℕ ↦ (a : ℚ)) hrec
  simp only [Nat.cast_add] at hrecQ
  have heval (m : ℕ) :
      (Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1)) ⊥ m) : ℚ) =
        (Polynomial.preHilbertPoly ℚ N 0).eval (m : ℚ) := by
    rw [finrank_quotientHomogeneousComponent_bot_fin,
      Polynomial.preHilbertPoly_eq_choose_sub_add ℚ N (k := 0) (n := m) (by omega)]
    simp only [Nat.sub_zero]
    congr 1
    rw [Nat.add_comm N m]
    exact Nat.choose_symm_add
  rw [heval, heval] at hrecQ
  rw [Polynomial.eval_sub, Polynomial.taylor_eval]
  have hcast : ((n - d : ℕ) : ℚ) = (n : ℚ) + -(d : ℚ) := by
    rw [Nat.cast_sub hn, sub_eq_add_neg]
  rw [hcast] at hrecQ
  linarith

/-- A prime hypersurface in `r+2` homogeneous variables has projective
dimension `r` and degree exactly the degree of its nonzero equation. -/
theorem hasProjectiveDimensionDegree_principal_homogeneous
    {K : Type*} [Field K] [CharZero K] {r d : ℕ}
    (G : MvPolynomial (Fin (r + 1 + 1)) K)
    (hG : G.IsHomogeneous d) (hGne : G ≠ 0) (hd : 0 < d)
    (hprime : (Ideal.span ({G} : Set _)).IsPrime) :
    HasProjectiveDimensionDegree (Ideal.span ({G} : Set _)) r d := by
  classical
  let J : Ideal (MvPolynomial (Fin (r + 1 + 1)) K) := Ideal.span ({G} : Set _)
  letI : J.IsPrime := hprime
  obtain ⟨degree, hcert, _⟩ :=
    properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
      (projectiveHilbertDegreeCertification_internal K)
      (⊥ : Ideal (MvPolynomial (Fin (r + 1 + 1)) K)) G
      Ideal.bot_prime (Ideal.IsHomogeneous.bot _)
      (hasProjectiveDimensionDegree_bot_over_field K (r + 1)) hG hGne
  have hJmem : J ∈ finiteMinimalPrimes
      ((⊥ : Ideal (MvPolynomial (Fin (r + 1 + 1)) K)) ⊔ J) := by
    simp only [bot_sup_eq, mem_finiteMinimalPrimes_iff,
      Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
  have hdim := (hcert J hJmem).1
  obtain ⟨hPdegree, hPlc⟩ := polynomial_backwardDifference_hilbert_data
    (Polynomial.preHilbertPoly ℚ (r + 1) 0) r 1 d (by omega) hd
    (Polynomial.natDegree_preHilbertPoly _ _ _)
    (by simp only [Polynomial.leadingCoeff_preHilbertPoly, Nat.cast_one, one_div])
  refine ⟨hdim, hd, _, hPdegree, ?_, d, ?_⟩
  · simpa only [Nat.one_mul] using hPlc
  · exact principal_homogeneous_hilbertPolynomial G hG hGne

/-- Bijective renaming preserves the entire published Hilbert certificate,
including the literal quotient dimension and every eventual Hilbert piece. -/
theorem hasProjectiveDimensionDegree_map_renameEquiv_internal
    {K : Type*} [Field K] {N r d : ℕ}
    (e : Fin (N + 1) ≃ Fin (N + 1))
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (h : HasProjectiveDimensionDegree I r d) :
    HasProjectiveDimensionDegree (I.map (renameEquiv K e)) r d := by
  obtain ⟨hdim, hd, P, hPdeg, hPlc, n₀, hP⟩ := h
  refine ⟨?_, hd, P, hPdeg, hPlc, n₀, ?_⟩
  · rw [← ringKrullDim_eq_of_ringEquiv (renameQuotientAlgEquiv K e I).toRingEquiv]
    exact hdim
  · intro n hn
    change (Module.finrank K (quotientHomogeneousComponent K (Fin (N + 1))
      (I.map (renameEquiv K e)) n) : ℚ) = _
    rw [← finrank_quotientHomogeneousComponent_map_renameEquiv K e I n]
    exact hP n hn

end
end TranslatedDepthSeven
