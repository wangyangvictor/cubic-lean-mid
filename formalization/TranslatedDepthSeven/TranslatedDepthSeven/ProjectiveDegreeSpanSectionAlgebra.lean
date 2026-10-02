import TranslatedDepthSeven.ProjectiveCurveDegreeSpanInternal
import TranslatedDepthSeven.HilbertColonExactSequenceInternal
import TranslatedDepthSeven.PolynomialHilbertDifferenceInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Exact algebra for a prime hyperplane section

The section ideal is the literal sum `I + (L)`. Multiplication by a
linear form outside the prime ideal gives the exact Hilbert recurrence.
In particular, the degree is preserved and the degree-one Hilbert value
drops by exactly one. These statements do not construct a prime section
and do not replace the section ideal by its radical or saturation.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

theorem projectiveSection_colon_eq_of_prime
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsPrime) (L : MvPolynomial σ K) (hL : L ∉ I) :
    I.colon (Ideal.span ({L} : Set _)) = I := by
  ext p
  rw [Ideal.mem_colon_singleton]
  exact ⟨fun h ↦ (hI.mem_or_mem h).resolve_right hL,
    fun h ↦ I.mul_mem_right L h⟩

theorem projectiveSection_finrank_recurrence
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ K))
    (L : MvPolynomial σ K) (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (n : ℕ) :
    Module.finrank K (quotientHomogeneousComponent K σ
      (I ⊔ Ideal.span ({L} : Set _)) (n + 1)) +
      Module.finrank K (quotientHomogeneousComponent K σ I n) =
      Module.finrank K (quotientHomogeneousComponent K σ I (n + 1)) := by
  have h := finrank_homogeneous_section_add_colon_eq I hhom L hLhom n
  have hc : Submodule.colon I (Ideal.span ({L} : Set _)) = I :=
    projectiveSection_colon_eq_of_prime I hI L hL
  rw [hc] at h
  exact h

theorem projectiveSection_hilbertZero_eq_one
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime) :
    Module.finrank K (quotientHomogeneousComponent K σ I 0) = 1 := by
  letI : I.IsPrime := hI
  let v : quotientHomogeneousComponent K σ I 0 :=
    ⟨1, Submodule.mem_map.mpr ⟨1, isHomogeneous_one σ K, by simp⟩⟩
  apply finrank_eq_one v
  · intro h
    exact one_ne_zero (congrArg Subtype.val h)
  · intro w
    obtain ⟨p, hp, hwp⟩ := Submodule.mem_map.mp w.2
    have hpzero : p.totalDegree = 0 := by
      by_cases hz : p = 0
      · simp [hz]
      · exact hp.totalDegree hz
    have hpC : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hpzero
    refine ⟨p.coeff 0, ?_⟩
    apply Subtype.ext
    change (p.coeff 0) • (1 : MvPolynomial σ K ⧸ I) = w.1
    rw [← hwp]
    conv_rhs => rw [hpC]
    simp only [Algebra.smul_def, mul_one]
    exact ((Ideal.Quotient.mkₐ K I).commutes (p.coeff 0)).symm

theorem projectiveSection_hilbertOne_add_one
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ K))
    (L : MvPolynomial σ K) (hLhom : L.IsHomogeneous 1) (hL : L ∉ I) :
    Module.finrank K (quotientHomogeneousComponent K σ
      (I ⊔ Ideal.span ({L} : Set _)) 1) + 1 =
      Module.finrank K (quotientHomogeneousComponent K σ I 1) := by
  simpa only [Nat.zero_add, projectiveSection_hilbertZero_eq_one I hI] using
    projectiveSection_finrank_recurrence I hI hhom L hLhom hL 0

theorem projectiveSection_preserves_hilbertDegree
    {K : Type*} [Field K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveHilbertDimensionDegree I (r + 1) d)
    (L : MvPolynomial (Fin (N + 1)) K)
    (hLhom : L.IsHomogeneous 1) (hL : L ∉ I) :
    HasProjectiveHilbertDimensionDegree (I ⊔ Ideal.span ({L} : Set _)) r d := by
  obtain ⟨hd, P, hP, hPlc, n₀, hPn⟩ := hdegree
  obtain ⟨hQ, hQlc⟩ := polynomial_backwardDifference_hilbert_data
    P r d 1 hd (by omega) hP hPlc
  refine ⟨hd, P - Polynomial.taylor (-1) P, hQ, ?_, n₀ + 1, ?_⟩
  · simpa only [Nat.mul_one, Nat.cast_one] using hQlc
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : n₀ ≤ m := by omega
    have hm1 : n₀ ≤ m + 1 := by omega
    have hrec := projectiveSection_finrank_recurrence I hI hhom L hLhom hL m
    have hrecQ :
        (Module.finrank K (projectiveHilbertPiece K N
          (I ⊔ Ideal.span ({L} : Set _)) (m + 1)) : ℚ) +
        P.eval (m : ℚ) = P.eval ((m + 1 : ℕ) : ℚ) := by
      rw [← hPn m hm, ← hPn (m + 1) hm1]
      exact_mod_cast hrec
    rw [Polynomial.eval_sub, Polynomial.taylor_eval]
    have hshift : ((m.succ : ℕ) : ℚ) + (-1 : ℚ) = m := by push_cast; ring
    rw [hshift]
    exact (eq_sub_iff_add_eq).mpr hrecQ

/-- For a homogeneous prime in characteristic zero, the positive Hilbert
polynomial already determines the actual Krull dimension. -/
theorem projectiveSection_fullDegree_of_hilbertDegree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveHilbertDimensionDegree I r d) :
    HasProjectiveDimensionDegree I r d := by
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem_of_projectiveHilbertDimensionDegree I hdegree
  have hirr : ¬ projectiveIrrelevantIdeal K N ≤ I := by
    intro h
    exact hi (h (Ideal.subset_span ⟨i, rfl⟩))
  obtain ⟨s, e, Q, hcert⟩ := projectiveHilbertDegreeCertification_internal K
    N I hI hhom hirr
  obtain ⟨hd, P, hPdeg, hPlc, kP, hP⟩ := hdegree
  obtain ⟨hdim, he, hQdeg, hQlc, kQ, hQ⟩ := hcert
  have hPQ : P = Q := by
    let shift := max kP kQ
    let rationalValues : ℕ → ℚ := fun n ↦ ((n + shift : ℕ) : ℚ)
    have hinj : Function.Injective rationalValues := by
      intro a b hab
      change (((a + shift : ℕ) : ℚ)) = ((b + shift : ℕ) : ℚ) at hab
      have hn : a + shift = b + shift := by exact_mod_cast hab
      omega
    apply Polynomial.eq_of_infinite_eval_eq P Q
    apply (Set.infinite_range_of_injective hinj).mono
    rintro x ⟨n, rfl⟩
    have hPk : kP ≤ n + shift := by dsimp only [shift]; omega
    have hQk : kQ ≤ n + shift := by dsimp only [shift]; omega
    change P.eval ((n + shift : ℕ) : ℚ) = Q.eval ((n + shift : ℕ) : ℚ)
    rw [← hP _ hPk, ← hQ _ hQk]
  have hsr : s = r := by rw [← hQdeg, ← hPdeg, hPQ]
  exact ⟨by simpa only [hsr] using hdim, hd, P, hPdeg, hPlc, kP, hP⟩

/-- An actual prime linear section preserves degree and drops projective
dimension by one. The primality of the literal section ideal is explicit. -/
theorem projectiveSection_preserves_degree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I (r + 1) d)
    (L : MvPolynomial (Fin (N + 1)) K)
    (hLhom : L.IsHomogeneous 1) (hL : L ∉ I)
    (hsection : (I ⊔ Ideal.span ({L} : Set _)).IsPrime) :
    HasProjectiveDimensionDegree (I ⊔ Ideal.span ({L} : Set _)) r d := by
  apply projectiveSection_fullDegree_of_hilbertDegree _ hsection
  · apply hhom.sup
    apply Ideal.homogeneous_span
    rintro p rfl
    exact ⟨1, hLhom⟩
  · exact projectiveSection_preserves_hilbertDegree I hI hhom hdegree.toHilbert
      L hLhom hL

end

end TranslatedDepthSeven
