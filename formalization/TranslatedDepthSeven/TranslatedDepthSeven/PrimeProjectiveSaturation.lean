import TranslatedDepthSeven.ProjectivePrimeChartSaturation
import TranslatedDepthSeven.PublishedCountingTheorems
import TranslatedDepthSeven.HomogeneousLinearNormalizationBoxCount

/-!
# Saturation of a projective prime component

A prime homogeneous cone which does not contain the irrelevant ideal is
already saturated with respect to that ideal.  The proof is elementary and
uses one coordinate absent from the prime.  This supplies the literal
saturation conjunct in `Published.IsIntegralProjectiveVariety`; it does not
postulate any projective-scheme interface.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

local instance primeProjectiveSaturationClassicalDecidablePred
    {A : Type*} (p : A → Prop) : DecidablePred p := Classical.decPred p

/-- If one coordinate is absent from a prime ideal, colon by every power of
the full irrelevant ideal is the prime itself. -/
theorem colon_projectiveIrrelevantIdeal_pow_eq_prime
    {N : ℕ}
    {P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hP : P.IsPrime) {i : Fin (N + 1)} (hi : X i ∉ P) (k : ℕ) :
    P.colon ((Published.projectiveIrrelevantIdeal ℚ N) ^ k) = P := by
  apply le_antisymm
  · intro f hf
    have hXi : X i ∈ Published.projectiveIrrelevantIdeal ℚ N := by
      apply Ideal.subset_span
      exact ⟨i, rfl⟩
    have hXik : X i ^ k ∈
        (Published.projectiveIrrelevantIdeal ℚ N) ^ k :=
      Ideal.pow_mem_pow hXi k
    have hmul : f * X i ^ k ∈ P := by
      exact (Submodule.mem_colon.mp hf) (X i ^ k) hXik
    exact (X_pow_mul_mem_prime_iff hP hi k f).mp (by
      simpa [mul_comm] using hmul)
  · exact Ideal.le_colon

/-- A prime cone not containing the irrelevant ideal is literally saturated
in the sense required by the published projective counting theorem. -/
theorem prime_isSaturatedByProjectiveIrrelevantIdeal
    {N : ℕ}
    {P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hP : P.IsPrime)
    (hirr : ¬ Published.projectiveIrrelevantIdeal ℚ N ≤ P) :
    Published.IsSaturatedByProjectiveIrrelevantIdeal P := by
  have hexists : ∃ i : Fin (N + 1), X i ∉ P := by
    by_contra h
    push_neg at h
    apply hirr
    rw [Published.projectiveIrrelevantIdeal]
    exact Ideal.span_le.mpr fun _ hf ↦ by
      obtain ⟨i, rfl⟩ := hf
      exact h i
  obtain ⟨i, hi⟩ := hexists
  unfold Published.IsSaturatedByProjectiveIrrelevantIdeal
  apply le_antisymm
  · exact le_iSup_of_le 0 Ideal.le_colon
  · refine iSup_le fun k ↦ ?_
    rw [colon_projectiveIrrelevantIdeal_pow_eq_prime hP hi k]

/-- Homogeneity, primality, and avoidance of the irrelevant ideal provide
all projective-integrality conditions except the Hilbert dimension--degree
formula. -/
theorem homogeneousPrime_projectiveQualification
    {N : ℕ}
    {P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hP : P.IsPrime)
    (hirr : ¬ Published.projectiveIrrelevantIdeal ℚ N ≤ P) :
    P.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
      Published.IsSaturatedByProjectiveIrrelevantIdeal P ∧
      P.IsPrime := by
  exact ⟨hhom, prime_isSaturatedByProjectiveIrrelevantIdeal hP hirr, hP⟩

/-- The affine zero locus of an ideal containing the irrelevant coordinate
ideal consists only of the cone vertex. -/
theorem eq_zero_of_mem_affineIdealZeroLocus_of_irrelevant_le
    {N : ℕ}
    {Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (hirr : Published.projectiveIrrelevantIdeal ℚ N ≤ Q)
    {x : Fin (N + 1) → ℚ} (hx : x ∈ affineIdealZeroLocus Q) :
    x = 0 := by
  funext i
  have hXi : X i ∈ Published.projectiveIrrelevantIdeal ℚ N := by
    apply Ideal.subset_span
    exact ⟨i, rfl⟩
  have := hx (X i) (hirr hXi)
  simpa using this

/-- Consequently an irrelevant component contributes at most one point to
every positive affine congruence rescaling. -/
theorem irrelevantComponent_affineDisplacement_card_le_one
    {N : ℕ}
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hirr : Published.projectiveIrrelevantIdeal ℚ N ≤ Q)
    (points : Finset (IntVector (N + 1)))
    (x₀ : IntVector (N + 1)) (m : ℕ) (hm : 0 < m) :
    (points.filter fun z ↦
      (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) ∈
        affineIdealZeroLocus Q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro z hz z' hz'
  have hz0 : (fun i ↦ (integralAffineMap x₀ z m i : ℚ)) = 0 :=
    eq_zero_of_mem_affineIdealZeroLocus_of_irrelevant_le hirr
      (Finset.mem_filter.mp hz).2
  have hz'0 : (fun i ↦ (integralAffineMap x₀ z' m i : ℚ)) = 0 :=
    eq_zero_of_mem_affineIdealZeroLocus_of_irrelevant_le hirr
      (Finset.mem_filter.mp hz').2
  apply integralAffineMap_injective hm x₀
  funext i
  have hcast := congrFun (hz0.trans hz'0.symm) i
  exact_mod_cast hcast

/-- Every actual minimal component of the literal Jacobian exceptional
locus which survives projectivization supplies all the projective
integrality data except its Hilbert dimension--degree formula. -/
theorem exceptionalMinimalPrime_projectiveQualification
    {N : ℕ} (equations : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hhomogeneous : ∀ f ∈ equations, ∃ d : ℕ, f.IsHomogeneous d)
    (Q : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hQ : Q ∈ finiteMinimalPrimes
      (depthSevenJacobianExceptionalIdeal equations))
    (hirr : ¬ Published.projectiveIrrelevantIdeal ℚ N ≤ Q) :
    Q.IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℚ) ∧
      Published.IsSaturatedByProjectiveIrrelevantIdeal Q ∧
      Q.IsPrime := by
  have hQprime : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  exact homogeneousPrime_projectiveQualification
    (exceptionalMinimalPrime_isHomogeneous equations hhomogeneous hQ)
    hQprime hirr

end

end TranslatedDepthSeven
