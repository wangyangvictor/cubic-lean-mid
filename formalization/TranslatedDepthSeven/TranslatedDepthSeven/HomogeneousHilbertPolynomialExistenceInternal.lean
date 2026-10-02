import TranslatedDepthSeven.HilbertColonExactSequenceInternal
import TranslatedDepthSeven.HilbertAffineChange
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Eventual polynomiality of a homogeneous quotient Hilbert function

This is the elementary Hilbert--Serre argument by Noetherian induction on
ideals. For a variable outside `I`, both `I + (X)` and, unless unchanged,
`I : X` strictly contain `I`. The checked homogeneous exact sequence gives
the recurrence. If `I : X = I`, a discrete integral solves it, with its
constant fixed at one index beyond the section's polynomial threshold.

This file proves polynomial existence only. Identification of its degree
with dimension and of its leading coefficient with positive integral
multiplicity are separate algebraic statements, not assumptions here.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Discrete integration with its additive constant fixed at an eventual
polynomial threshold. -/
theorem exists_eventual_polynomial_of_successive_difference
    (f g : ℕ → ℚ)
    (hrec : ∀ n, f (n + 1) = f n + g (n + 1))
    (hg : ∃ P : Polynomial ℚ, ∃ n₀ : ℕ,
      ∀ n ≥ n₀, g n = P.eval (n : ℚ)) :
    ∃ Q : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀, f n = Q.eval (n : ℚ) := by
  classical
  obtain ⟨P, n₀, hP⟩ := hg
  let A := f n₀ - ∑ k ∈ Finset.range (n₀ + 1), P.eval (k : ℚ)
  refine ⟨Published.cumulativePolynomial P A, n₀, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [Published.cumulativePolynomial_eval]; dsimp [A]; ring
  | succ n hn ih =>
    rw [hrec, hP (n + 1) (by omega), ih,
      Published.cumulativePolynomial_eval, Published.cumulativePolynomial_eval,
      Finset.sum_range_succ (n := n + 1)]
    ring

/-- Two eventual polynomials remain polynomial under the shift occurring
in the homogeneous colon exact sequence. -/
theorem exists_eventual_polynomial_of_shifted_sum
    (f g h : ℕ → ℚ)
    (hrec : ∀ n, f (n + 1) = g (n + 1) + h n)
    (hg : ∃ P : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀, g n = P.eval (n : ℚ))
    (hh : ∃ P : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀, h n = P.eval (n : ℚ)) :
    ∃ Q : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀, f n = Q.eval (n : ℚ) := by
  obtain ⟨P, a, hP⟩ := hg
  obtain ⟨Q, b, hQ⟩ := hh
  refine ⟨P + Q.comp (Polynomial.X - 1), max a (b + 1), ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [hrec, hP (k + 1) (by omega), hQ k (by omega)]
  simp

/-- If all variables vanish in a quotient, every positive homogeneous
piece vanishes. This also handles an empty set of variables. -/
theorem quotientHomogeneousComponent_eq_bot_of_variables_mem
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hX : ∀ i, X i ∈ I)
    {n : ℕ} (hn : 0 < n) : quotientHomogeneousComponent K σ I n = ⊥ := by
  classical
  have hspan : Ideal.span (X '' (Set.univ : Set σ) : Set (MvPolynomial σ K)) ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    exact hX i
  have hmem : ∀ p : MvPolynomial σ K, p.IsHomogeneous n → p ∈ I := by
    intro p hp
    apply hspan
    apply mem_ideal_span_X_image.mpr
    intro d hd
    have hdne : d ≠ 0 := by
      intro heq
      subst d
      exact (mem_support_iff.mp hd) (hp.coeff_eq_zero (by simpa using hn.ne))
    have hex : ∃ i, d i ≠ 0 := by
      by_contra! h
      apply hdne
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Set.mem_univ i, hi⟩
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk I p = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem p hp)

/-- Hilbert--Serre polynomial existence, for arbitrary homogeneous ideals
over any field and any finite set of polynomial variables. -/
theorem exists_eventual_homogeneousHilbertPolynomial
    {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ P : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (Module.finrank K (quotientHomogeneousComponent K σ I n) : ℚ) =
        P.eval (n : ℚ) := by
  classical
  let HF := fun (J : Ideal (MvPolynomial σ K)) (n : ℕ) =>
    (Module.finrank K (quotientHomogeneousComponent K σ J n) : ℚ)
  change ∃ P : Polynomial ℚ, ∃ n₀ : ℕ, ∀ n ≥ n₀, HF I n = P.eval (n : ℚ)
  revert hI
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    intro hI
    by_cases hX : ∀ i, X i ∈ I
    · refine ⟨0, 1, ?_⟩
      intro n hn
      dsimp [HF]
      rw [quotientHomogeneousComponent_eq_bot_of_variables_mem I hX (by omega)]
      simp
    push_neg at hX
    obtain ⟨i, hi⟩ := hX
    let J := I ⊔ Ideal.span ({X i} : Set (MvPolynomial σ K))
    let C := I.colon (Ideal.span ({X i} : Set (MvPolynomial σ K)))
    have hIJ : I < J := by
      apply lt_of_le_of_ne le_sup_left
      intro heq
      apply hi
      rw [heq]
      exact (show Ideal.span ({X i} : Set (MvPolynomial σ K)) ≤ J from le_sup_right)
        (Ideal.subset_span (by simp))
    have hJ : J.IsHomogeneous (homogeneousSubmodule σ K) := by
      apply hI.sup
      apply Ideal.homogeneous_span
      intro p hp
      obtain rfl : p = X i := Set.mem_singleton_iff.mp hp
      exact ⟨1, isHomogeneous_X K i⟩
    have hC : C.IsHomogeneous (homogeneousSubmodule σ K) :=
      homogeneous_colon_span_singleton I hI (X i) (isHomogeneous_X K i)
    have hrec : ∀ n, HF I (n + 1) = HF J (n + 1) + HF C n := by
      intro n
      have hh := finrank_homogeneous_section_add_colon_eq I hI
        (X i) (isHomogeneous_X K i) n
      dsimp [HF, J, C]
      exact_mod_cast hh.symm
    have hJpoly := ih J hIJ hJ
    by_cases hCI : C = I
    · apply exists_eventual_polynomial_of_successive_difference (HF I) (HF J) _ hJpoly
      intro n
      simpa only [hCI, add_comm] using hrec n
    · have hIC : I < C := lt_of_le_of_ne Ideal.le_colon (Ne.symm hCI)
      exact exists_eventual_polynomial_of_shifted_sum (HF I) (HF J) (HF C)
        hrec hJpoly (ih C hIC hC)

end
end TranslatedDepthSeven
