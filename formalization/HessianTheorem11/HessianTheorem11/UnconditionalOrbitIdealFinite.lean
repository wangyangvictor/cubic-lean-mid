import HessianTheorem11.UnconditionalOrbitIdeal
import Mathlib.RingTheory.Polynomial.Basic

/-! A finite cutoff of the invariant ideal generates the entire ideal.
Consequently its actual evaluation map has exactly the prescribed zero
locus, not merely a subset of the target's equations. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial Module
variable {K : Type*} [Field K] {σ : Type*} [Fintype σ]

theorem exists_boundedIdeal_generates (S : Set (σ → K)) :
    ∃ N : ℕ, Ideal.span (boundedIdeal S N : Set (MvPolynomial σ K)) = vanishingIdeal K S := by
  classical
  obtain ⟨s,hs⟩ := IsNoetherian.noetherian (vanishingIdeal K S)
  let N := s.sup MvPolynomial.totalDegree
  refine ⟨N,le_antisymm ?_ ?_⟩
  · apply Ideal.span_le.mpr
    intro P hP
    exact hP.1
  · rw [← hs]
    apply Ideal.span_le.mpr
    intro P hP
    apply Ideal.subset_span
    apply (mem_boundedIdeal S N P).mpr
    refine ⟨?_,?_⟩
    · have h : P ∈ vanishingIdeal K S := by rw [← hs]; exact Submodule.subset_span hP
      exact h
    · exact Finset.le_sup (f := MvPolynomial.totalDegree) hP

theorem boundedEvaluation_eq_zero_iff (S : Set (σ → K)) (N : ℕ)
    (hgen : Ideal.span (boundedIdeal S N : Set (MvPolynomial σ K)) = vanishingIdeal K S)
    (x : σ → K) :
    boundedEvaluation S N x = 0 ↔ x ∈ zeroLocus K (vanishingIdeal K S) := by
  constructor
  · intro hz
    have hker : vanishingIdeal K S ≤ RingHom.ker (eval x) := by
      rw [← hgen]
      apply Ideal.span_le.mpr
      intro P hP
      exact congrArg (fun f : Dual K (boundedIdeal S N) => f ⟨P,hP⟩) hz
    exact fun P hP => hker hP
  · intro hx
    apply LinearMap.ext
    intro P
    exact hx P.val P.property.1

end HessianTheorem11.UnconditionalOrbitIdeal
