import TranslatedDepthSeven.PublishedCountingTheorems

/-!
# Direct specializations of the permitted published counting theorems

This file performs only quantifier instantiation.  Its theorems expose the
four bibliographic propositions in the forms used later, without adding a
geometric decomposition or a branch estimate to the external boundary.
-/

namespace TranslatedDepthSeven
namespace Published

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization

/-- Pila's printed inequality for one displayed affine ideal. -/
theorem pila1995_theoremA_apply
    (hPila : Pila1995TheoremA)
    {n d N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℝ))
    (hd : 1 ≤ d)
    (hI : HasAffineDimensionDegree I n d) :
    ∃ c : ℝ, 0 < c ∧
      ∀ H : ℝ, 1 < H →
        ((pilaIntegralPoints I H).card : ℝ) ≤
          c * H ^ ((n : ℝ) - 1 + (d : ℝ)⁻¹) *
            Real.exp
              (12 * Real.sqrt
                ((d : ℝ) * Real.log H * Real.log (Real.log H))) := by
  obtain ⟨c, hc, hbound⟩ := hPila n d N hd
  exact ⟨c, hc, hbound I (HasAffineDimensionDegree.toHilbert hI)⟩

/-- Salberger's non-uniform projective dimension-growth theorem for one
displayed saturated homogeneous prime ideal. -/
theorem salberger2023_theorem01_apply
    (hSalberger : Salberger2023Theorem01)
    {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : IsIntegralProjectiveVariety I r d)
    (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      (rationalProjectivePoints I B).Finite ∧
      ((rationalProjectivePoints I B).ncard : ℝ) ≤
        C * B ^ ((r : ℝ) + ε) := by
  exact hSalberger N r d I hI hd ε hε

/-- Salberger's coefficient-uniform affine hypersurface theorem for one
displayed polynomial and its top homogeneous part. -/
theorem salberger2023_theorem04_apply
    (hSalberger : Salberger2023Theorem04)
    {N d : ℕ} (hN : 3 ≤ N) (hd : d = 3 ∨ 4 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin N) ℤ)
        (h : MvPolynomial (Fin N) ℚ),
        IsTopHomogeneousPart f h d → IsAbsolutelyIrreducible h →
        ∀ B : ℝ, 1 ≤ B →
          ((affineHypersurfaceIntegerPoints f B).card : ℝ) ≤
            C * B ^ salberger2023AffineExponent N d ε := by
  exact hSalberger N d hN hd ε hε

/-- The multiplicity-one specialization of Salberger 2007, Corollary 3.7.
The product condition remains visible and is not replaced by a later branch
bound. -/
theorem salberger2007_corollary37_multiplicityOne
    (hSalberger : Salberger2007Corollary37)
    {N d r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hr : 1 ≤ r)
    (hI : IsReducedEquidimensionalProjectiveScheme I r d)
    (hinfinity : InfinityHyperplaneMeetsProperly I)
    {B : ℝ} (hB : 1 ≤ B)
    {index : Type} [Fintype index]
    (prime : index → ℕ)
    (hprime : ∀ i, (prime i).Prime)
    (hinjective : Function.Injective prime)
    (point : ∀ i, Fin (N + 1) → ZMod (prime i))
    (hchart : ∀ i, point i 0 ≠ 0)
    (hmultiplicity : ∀ i,
      HasHilbertSamuelMultiplicityAt (hprime i)
        (projectiveSpecialFiberIdeal I) (point i) r 1)
    (hproduct :
      B ^ (1 + ε) ≤
        ∏ i, (prime i : ℝ) ^
          (((d : ℝ) / (1 : ℝ)) ^ ((r : ℝ)⁻¹))) :
    ∃ K : ℕ,
      ∃ (k : ℕ) (G : MvPolynomial (Fin (N + 1)) ℚ),
        k ≤ K ∧ G.IsHomogeneous k ∧ G ∉ I ∧
          ∀ x, InSalbergerSOne I B prime point x →
            MvPolynomial.eval (fun i ↦ (x i : ℚ)) G = 0 := by
  obtain ⟨K, hK⟩ := hSalberger N d ε hε
  refine ⟨K, ?_⟩
  have hproduct' :
      B ^ (1 + ε) ≤
        ∏ i, (prime i : ℝ) ^
          (((d : ℝ) / ((1 : ℕ) : ℝ)) ^ ((r : ℝ)⁻¹)) := by
    simpa using hproduct
  exact hK r hr I hI hinfinity B hB index inferInstance prime hprime
    hinjective (fun _ ↦ 1) (fun _ ↦ Nat.zero_lt_succ 0) point hchart
    hmultiplicity hproduct'

end

end Published
end TranslatedDepthSeven
