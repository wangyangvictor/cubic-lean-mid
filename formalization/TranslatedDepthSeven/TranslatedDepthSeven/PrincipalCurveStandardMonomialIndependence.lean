import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Standard monomials for a principal polynomial quotient

A finite family of distinct monomials none of which is divisible by the
leading monomial of `f` stays linearly independent modulo `(f)`. This direct
leading-term proof is the only Groebner-basis fact needed for the affine
curve determinant block.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
open scoped BigOperators

theorem linearIndependent_standardMonomials_quotient_principal
    {K σ ι : Type*} [Field K] [Fintype ι]
    (m : MonomialOrder σ) (f : MvPolynomial σ K) (hf : f ≠ 0)
    (d : ι → σ →₀ ℕ) (hd : Function.Injective d)
    (hstandard : ∀ i, ¬ m.degree f ≤ d i) :
    LinearIndependent K (fun i =>
      Ideal.Quotient.mk (Ideal.span ({f} : Set _)) (monomial (d i) 1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let g : MvPolynomial σ K := ∑ i, c i • monomial (d i) 1
  have hgmem : g ∈ Ideal.span ({f} : Set _) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ K (Ideal.span ({f} : Set _)) g = 0
    simpa only [g, map_sum, map_smul] using hc
  have hgzero : g = 0 := by
    by_contra hg
    have hlead : g.coeff (m.degree g) ≠ 0 :=
      m.leadingCoeff_ne_zero_iff.mpr hg
    have hsum : (∑ i, c i * (monomial (d i) (1 : K)).coeff (m.degree g)) ≠ 0 := by
      simpa only [g, coeff_sum, coeff_smul, smul_eq_mul] using hlead
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hdgi : m.degree g = d i := by
      by_contra h
      simp only [coeff_monomial] at hi
      split_ifs at hi with heq
      · exact h heq.symm
      · simp at hi
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton.mp hgmem
    have hhne : h ≠ 0 := by
      intro hz
      apply hg
      simpa [hz] using hh
    have hdiv : m.degree f ≤ m.degree g := by
      rw [hh, m.degree_mul hf hhne]
      exact le_add_of_nonneg_right (zero_le _)
    exact hstandard i (hdgi ▸ hdiv)
  have hli := (MvPolynomial.basisMonomials σ K).linearIndependent.comp d hd
  apply Fintype.linearIndependent_iff.mp hli c
  simpa only [MvPolynomial.coe_basisMonomials, Function.comp_apply] using hgzero

end
end TranslatedDepthSeven
