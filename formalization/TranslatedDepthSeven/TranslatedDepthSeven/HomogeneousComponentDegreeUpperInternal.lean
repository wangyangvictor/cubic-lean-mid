import TranslatedDepthSeven.HomogeneousComponentDegreeMassInternal

/-!
# Component degrees from an eventual Hilbert upper polynomial

An upper bound, rather than an equality with the containing scheme's
Hilbert polynomial, suffices for the previously proved comparison.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- The exact component-degree comparison using only an eventual upper
polynomial for the containing ideal's homogeneous pieces. -/
theorem sum_projectiveDegrees_le_of_hilbertPolynomial_upper
    {K : Type u} [Field K] {N r d : ℕ}
    {ι : Type v} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (P : ι → Ideal (MvPolynomial (Fin (N + 1)) K))
    (di : ι → ℕ) (hinjective : Function.Injective P)
    (hprime : ∀ i, (P i).IsPrime)
    (hhom : ∀ i, (P i).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdim : ∀ i, HasProjectiveDimensionDegree (P i) r (di i))
    (hcontain : ∀ i, I ≤ P i)
    (Q : Polynomial ℚ) (hd : 0 < d)
    (hQdegree : Q.natDegree = r)
    (hQleading : Q.leadingCoeff = (d : ℚ) / r.factorial)
    (k₀ : ℕ)
    (hupper : ∀ k ≥ k₀,
      (Module.finrank K (projectiveHilbertPiece K N I k) : ℚ) ≤ Q.eval (k : ℚ)) :
    ∑ i, di i ≤ d := by
  classical
  obtain ⟨E, hbound⟩ := exists_shift_sum_finrank_homogeneousComponents_le
    I P di hinjective hprime hhom hdim hcontain
  choose Pi hPdegree hPleading ki hPeval using fun i ↦ (hdim i).2.2
  let kbase : ℕ := max k₀ (Finset.univ.sup ki)
  apply sum_degrees_le_of_shifted_hilbertPolynomial_comparison
    Pi Q r d E kbase di hd (fun i ↦ (hdim i).2.1)
    hPdegree hPleading hQdegree hQleading
  intro n hn
  have hki (i : ι) : ki i ≤ n :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  have hkQ : k₀ ≤ n + E := by
    have hk : k₀ ≤ n := (le_max_left _ _).trans hn
    omega
  have hleft : (∑ i, (Pi i).eval (n : ℚ)) =
      ∑ i, (Module.finrank K (projectiveHilbertPiece K N (P i) n) : ℚ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hPeval i n (hki i)).symm
  rw [hleft]
  apply le_trans _ (hupper (n + E) hkQ)
  exact_mod_cast hbound n

end

end TranslatedDepthSeven
