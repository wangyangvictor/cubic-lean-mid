import TranslatedDepthSeven.HilbertAffineChange

/-!
# Recovering the projective Hilbert polynomial from the affine cone

The homogeneous Hilbert function is the first difference of the cumulative
Hilbert function.  We verify the degree and leading coefficient of that
difference by the previously proved discrete-integration formula; no
Hilbert-polynomial existence or dimension theorem is imported here.
-/

namespace TranslatedDepthSeven
namespace Published

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 2000000

def backwardDifferencePolynomial (P : Polynomial ℚ) : Polynomial ℚ :=
  P - P.comp (Polynomial.X - Polynomial.C 1)

@[simp] theorem backwardDifferencePolynomial_eval
    (P : Polynomial ℚ) (x : ℚ) :
    (backwardDifferencePolynomial P).eval x = P.eval x - P.eval (x - 1) := by
  simp [backwardDifferencePolynomial]

theorem cumulativePolynomial_backwardDifference (P : Polynomial ℚ) :
    cumulativePolynomial (backwardDifferencePolynomial P) (P.eval (-1)) = P := by
  have hnat (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (backwardDifferencePolynomial P).eval (k : ℚ)) + P.eval (-1) =
          P.eval (n : ℚ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        simp only [backwardDifferencePolynomial_eval, Nat.cast_add, Nat.cast_one] at ih ⊢
        have hx : (n : ℚ) + 1 - 1 = n := by ring
        rw [hx]
        linarith
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ ↦ (n : ℚ)))).mono
  rintro x ⟨n, rfl⟩
  exact (cumulativePolynomial_eval _ _ n).trans (hnat n)

theorem backwardDifferencePolynomial_ne_zero
    (P : Polynomial ℚ) (hP : 0 < P.natDegree) :
    backwardDifferencePolynomial P ≠ 0 := by
  intro hzero
  have heq := cumulativePolynomial_backwardDifference P
  rw [hzero] at heq
  have hconstant : cumulativePolynomial 0 (P.eval (-1)) =
      Polynomial.C (P.eval (-1)) := by
    simp [cumulativePolynomial, discreteIntegralPolynomial]
  rw [hconstant] at heq
  have hdegree := congrArg Polynomial.natDegree heq
  simp only [Polynomial.natDegree_C] at hdegree
  omega

theorem backwardDifferencePolynomial_degree_leading
    (P : Polynomial ℚ) (hP : 0 < P.natDegree) :
    (backwardDifferencePolynomial P).natDegree + 1 = P.natDegree ∧
      (backwardDifferencePolynomial P).leadingCoeff =
        P.leadingCoeff * (P.natDegree : ℚ) := by
  have hne := backwardDifferencePolynomial_ne_zero P hP
  have hdeg := cumulativePolynomial_natDegree
    (backwardDifferencePolynomial P) (P.eval (-1)) hne
  rw [cumulativePolynomial_backwardDifference] at hdeg
  refine ⟨hdeg.symm, ?_⟩
  have hlc := cumulativePolynomial_leadingCoeff
    (backwardDifferencePolynomial P) (P.eval (-1)) hne
  rw [cumulativePolynomial_backwardDifference] at hlc
  have hcast : ((backwardDifferencePolynomial P).natDegree : ℚ) + 1 =
      (P.natDegree : ℚ) := by exact_mod_cast hdeg.symm
  rw [hcast] at hlc
  exact (eq_div_iff (by positivity : (P.natDegree : ℚ) ≠ 0)).mp hlc |>.symm

/-- The reverse Hilbert shift for a positive-dimensional homogeneous cone.
The dimension equality in the conclusion is a numerical consequence of
the polynomial calculation, not an additional geometric hypothesis. -/
theorem exists_projectiveDimensionDegree_of_homogeneous_affineCone
    {K : Type*} [Field K] {N s d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K))
    (haffine : HasAffineDimensionDegree I s d) (hs : 0 < s) :
    ∃ r : ℕ, r + 1 = s ∧ HasProjectiveDimensionDegree I r d := by
  rcases haffine with ⟨hprime, hdim, hd, P, hPdegree, hPlc, k₀, heventual⟩
  let Q := backwardDifferencePolynomial P
  obtain ⟨hQdegree, hQlc⟩ := backwardDifferencePolynomial_degree_leading P
    (by omega)
  have hrs : Q.natDegree + 1 = s := hQdegree.trans hPdegree
  refine ⟨Q.natDegree, hrs, ?_, hd, Q, rfl, ?_, k₀ + 1, ?_⟩
  · simpa only [← hrs, Nat.cast_add, Nat.cast_one] using hdim
  · change (backwardDifferencePolynomial P).leadingCoeff = _
    rw [hQlc, hPlc, hPdegree, ← hrs, Nat.factorial_succ]
    push_cast
    field_simp
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hj : k₀ ≤ j := by omega
    have hj1 : k₀ ≤ j + 1 := by omega
    have hsumj := heventual j hj
    have hsumj1 := heventual (j + 1) hj1
    rw [affineHilbertFiltration_finrank_eq_sum_projectiveHilbertPiece I hI] at hsumj hsumj1
    push_cast at hsumj hsumj1
    rw [Finset.sum_range_succ] at hsumj1
    change _ = (backwardDifferencePolynomial P).eval ((j + 1 : ℕ) : ℚ)
    rw [backwardDifferencePolynomial_eval]
    have hx : ((j + 1 : ℕ) : ℚ) - 1 = j := by push_cast; ring
    rw [hx]
    push_cast
    linarith

end
end Published
end TranslatedDepthSeven
