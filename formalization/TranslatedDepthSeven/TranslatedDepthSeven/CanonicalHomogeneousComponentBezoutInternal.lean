import TranslatedDepthSeven.WeightedHomogeneousComponentBezoutInternal
import TranslatedDepthSeven.ProjectiveDegreeOneSpan

/-!
# Canonical projective component weights

The dimensions and degrees are taken from the actual Hilbert certificates,
not from an assumed bound on components. The irrelevant prime has weight
zero. This specializes the homogeneous cut induction to projective space.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

def projectiveDimensionDegreeWeight {N : ℕ} (B : ℕ)
    (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) : ℕ := by
  classical
  exact if h : ∃ r d : ℕ, HasProjectiveDimensionDegree P r d then
    h.choose_spec.choose * B ^ h.choose
  else 0

theorem projectiveDimensionDegreeWeight_eq {N B r d : ℕ}
    {P : Ideal (MvPolynomial (Fin (N + 1)) ℚ)}
    (h : HasProjectiveDimensionDegree P r d) :
    projectiveDimensionDegreeWeight B P = d * B ^ r := by
  classical
  have hex : ∃ s e : ℕ, HasProjectiveDimensionDegree P s e := ⟨r, d, h⟩
  rw [projectiveDimensionDegreeWeight, dif_pos hex]
  have hc := hex.choose_spec.choose_spec
  have hs : hex.choose + 1 = r + 1 := by exact_mod_cast hc.1.symm.trans h.1
  have hdim : hex.choose = r := by omega
  have hc' : HasProjectiveDimensionDegree P r hex.choose_spec.choose :=
    Eq.mp (congrArg (fun s ↦ HasProjectiveDimensionDegree P s hex.choose_spec.choose) hdim) hc
  have hdeg := projectiveDegree_eq_of_hasProjectiveDimensionDegree hc' h
  rw [hdeg, hdim]

theorem projectiveDimensionDegreeWeight_eq_zero_of_irrelevant
    {N B : ℕ} (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hPprime : P.IsPrime) (hirr : projectiveIrrelevantIdeal ℚ N ≤ P) :
    projectiveDimensionDegreeWeight B P = 0 := by
  classical
  unfold projectiveDimensionDegreeWeight
  apply dif_neg
  rintro ⟨r, d, hcert⟩
  have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le N P hPprime hirr
  have hbad : r + 1 = 0 := by exact_mod_cast hcert.1.symm.trans hzero
  omega

theorem hasProjectiveDimensionDegree_bot (N : ℕ) :
    HasProjectiveDimensionDegree
      (⊥ : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) N 1 := by
  refine ⟨?_, by omega, Polynomial.preHilbertPoly ℚ N 0, ?_, ?_, 0, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv
      (RingEquiv.quotientBot (MvPolynomial (Fin (N + 1)) ℚ)),
      ringKrullDim_mvPolynomial_fin_eq_of_field]
    norm_cast
  · exact Polynomial.natDegree_preHilbertPoly ℚ N 0
  · simpa only [Nat.cast_one, one_div] using
      Polynomial.leadingCoeff_preHilbertPoly ℚ N 0
  · intro k _
    have hmap :
        Module.finrank ℚ (projectiveHilbertPiece ℚ N ⊥ k) =
          Module.finrank ℚ (homogeneousSubmodule (Fin (N + 1)) ℚ k) := by
      exact (AlgEquiv.quotientBot ℚ
        (MvPolynomial (Fin (N + 1)) ℚ)).symm.toLinearEquiv.finrank_map_eq _
    rw [hmap, finrank_mvPolynomial_homogeneousSubmodule_fin]
    have heval := Polynomial.preHilbertPoly_eq_choose_sub_add ℚ N
      (k := 0) (n := k) (by omega)
    have hsymm : (N + 1 + k - 1).choose k = (k + N).choose N := by
      have h : N + 1 + k - 1 = k + N := by omega
      rw [h]
      simpa using (Nat.choose_symm (by omega : k ≤ k + N)).symm
    rw [hsymm]
    simpa using heval.symm

/-- The weighted sum of all nonempty projective components of an arbitrary
finite homogeneous family of degrees at most B is at most B^N. Components
of different dimensions are all retained in this one sum. -/
theorem finiteHomogeneousEquation_projectiveWeight_sum_le
    {N B : ℕ} (hB : 1 ≤ B)
    (family : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hfamily : ∀ f ∈ family, ∃ a ≤ B, f.IsHomogeneous a) :
    ∑ P ∈ finiteMinimalPrimes (finiteEquationIdeal family),
      projectiveDimensionDegreeWeight B P ≤ B ^ N := by
  have h := iteratedHomogeneousCut_projectiveDimensionDegreeWeight_le
    hB (⊥ : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (Ideal.bot_prime) (Ideal.IsHomogeneous.bot _)
    (hasProjectiveDimensionDegree_bot N)
    (projectiveDimensionDegreeWeight B)
    (fun P r d h ↦ projectiveDimensionDegreeWeight_eq h)
    (fun P hp hi ↦ projectiveDimensionDegreeWeight_eq_zero_of_irrelevant P hp hi)
    family hfamily
  simpa only [bot_sup_eq, one_mul, finiteEquationIdeal] using h

end
end TranslatedDepthSeven
