import TranslatedDepthSeven.ProperHomogeneousHypersurfaceComponentDegreeInternal
import TranslatedDepthSeven.FiniteEquationComponentDimensionInternal
import TranslatedDepthSeven.HomogeneousIrrelevantDimensionFieldInternal

/-!
# Proper hypersurface components from Hilbert certification

For a positive-dimensional projective prime source, the internally proved
finite-equation dimension theorem and strict prime dimension drop force
every proper hypersurface component to have the expected dimension.
Hilbert certification then supplies the actual degrees, and the checked
component comparison bounds their sum by the product of the degrees.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type*} [Field K] [CharZero K]

/-- The complete component certificate and degree-sum statement
for a proper homogeneous hypersurface in positive projective dimension.
It needs only the existing Hilbert certification over the coefficient field, not Bezout or an extra
dimension hypothesis. -/
theorem properHomogeneousHypersurface_componentDimensionDegreeMass_over_field
    (hHilbert : StandardAG.ProjectiveHilbertDegreeCertification K)
    {N r d a : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (G : MvPolynomial (Fin (N + 1)) K)
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hIprojective : HasProjectiveDimensionDegree I (r + 1) d)
    (hGhom : G.IsHomogeneous a) (hGnot : G ∉ I) :
    ∃ degree : Ideal (MvPolynomial (Fin (N + 1)) K) → ℕ,
      (∀ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)),
        HasProjectiveDimensionDegree P r (degree P)) ∧
      ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span ({G} : Set _)), degree P ≤ d * a := by
  classical
  let J := I ⊔ Ideal.span ({G} : Set _)
  have hGideal : (Ideal.span ({G} : Set _)).IsHomogeneous
      (homogeneousSubmodule (Fin (N + 1)) K) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    exact ⟨a, hGhom⟩
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) :=
    hIhom.sup hGideal
  have hPhom (P : Ideal (MvPolynomial (Fin (N + 1)) K))
      (hP : P ∈ finiteMinimalPrimes J) :
      P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) :=
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
      ((mem_finiteMinimalPrimes_iff J P).mp hP)
  have hexists (P : Ideal (MvPolynomial (Fin (N + 1)) K))
      (hP : P ∈ finiteMinimalPrimes J) :
      ∃ e : ℕ, HasProjectiveDimensionDegree P r e := by
    have hPprime := isPrime_of_mem_finiteMinimalPrimes hP
    letI : I.IsPrime := hIprime
    letI : P.IsPrime := hPprime
    obtain ⟨t, ht, htlower⟩ := finiteEquation_minimalComponent_dimension_lower
      K (MvPolynomial (Fin (N + 1)) K) I P ({G} : Finset _)
      (by simpa only [Finset.coe_singleton] using (mem_finiteMinimalPrimes_iff J P).mp hP)
      (n := r + 2) (by simpa [Nat.add_assoc] using hIprojective.1)
    simp only [Finset.card_singleton] at htlower
    have htpos : 0 < t := by omega
    have hirrelevant : ¬ projectiveIrrelevantIdeal K N ≤ P := by
      intro hirr
      have hzero := ringKrullDim_quotient_eq_zero_of_irrelevant_le_over_field N P hPprime hirr
      have htzero : t = 0 := by exact_mod_cast ht.symm.trans hzero
      omega
    obtain ⟨s, e, HP, hcert⟩ := hHilbert N P hPprime (hPhom P hP) hirrelevant
    have hproj := hcert.toPublished
    have hts : t = s + 1 := by exact_mod_cast ht.symm.trans hproj.1
    have hJP : J ≤ P := le_of_mem_finiteMinimalPrimes hP
    have hGP : G ∈ P := hJP
      ((show Ideal.span ({G} : Set _) ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton G)))
    have hIP : I < P := lt_of_le_of_ne (le_sup_left.trans hJP) (by
      intro heq
      exact hGnot (heq.symm ▸ hGP))
    have hfinite : ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) < ⊤ := by
      rw [hIprojective.1]
      change (↑((r + 1 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
      exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
    have hupper := ringKrullDim_quotient_lt_of_prime_lt I P hIP hfinite
    rw [hproj.1, hIprojective.1] at hupper
    have hu : s + 1 < r + 1 + 1 := by exact_mod_cast hupper
    have hs : s = r := by omega
    exact ⟨e, hs ▸ hproj⟩
  have htotal (P : Ideal (MvPolynomial (Fin (N + 1)) K)) :
      ∃ e : ℕ, P ∈ finiteMinimalPrimes J → HasProjectiveDimensionDegree P r e := by
    by_cases hP : P ∈ finiteMinimalPrimes J
    · obtain ⟨e, he⟩ := hexists P hP
      exact ⟨e, fun _ ↦ he⟩
    · exact ⟨0, fun h ↦ False.elim (hP h)⟩
  choose degree hdegree using htotal
  refine ⟨degree, hdegree, ?_⟩
  have hmass := sum_projectiveDegrees_proper_homogeneous_hypersurface_le
    I hIprime hIprojective G hGhom hGnot
    (fun P : ↥(finiteMinimalPrimes J) ↦ P.1)
    (fun P : ↥(finiteMinimalPrimes J) ↦ degree P.1)
    Subtype.val_injective
    (fun P ↦ isPrime_of_mem_finiteMinimalPrimes P.2)
    (fun P ↦ hPhom P.1 P.2) (fun P ↦ hdegree P.1 P.2)
    (fun P ↦ le_of_mem_finiteMinimalPrimes P.2)
  simpa only [Finset.sum_coe_sort] using hmass

end

end TranslatedDepthSeven
