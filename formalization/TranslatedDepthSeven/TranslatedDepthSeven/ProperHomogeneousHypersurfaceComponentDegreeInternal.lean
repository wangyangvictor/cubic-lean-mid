import TranslatedDepthSeven.HomogeneousComponentDegreeUpperInternal
import TranslatedDepthSeven.PolynomialHilbertDifferenceInternal
import TranslatedDepthSeven.HomogeneousHypersurfaceHilbertBoundInternal

/-!
# Reduced component degree bound for a proper homogeneous hypersurface

Component dimension/degree certificates are explicit hypotheses. This
proves the degree bound only; it does not assert that such certificates
exist or that all minimal components have the expected dimension.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

universe u v

/-- A proper positive-degree homogeneous section has an eventual Hilbert
upper polynomial with dimension one less and degree at most the product. -/
theorem exists_hilbertPolynomial_upper_proper_homogeneous_hypersurface
    {K : Type u} [Field K] {N r d e : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hIprime : I.IsPrime)
    (hI : HasProjectiveDimensionDegree I (r + 1) d)
    (f : MvPolynomial (Fin (N + 1)) K)
    (hfhom : f.IsHomogeneous e) (hfnot : f ∉ I) (he : 0 < e) :
    ∃ Q : Polynomial ℚ, Q.natDegree = r ∧
      Q.leadingCoeff = (d * e : ℕ) / (r.factorial : ℚ) ∧
      ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (Module.finrank K (projectiveHilbertPiece K N
          (I ⊔ Ideal.span ({f} : Set _)) k) : ℚ) ≤ Q.eval (k : ℚ) := by
  obtain ⟨_hdim, hd, P, hPdegree, hPleading, k₀, heventual⟩ := hI
  let Q := P - Polynomial.taylor (-(e : ℚ)) P
  obtain ⟨hQdegree, hQleading⟩ :=
    polynomial_backwardDifference_hilbert_data P r d e hd he hPdegree hPleading
  refine ⟨Q, hQdegree, hQleading, k₀ + e, ?_⟩
  intro k hk
  have hek : e ≤ k := by omega
  have hsmall : k₀ ≤ k - e := by omega
  have hlarge : k₀ ≤ k := by omega
  have hsum : e + (k - e) = k := by omega
  have hsection := finrank_homogeneous_hypersurface_section_add_le
    I hIprime f hfhom hfnot (k - e)
  rw [hsum] at hsection
  have hsectionQ :
      (Module.finrank K (projectiveHilbertPiece K N
        (I ⊔ Ideal.span ({f} : Set _)) k) : ℚ) +
        P.eval ((k - e : ℕ) : ℚ) ≤ P.eval (k : ℚ) := by
    rw [← heventual (k - e) hsmall, ← heventual k hlarge]
    exact_mod_cast hsection
  have hQeval : Q.eval (k : ℚ) = P.eval (k : ℚ) - P.eval ((k - e : ℕ) : ℚ) := by
    simp only [Q, Polynomial.eval_sub, Polynomial.taylor_eval]
    rw [Nat.cast_sub hek]
    simp only [sub_eq_add_neg]
  rw [hQeval]
  linarith

/-- Proper homogeneous hypersurface degree bound for a supplied finite
family of distinct prime components of the expected projective dimension.

No reducedness of the section is required. The dimension and Hilbert-degree
certificates of the component primes remain explicit hypotheses. -/
theorem sum_projectiveDegrees_proper_homogeneous_hypersurface_le
    {K : Type u} [Field K] {N r d e : ℕ}
    {ι : Type v} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hIprime : I.IsPrime)
    (hI : HasProjectiveDimensionDegree I (r + 1) d)
    (f : MvPolynomial (Fin (N + 1)) K)
    (hfhom : f.IsHomogeneous e) (hfnot : f ∉ I)
    (P : ι → Ideal (MvPolynomial (Fin (N + 1)) K))
    (di : ι → ℕ) (hinjective : Function.Injective P)
    (hprime : ∀ i, (P i).IsPrime)
    (hhom : ∀ i, (P i).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdim : ∀ i, HasProjectiveDimensionDegree (P i) r (di i))
    (hcontain : ∀ i, I ⊔ Ideal.span ({f} : Set _) ≤ P i) :
    ∑ i, di i ≤ d * e := by
  classical
  by_cases hezero : e = 0
  · have hfdegree : f.totalDegree = 0 := Nat.eq_zero_of_le_zero (hezero ▸ hfhom.totalDegree_le)
    have hfC : f = C (f.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hfdegree
    have hc : f.coeff 0 ≠ 0 := by
      intro hc
      apply hfnot
      rw [hfC, hc, map_zero]
      exact I.zero_mem
    have hfunit : IsUnit f := by
      rw [hfC]
      exact (isUnit_iff_ne_zero.mpr hc).map C
    letI : IsEmpty ι := ⟨fun i ↦ (hprime i).ne_top
      ((P i).eq_top_of_isUnit_mem
        (hcontain i (show f ∈ I ⊔ Ideal.span ({f} : Set _) from
          (show Ideal.span ({f} : Set _) ≤ I ⊔ Ideal.span ({f} : Set _) from le_sup_right)
            (Ideal.subset_span (Set.mem_singleton f)))) hfunit)⟩
    simp [hezero]
  · have he : 0 < e := Nat.pos_of_ne_zero hezero
    obtain ⟨Q, hQdegree, hQleading, k₀, hupper⟩ :=
      exists_hilbertPolynomial_upper_proper_homogeneous_hypersurface I hIprime hI f hfhom hfnot he
    exact sum_projectiveDegrees_le_of_hilbertPolynomial_upper
      (I ⊔ Ideal.span ({f} : Set _)) P di hinjective hprime hhom hdim hcontain
      Q (Nat.mul_pos hI.2.1 he) hQdegree hQleading k₀ hupper

end

end TranslatedDepthSeven
