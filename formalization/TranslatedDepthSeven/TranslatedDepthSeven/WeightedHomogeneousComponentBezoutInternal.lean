import TranslatedDepthSeven.ProperHomogeneousHypersurfaceCertificatesInternal
import TranslatedDepthSeven.MinimalPrimeCutDegreeSumInternal
import TranslatedDepthSeven.ProjectiveHilbertDegreeCertificationInternal

/-!
# Dimension-weighted degree under arbitrary homogeneous cuts

For B≥1, assign degree(P) B^dim(P) to each nonempty projective prime and
zero to the irrelevant prime. A homogeneous equation of degree at most B
cannot increase the total weight: a retained component is unchanged, and
a proper section has one less dimension and total degree at most B times
the source degree. Consequently an arbitrary finite equation family has
the same weighted bound, irrespective of its cardinality and of purity.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

/-- One homogeneous cut decreases the dimension-weighted degree. The
irrelevant component is given weight zero, including after cutting a
projective zero-fold by a nonvanishing equation. -/
theorem sum_projectiveDimensionDegreeWeight_single_cut_le
    {N B : ℕ} (hB : 1 ≤ B)
    (weight : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hweight : ∀ P r d, HasProjectiveDimensionDegree P r d → weight P = d * B ^ r)
    (hirr : ∀ P, P.IsPrime → projectiveIrrelevantIdeal ℚ N ≤ P → weight P = 0)
    (P : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hPprime : P.IsPrime)
    (hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (f : MvPolynomial (Fin (N + 1)) ℚ) (a : ℕ)
    (hfhom : f.IsHomogeneous a) (ha : a ≤ B) :
    ∑ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), weight Q ≤ weight P := by
  classical
  by_cases hfP : f ∈ P
  · have hcut : P ⊔ Ideal.span ({f} : Set _) = P :=
      sup_eq_left.mpr (Ideal.span_le.mpr (fun g hg ↦ (Set.mem_singleton_iff.mp hg) ▸ hfP))
    have hprimes : finiteMinimalPrimes P = {P} := by
      letI : P.IsPrime := hPprime
      ext Q
      simp only [mem_finiteMinimalPrimes_iff, Ideal.minimalPrimes_eq_subsingleton_self,
        Set.mem_singleton_iff, Finset.mem_singleton]
    simp only [hcut, hprimes, Finset.sum_singleton, le_refl]
  by_cases hPir : projectiveIrrelevantIdeal ℚ N ≤ P
  · have hzero : ∀ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), weight Q = 0 := by
      intro Q hQ
      exact hirr Q (isPrime_of_mem_finiteMinimalPrimes hQ)
        (hPir.trans (le_sup_left.trans (le_of_mem_finiteMinimalPrimes hQ)))
    rw [Finset.sum_eq_zero hzero]
    exact Nat.zero_le _
  obtain ⟨r, d, HP, hcert⟩ := projectiveHilbertDegreeCertification_internal ℚ
    N P hPprime hPhom hPir
  have hPcert := hcert.toPublished
  by_cases hr : r = 0
  · subst r
    have hzero : ∀ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), weight Q = 0 := by
      intro Q hQ
      have hQprime := isPrime_of_mem_finiteMinimalPrimes hQ
      have hcutHom : (P ⊔ Ideal.span ({f} : Set _)).IsHomogeneous
          (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
        apply hPhom.sup
        apply Ideal.homogeneous_span
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨a, hfhom⟩
      have hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
        apply isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
          hcutHom ((mem_finiteMinimalPrimes_iff _ _).mp hQ)
      by_cases hQir : projectiveIrrelevantIdeal ℚ N ≤ Q
      · exact hirr Q hQprime hQir
      obtain ⟨s, e, HQ, hQcert⟩ := projectiveHilbertDegreeCertification_internal ℚ
        N Q hQprime hQhom hQir
      have hPQ : P < Q := lt_of_le_of_ne
        (le_sup_left.trans (le_of_mem_finiteMinimalPrimes hQ)) (by
          intro heq
          apply hfP
          rw [heq]
          exact le_of_mem_finiteMinimalPrimes hQ
            ((show Ideal.span ({f} : Set _) ≤ P ⊔ Ideal.span ({f} : Set _) from le_sup_right)
              (Ideal.subset_span (Set.mem_singleton f))))
      letI : P.IsPrime := hPprime
      letI : Q.IsPrime := hQprime
      have hfinite : ringKrullDim (MvPolynomial (Fin (N + 1)) ℚ ⧸ P) < ⊤ := by
        rw [hPcert.1]
        change (↑((1 : ℕ) : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
        exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
      have hdim := ringKrullDim_quotient_lt_of_prime_lt P Q hPQ hfinite
      rw [hPcert.1, hQcert.toPublished.1] at hdim
      have : s + 1 < 0 + 1 := by exact_mod_cast hdim
      omega
    rw [Finset.sum_eq_zero hzero]
    exact Nat.zero_le _
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrsucc : r - 1 + 1 = r := by omega
    obtain ⟨deg, hc, hm⟩ := properHomogeneousHypersurface_componentDimensionDegreeMass
      (projectiveHilbertDegreeCertification_internal ℚ)
      (r := r - 1) P f hPprime hPhom (hrsucc.symm ▸ hPcert) hfhom hfP
    calc
      ∑ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), weight Q =
          (∑ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), deg Q) * B ^ (r - 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro Q hQ
        exact hweight Q (r - 1) (deg Q) (hc Q hQ)
      _ ≤ (d * a) * B ^ (r - 1) := Nat.mul_le_mul_right _ hm
      _ ≤ (d * B) * B ^ (r - 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d ha)
      _ = d * B ^ r := by
        conv_rhs => rw [← hrsucc, pow_succ]
        ring
      _ = weight P := (hweight P r d hPcert).symm

/-- Arbitrarily many homogeneous equations of degree at most B preserve
the source's weighted degree bound. No equidimensionality or lower bound
on the dimensions of the resulting components is assumed. -/
theorem iteratedHomogeneousCut_projectiveDimensionDegreeWeight_le
    {N B r d : ℕ} (hB : 1 ≤ B)
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ))
    (hIcert : HasProjectiveDimensionDegree I r d)
    (weight : Ideal (MvPolynomial (Fin (N + 1)) ℚ) → ℕ)
    (hweight : ∀ P s e, HasProjectiveDimensionDegree P s e → weight P = e * B ^ s)
    (hirr : ∀ P, P.IsPrime → projectiveIrrelevantIdeal ℚ N ≤ P → weight P = 0)
    (family : Finset (MvPolynomial (Fin (N + 1)) ℚ))
    (hfamily : ∀ f ∈ family, ∃ a ≤ B, f.IsHomogeneous a) :
    ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span (family : Set _)), weight P ≤ d * B ^ r := by
  classical
  induction family using Finset.induction_on with
  | empty =>
      have hprimes : finiteMinimalPrimes I = {I} := by
        letI : I.IsPrime := hIprime
        ext P
        simp only [mem_finiteMinimalPrimes_iff, Ideal.minimalPrimes_eq_subsingleton_self,
          Set.mem_singleton_iff, Finset.mem_singleton]
      simp only [Finset.coe_empty, Ideal.span_empty, sup_bot_eq, hprimes,
        Finset.sum_singleton, hweight I r d hIcert, le_refl]
  | @insert f S hf ih =>
      obtain ⟨a, ha, hfa⟩ := hfamily f (Finset.mem_insert_self _ _)
      have hS : ∀ g ∈ S, ∃ a ≤ B, g.IsHomogeneous a :=
        fun g hg ↦ hfamily g (Finset.mem_insert_of_mem hg)
      have hJhom : (I ⊔ Ideal.span (S : Set _)).IsHomogeneous
          (homogeneousSubmodule (Fin (N + 1)) ℚ) := by
        apply hIhom.sup
        apply Ideal.homogeneous_span
        intro g hg
        obtain ⟨a, _, hga⟩ := hS g hg
        exact ⟨a, hga⟩
      have hcutEq : I ⊔ Ideal.span ((insert f S : Finset _) : Set _) =
          (I ⊔ Ideal.span (S : Set _)) ⊔ Ideal.span ({f} : Set _) := by
        rw [Finset.coe_insert, Ideal.span_insert]
        ac_rfl
      rw [hcutEq]
      calc
        _ ≤ ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span (S : Set _)),
            ∑ Q ∈ finiteMinimalPrimes (P ⊔ Ideal.span ({f} : Set _)), weight Q :=
          sum_minimalPrimes_sup_le_sum_source_cuts _ _ _
        _ ≤ ∑ P ∈ finiteMinimalPrimes (I ⊔ Ideal.span (S : Set _)), weight P := by
          apply Finset.sum_le_sum
          intro P hP
          exact sum_projectiveDimensionDegreeWeight_single_cut_le hB weight hweight hirr
            P (isPrime_of_mem_finiteMinimalPrimes hP)
            (isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous hJhom
              ((mem_finiteMinimalPrimes_iff _ _).mp hP)) f a hfa ha
        _ ≤ d * B ^ r := ih hS

end
end TranslatedDepthSeven
