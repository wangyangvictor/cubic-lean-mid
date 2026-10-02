import TranslatedDepthSeven.FiniteEquationMinimalComponents

/-!
# Minimal components after adjoining equations

Every minimal component of I+J is a minimal component of P+J for some
minimal component P of I. Counting a component only once therefore bounds
any nonnegative weighted sum by the sum over all source components. This
algebraic fact has no equidimensionality or reducedness hypothesis.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A minimal component after adjoining J comes from at least one minimal
component before adjoining J. No uniqueness of that source is asserted. -/
theorem exists_sourceMinimalPrime_of_mem_minimalPrimes_sup
    (I J Q : Ideal R) (hQ : Q ∈ finiteMinimalPrimes (I ⊔ J)) :
    ∃ P ∈ finiteMinimalPrimes I, Q ∈ finiteMinimalPrimes (P ⊔ J) := by
  letI : Q.IsPrime := isPrime_of_mem_finiteMinimalPrimes hQ
  have hIQ : I ≤ Q := le_sup_left.trans (le_of_mem_finiteMinimalPrimes hQ)
  have hJQ : J ≤ Q := le_sup_right.trans (le_of_mem_finiteMinimalPrimes hQ)
  obtain ⟨P, hP, hPQ⟩ := exists_finiteMinimalPrime_le hIQ
  obtain ⟨Q', hQ', hQ'Q⟩ := exists_finiteMinimalPrime_le (sup_le hPQ hJQ)
  have hIJQ' : I ⊔ J ≤ Q' :=
    (sup_le_sup_right (le_of_mem_finiteMinimalPrimes hP) J).trans
      (le_of_mem_finiteMinimalPrimes hQ')
  have hQmin := (mem_finiteMinimalPrimes_iff (I ⊔ J) Q).mp hQ
  have hQQ' : Q ≤ Q' :=
    hQmin.2 ⟨isPrime_of_mem_finiteMinimalPrimes hQ', hIJQ'⟩ hQ'Q
  exact ⟨P, hP, (le_antisymm hQ'Q hQQ') ▸ hQ'⟩

/-- Weighted component sums do not increase when each target is counted
once instead of once for every possible source component. -/
theorem sum_minimalPrimes_sup_le_sum_source_cuts
    (I J : Ideal R) (weight : Ideal R → ℕ) :
    ∑ Q ∈ finiteMinimalPrimes (I ⊔ J), weight Q ≤
      ∑ P ∈ finiteMinimalPrimes I,
        ∑ Q ∈ finiteMinimalPrimes (P ⊔ J), weight Q := by
  classical
  let target := finiteMinimalPrimes (I ⊔ J)
  have hexists (Q : Ideal R) (hQ : Q ∈ target) :
      ∃ P ∈ finiteMinimalPrimes I, Q ∈ finiteMinimalPrimes (P ⊔ J) :=
    exists_sourceMinimalPrime_of_mem_minimalPrimes_sup I J Q hQ
  let source : Ideal R → Ideal R := fun Q ↦
    if hQ : Q ∈ target then Classical.choose (hexists Q hQ) else ⊤
  have hsource (Q : Ideal R) (hQ : Q ∈ target) :
      source Q ∈ finiteMinimalPrimes I ∧
        Q ∈ finiteMinimalPrimes (source Q ⊔ J) := by
    simpa only [source, dif_pos hQ] using Classical.choose_spec (hexists Q hQ)
  calc
    ∑ Q ∈ target, weight Q =
        ∑ P ∈ finiteMinimalPrimes I,
          ∑ Q ∈ target with source Q = P, weight Q :=
      (Finset.sum_fiberwise_of_maps_to (fun Q hQ ↦ (hsource Q hQ).1) weight).symm
    _ ≤ ∑ P ∈ finiteMinimalPrimes I,
          ∑ Q ∈ finiteMinimalPrimes (P ⊔ J), weight Q := by
      apply Finset.sum_le_sum
      intro P _hP
      apply Finset.sum_le_sum_of_subset
      intro Q hQ
      obtain ⟨hQt, hQP⟩ := Finset.mem_filter.mp hQ
      simpa only [hQP] using (hsource Q hQt).2

/-- A uniform multiplicative bound for each prime source gives the same
bound for an arbitrary finite union of components. -/
theorem sum_minimalPrimes_sup_le_mul_source_sum
    (I J : Ideal R) (weight sourceWeight : Ideal R → ℕ) (C : ℕ)
    (hbound : ∀ P ∈ finiteMinimalPrimes I,
      ∑ Q ∈ finiteMinimalPrimes (P ⊔ J), weight Q ≤ C * sourceWeight P) :
    ∑ Q ∈ finiteMinimalPrimes (I ⊔ J), weight Q ≤
      C * ∑ P ∈ finiteMinimalPrimes I, sourceWeight P := by
  calc
    _ ≤ ∑ P ∈ finiteMinimalPrimes I,
        ∑ Q ∈ finiteMinimalPrimes (P ⊔ J), weight Q :=
      sum_minimalPrimes_sup_le_sum_source_cuts I J weight
    _ ≤ ∑ P ∈ finiteMinimalPrimes I, C * sourceWeight P :=
      Finset.sum_le_sum hbound
    _ = _ := (Finset.mul_sum _ _ _).symm

end
end TranslatedDepthSeven
