import TranslatedDepthSeven.FiniteEquationMinimalComponents
import TranslatedDepthSeven.FiniteComponentFrontier
import TranslatedDepthSeven.LocalizedIdealEquality
import TranslatedDepthSeven.CharacteristicPolynomialHeight

/-!
# Isolating one reduced component on a principal open

Let `P` be a minimal prime over an ideal `I` in a Noetherian ring.  There is
one element `s ∉ P` such that, after inverting `s`, the radical of `I` equals
`P`.  The proof chooses, for every other minimal component `Q`, one element
of `Q \ P` and multiplies these finitely many separators.

Applied in a fixed polynomial family, `s` is itself one fixed polynomial in
the family parameters.  Consequently its specialized size has an elementary
polynomial bound; no separate effective-algebra oracle is needed for this
component-isolation step.
-/

namespace TranslatedDepthSeven

noncomputable section

open Finset

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A minimal component can be separated from all the other minimal
components by one element outside that component.  Multiplication by the
separator sends the whole selected prime into the radical of the original
ideal. -/
theorem exists_minimalComponent_separator
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ∃ s : R, s ∉ P ∧ ∀ x ∈ P, s * x ∈ I.radical := by
  classical
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  let components : Finset (Ideal R) := finiteMinimalPrimes I
  let others : Finset (Ideal R) := components.erase P
  have hsep : ∀ Q ∈ others, ∃ a : R, a ∈ Q ∧ a ∉ P := by
    intro Q hQ
    have hQcomponent : Q ∈ finiteMinimalPrimes I := by
      exact (Finset.mem_of_mem_erase hQ)
    have hQP : Q ≠ P := (Finset.ne_of_mem_erase hQ)
    have hnle : ¬Q ≤ P := by
      intro hle
      apply hQP
      exact finiteMinimalPrimes_eq_of_le hQcomponent
        ((mem_finiteMinimalPrimes_iff I P).mpr hP) hle
    simpa only [SetLike.not_le_iff_exists] using hnle
  let a : Ideal R → R := fun Q ↦
    if hQ : Q ∈ others then Classical.choose (hsep Q hQ) else 1
  have ha_mem : ∀ Q, ∀ hQ : Q ∈ others, a Q ∈ Q := by
    intro Q hQ
    simp only [a, dif_pos hQ]
    exact (Classical.choose_spec (hsep Q hQ)).1
  have ha_not_mem : ∀ Q, ∀ hQ : Q ∈ others, a Q ∉ P := by
    intro Q hQ
    simp only [a, dif_pos hQ]
    exact (Classical.choose_spec (hsep Q hQ)).2
  let s : R := ∏ Q ∈ others, a Q
  have hsP : s ∉ P := by
    intro hs
    obtain ⟨Q, hQ, haQ⟩ :=
      (Ideal.IsPrime.prod_mem_iff (p := P) (s := others) (x := a)).mp hs
    exact ha_not_mem Q hQ haQ
  refine ⟨s, hsP, ?_⟩
  intro x hx
  rw [← Ideal.sInf_minimalPrimes]
  apply Ideal.mem_sInf.mpr
  intro Q hQ
  by_cases hQP : Q = P
  · subst Q
    exact P.mul_mem_left s hx
  · have hQcomponent : Q ∈ components := by
      exact (mem_finiteMinimalPrimes_iff I Q).mpr hQ
    have hQothers : Q ∈ others := by
      exact Finset.mem_erase.mpr ⟨hQP, hQcomponent⟩
    have haQdiv : a Q ∣ s := by
      exact Finset.dvd_prod_of_mem a hQothers
    obtain ⟨c, hc⟩ := haQdiv
    have hsQ : s ∈ Q := by
      rw [hc]
      simpa [mul_comm] using Q.mul_mem_left c (ha_mem Q hQothers)
    simpa [mul_comm] using Q.mul_mem_left x hsQ

/-- On the principal open supplied above, the reduced equation ideal is
literally the selected irreducible-component ideal.  Thus scheme-theoretic
reduction and component extraction have been carried out together. -/
theorem exists_map_away_radical_eq_minimalComponent
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ∃ s : R, s ∉ P ∧
      Ideal.map (algebraMap R (Localization.Away s)) I.radical =
        Ideal.map (algebraMap R (Localization.Away s)) P := by
  obtain ⟨s, hsP, hclear⟩ := exists_minimalComponent_separator I P hP
  refine ⟨s, hsP, map_away_eq_of_mul_mem I.radical P s ?_ hclear⟩
  exact hP.1.1.radical_le_iff.mpr hP.1.2

/-- In a fixed integral polynomial family, the separating element above is a
fixed polynomial.  Its value at parameters of height at most `H` therefore
has the displayed elementary polynomial bound.  This is the precise sense
in which effectivity of this step is automatic from a uniform algebraic
family construction. -/
theorem exists_minimalComponent_polynomial_separator_with_eval_bound
    {τ : Type*} [Fintype τ]
    (I P : Ideal (MvPolynomial τ ℤ)) (hP : P ∈ I.minimalPrimes) :
    ∃ s : MvPolynomial τ ℤ,
      s ∉ P ∧
      (∀ x ∈ P, s * x ∈ I.radical) ∧
      ∀ (H : ℕ) (t : τ → ℤ),
        (∀ i, (t i).natAbs ≤ H) →
        (MvPolynomial.eval t s).natAbs ≤
          s.support.card *
            (s.support.sup fun m ↦ (s.coeff m).natAbs) *
            max 1 H ^ s.totalDegree := by
  obtain ⟨s, hsP, hclear⟩ := exists_minimalComponent_separator I P hP
  refine ⟨s, hsP, hclear, ?_⟩
  intro H t ht
  exact eval_natAbs_le_support_mul_coeff_mul_pow_generic s t
    (fun m hm ↦ Finset.le_sup (f := fun m ↦ (s.coeff m).natAbs) hm)
    le_rfl ht

/-- Static component-open devissage.  The separator is chosen once for the
component `P`.  Every prime point of that component either lies on the
principal open `D(s)`, or lies on one of the finitely many irreducible
components of the closed boundary `V(P + (s))`; every such boundary
component strictly contains `P`. -/
theorem exists_minimalComponent_open_or_strict_boundary
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) :
    ∃ s : R, s ∉ P ∧
      Ideal.map (algebraMap R (Localization.Away s)) I.radical =
        Ideal.map (algebraMap R (Localization.Away s)) P ∧
      ∀ T : Ideal R, T.IsPrime → P ≤ T →
        s ∉ T ∨
          ∃ L ∈ finiteMinimalPrimes (P ⊔ Ideal.span {s}),
            P < L ∧ L ≤ T := by
  obtain ⟨s, hsP, hmap⟩ :=
    exists_map_away_radical_eq_minimalComponent I P hP
  refine ⟨s, hsP, hmap, ?_⟩
  intro T hT hPT
  by_cases hsT : s ∈ T
  · right
    letI : T.IsPrime := hT
    have hspanT : Ideal.span {s} ≤ T := by
      apply Ideal.span_le.mpr
      simpa using hsT
    obtain ⟨L, hL, hLT⟩ :=
      exists_finiteMinimalPrime_le (I := P ⊔ Ideal.span {s}) (P := T)
        (sup_le hPT hspanT)
    have hsupL : P ⊔ Ideal.span {s} ≤ L :=
      le_of_mem_finiteMinimalPrimes hL
    have hPL : P ≤ L := le_sup_left.trans hsupL
    have hsL : s ∈ L := by
      apply hsupL
      apply (show Ideal.span {s} ≤ P ⊔ Ideal.span {s} from le_sup_right)
      exact Ideal.subset_span (by simp)
    have hPneL : P ≠ L := by
      intro hEq
      apply hsP
      rwa [hEq]
    exact ⟨L, hL, lt_of_le_of_ne hPL hPneL, hLT⟩
  · exact Or.inl hsT

/-- Numerical form of the preceding devissage.  If the selected component
has finite dimension `d`, every irreducible component of its closed boundary
has dimension strictly below `d`. -/
theorem exists_minimalComponent_open_or_lowerDimensional_boundary
    (I P : Ideal R) (hP : P ∈ I.minimalPrimes) {d : ℕ}
    (hPdim : ringKrullDim (R ⧸ P) = d) :
    ∃ s : R, s ∉ P ∧
      Ideal.map (algebraMap R (Localization.Away s)) I.radical =
        Ideal.map (algebraMap R (Localization.Away s)) P ∧
      ∀ T : Ideal R, T.IsPrime → P ≤ T →
        s ∉ T ∨
          ∃ L ∈ finiteMinimalPrimes (P ⊔ Ideal.span {s}),
            P < L ∧ L ≤ T ∧ ringKrullDim (R ⧸ L) < d := by
  obtain ⟨s, hsP, hmap, hpartition⟩ :=
    exists_minimalComponent_open_or_strict_boundary I P hP
  refine ⟨s, hsP, hmap, ?_⟩
  intro T hT hPT
  rcases hpartition T hT hPT with hsT | ⟨L, hL, hPL, hLT⟩
  · exact Or.inl hsT
  · right
    letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
    letI : L.IsPrime := isPrime_of_mem_finiteMinimalPrimes hL
    have hPfinite : ringKrullDim (R ⧸ P) < ⊤ := by
      rw [hPdim]
      change (↑(d : ℕ∞) : WithBot ℕ∞) < ↑(⊤ : ℕ∞)
      exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top d)
    have hdrop := ringKrullDim_quotient_lt_of_prime_lt P L hPL hPfinite
    rw [hPdim] at hdrop
    exact ⟨L, hL, hPL, hLT, hdrop⟩

end

end TranslatedDepthSeven
