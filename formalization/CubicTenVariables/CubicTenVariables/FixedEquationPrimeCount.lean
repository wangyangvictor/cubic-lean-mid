import CubicTenVariables.FixedEquationNormalization
import CubicTenVariables.LocalizedIntegerExceptionalSet
import CubicTenVariables.IntegralEquationCounts

/-! Uniform all-prime counting for the actual reductions of a fixed
integral equation family. The rational quotient dimension is the only
dimension input; normalization, all exceptional primes, and reindexing
are handled internally. -/

noncomputable section
namespace CubicTenVariables.FixedEquationPrimeCount
open MvPolynomial IntegralEquationCounts

/-- The constant precedes every prime, including exceptional primes.
The counted points are all solutions of the original reduced equations. -/
theorem exists_uniform_fin_bound {N t r : ℕ}
    (f : Fin t → MvPolynomial (Fin N) ℤ)
    (hproper : FixedEquationNormalization.equationIdeal f ℚ ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℚ ⧸
      FixedEquationNormalization.equationIdeal f ℚ) ≤ (r : WithBot ℕ∞)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → zeroCount f p ≤ C*p^r := by
  obtain ⟨Δ, hΔ, δ, hδ, C, _hC, hcount⟩ :=
    FixedEquationNormalization.exists_specialization_bound f hproper hdim
  obtain ⟨D, hD, _hΔD, hunit⟩ :=
    LocalizedIntegerExceptionalSet.exists_exceptionalInteger Δ hΔ δ hδ
  apply exists_all_prime_bound_of_good_prime_bound f r C D hD
  intro p hp hpD
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpΔ, hu⟩ := hunit p hp hpD
  simpa only [zeroCount, Nat.card_zmod] using
    hcount (ZMod p) (TranslatedDepthSeven.awayIntToZMod Δ p hp hpΔ) hu

/-- The same theorem for any finite variable type, in particular the
native paired-coordinate incidence variables. No point-count premise,
model-identification premise, or excluded-prime hypothesis remains. -/
theorem exists_uniform_bound {σ : Type*} [Fintype σ] {t r : ℕ}
    (f : Fin t → MvPolynomial σ ℤ)
    (hproper : Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (f i))) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial σ ℚ ⧸
      Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (f i)))) ≤
        (r : WithBot ℕ∞)) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ p : ℕ, p.Prime → zeroCount f p ≤ C*p^r := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let g : Fin t → MvPolynomial (Fin (Fintype.card σ)) ℤ :=
    fun i => rename e (f i)
  have hg : FixedEquationNormalization.equationIdeal g ℚ =
      Ideal.span (Set.range (fun i => rename e (map (Int.castRingHom ℚ) (f i)))) := by
    change Ideal.span (Set.range (fun i => map (Int.castRingHom ℚ) (rename e (f i)))) = _
    simp only [map_rename]
  have hp : FixedEquationNormalization.equationIdeal g ℚ ≠ ⊤ := by
    rw [hg]
    exact FiniteVariableEquations.span_rename_ne_top e _ hproper
  have hd : ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) ℚ ⧸
      FixedEquationNormalization.equationIdeal g ℚ) ≤ (r : WithBot ℕ∞) := by
    rw [hg, FiniteVariableEquations.quotient_dimension_rename]
    exact hdim
  obtain ⟨C, hC, hc⟩ := exists_uniform_fin_bound g hp hd
  refine ⟨C, hC, ?_⟩
  intro p hp
  rw [zeroCount_rename e f p]
  exact hc p hp

end CubicTenVariables.FixedEquationPrimeCount
