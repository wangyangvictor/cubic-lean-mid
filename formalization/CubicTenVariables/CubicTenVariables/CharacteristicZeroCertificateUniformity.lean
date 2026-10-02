import TranslatedDepthSeven.FinitePrincipalOpenDevissage
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! Uniform polynomial certificates from characteristic-zero parameter strata.

The geometric dense-open certificate is an explicit premise, required on
every prime stratum of characteristic zero. Noetherian induction covers
the exceptional parameter loci too. Vertical strata contribute a positive
integer to invert. The conclusion places one exceptional integer and one
degree bound before every field and every parameter specialization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical

namespace CubicTenVariables.CharacteristicZeroCertificateUniformity
open MvPolynomial TranslatedDepthSeven

variable {R : Type} [CommRing R] {m : ℕ}

/-- An actual nonzero parameter polynomial certifying a property of tuples. -/
def HasCertificate
    (Good : ∀ (K : Type) [Field K], (R →+* K) → (Fin m → K) → Prop)
    (D : ℕ) {K : Type} [Field K] (ρ : R →+* K) : Prop :=
  ∃ Δ : MvPolynomial (Fin m) K, Δ ≠ 0 ∧ Δ.totalDegree ≤ D ∧
    ∀ γ : Fin m → K, eval γ Δ ≠ 0 → Good K ρ γ

theorem HasCertificate.mono
    {Good : ∀ (K : Type) [Field K], (R →+* K) → (Fin m → K) → Prop}
    {D D' : ℕ} {K : Type} [Field K] {ρ : R →+* K}
    (h : HasCertificate Good D ρ) (hDD' : D ≤ D') : HasCertificate Good D' ρ := by
  obtain ⟨Δ, hΔ, hdeg, hgood⟩ := h
  exact ⟨Δ, hΔ, hdeg.trans hDD', hgood⟩

private structure CertificateSize where
  excluded : ℕ
  positive : 0 < excluded
  degree : ℕ

private def ValidAtPrime
    (Eligible : ∀ (K : Type) [Field K], (R →+* K) → Prop)
    (Good : ∀ (K : Type) [Field K], (R →+* K) → (Fin m → K) → Prop)
    (size : CertificateSize) (P : Ideal R) : Prop :=
  ∀ (K : Type) [Field K] (ρ : R →+* K), RingHom.ker ρ = P →
    (size.excluded : K) ≠ 0 → Eligible K ρ → HasCertificate Good size.degree ρ

/-- Dense-open certificates on all characteristic-zero prime strata give
one degree bound after inverting one positive integer. The hypotheses on
an eligible fiber remain explicit; no uniformity in an omitted parameter
is inferred from the generic stratum alone. -/
theorem exists_uniform_degree_away_from_integer [IsNoetherianRing R]
    (Eligible : ∀ (K : Type) [Field K], (R →+* K) → Prop)
    (Good : ∀ (K : Type) [Field K], (R →+* K) → (Fin m → K) → Prop)
    (hopen : ∀ P : Ideal R, P.IsPrime →
      (∀ n : ℕ, 0 < n → (n : R) ∉ P) →
      ∃ s : R, s ∉ P ∧ ∃ D : ℕ,
        ∀ (K : Type) [Field K] (ρ : R →+* K),
          P ≤ RingHom.ker ρ → ρ s ≠ 0 → Eligible K ρ → HasCertificate Good D ρ) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      ∀ (K : Type) [Field K] (ρ : R →+* K),
        (N : K) ≠ 0 → Eligible K ρ → HasCertificate Good D ρ := by
  classical
  have hg : PrimeStratumGenericPrincipalOpenData (ValidAtPrime Eligible Good) := by
    intro P hP
    by_cases hzero : ∀ n : ℕ, 0 < n → (n : R) ∉ P
    · obtain ⟨s, hs, D, hD⟩ := hopen P hP hzero
      let size : CertificateSize := ⟨1, by decide, D⟩
      refine ⟨s, hs, [size], ?_⟩
      intro T _hT hPT hsT
      refine ⟨size, by simp, ?_⟩
      intro K _ ρ hker _hN he
      apply hD K ρ (hker ▸ hPT) _ he
      intro hz
      exact hsT (hker ▸ RingHom.mem_ker.mpr hz)
    · push_neg at hzero
      obtain ⟨n, hn, hnP⟩ := hzero
      let size : CertificateSize := ⟨n, hn, 0⟩
      refine ⟨1, hP.one_notMem, [size], ?_⟩
      intro T _hT hPT _h1
      refine ⟨size, by simp, ?_⟩
      intro K _ ρ hker hN _he
      have hnker : (n : R) ∈ RingHom.ker ρ := hker ▸ hPT hnP
      have hnzero : (n : K) = 0 := by
        simpa only [map_natCast] using RingHom.mem_ker.mp hnker
      exact (hN hnzero).elim
  obtain ⟨charts, _hstructure, hcover⟩ :=
    exists_finitePrincipalOpenStratifiedCover_of_primeGenericData
      (ValidAtPrime Eligible Good) hg (⊥ : Ideal R)
  let N := ∏ chart ∈ charts.toFinset, chart.payload.excluded
  let D := ∑ chart ∈ charts.toFinset, chart.payload.degree
  refine ⟨N, Finset.prod_pos (fun chart _ ↦ chart.payload.positive), D, ?_⟩
  intro K _ ρ hN he
  obtain ⟨chart, hchart, _hcovers, hvalid⟩ :=
    hcover (RingHom.ker ρ) (RingHom.ker_isPrime ρ) bot_le
  have hc : chart ∈ charts.toFinset := List.mem_toFinset.mpr hchart
  have hproduct : (∏ c ∈ charts.toFinset, (c.payload.excluded : K)) ≠ 0 := by
    simpa only [N, Nat.cast_prod] using hN
  have hlocal : (chart.payload.excluded : K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hproduct chart hc
  have hdegree : chart.payload.degree ≤ D :=
    Finset.single_le_sum (f := fun c ↦ c.payload.degree) (fun _ _ ↦ Nat.zero_le _) hc
  exact (hvalid K ρ rfl hlocal he).mono hdegree

end CubicTenVariables.CharacteristicZeroCertificateUniformity
