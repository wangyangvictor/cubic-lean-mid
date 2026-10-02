import TranslatedDepthSeven.ManuscriptReservoir
import TranslatedDepthSeven.ModulusReservoirGraph

/-!
# The manuscript reservoir stated on the integer moduli

The prime-subset statement in `ManuscriptReservoir` is convenient for the
construction.  This file transports it, without any loss, to the literal
square-free integers obtained by multiplying those primes.  It also records
that deletion by one or two integer certificates gives exactly the coprime
subfamilies of the original reservoir.
-/

namespace TranslatedDepthSeven

open Filter
open scoped Topology

noncomputable section

/-- The members of the reservoir on the allowed primes are exactly the
members of the original reservoir coprime to the certificate. -/
theorem mem_certificateAllowed_modulusReservoir_iff
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {k q : ℕ} (D : ℤ) :
    q ∈ modulusReservoir (certificateAllowedPrimes P D) k ↔
      q ∈ modulusReservoir P k ∧ Nat.Coprime q D.natAbs := by
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hs' := Finset.mem_powersetCard.mp hs
    have hsP : s ⊆ P := fun p hp ↦
      (Finset.mem_filter.mp (hs'.1 hp)).1
    have hcop : Nat.Coprime (primeProduct s) D.natAbs :=
      (subset_certificateAllowedPrimes_iff_coprime hP hsP D).mp hs'.1
    exact ⟨Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hsP, hs'.2⟩, rfl⟩, hcop⟩
  · rintro ⟨hq, hcop⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hs' := Finset.mem_powersetCard.mp hs
    have hsAllowed : s ⊆ certificateAllowedPrimes P D :=
      (subset_certificateAllowedPrimes_iff_coprime hP hs'.1 D).mpr hcop
    exact Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hsAllowed, hs'.2⟩, rfl⟩

/-- The corresponding exact description after deleting the prime divisors
of two certificates. -/
theorem mem_certificateAllowedTwo_modulusReservoir_iff
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {k q : ℕ} (D₁ D₂ : ℤ) :
    q ∈ modulusReservoir (certificateAllowedPrimesTwo P D₁ D₂) k ↔
      q ∈ modulusReservoir P k ∧ Nat.Coprime q D₁.natAbs ∧
        Nat.Coprime q D₂.natAbs := by
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hs' := Finset.mem_powersetCard.mp hs
    have hsP : s ⊆ P := fun p hp ↦
      (Finset.mem_filter.mp (hs'.1 hp)).1
    have hcop := (subset_certificateAllowedPrimesTwo_iff_coprime
      hP hsP D₁ D₂).mp hs'.1
    exact ⟨Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hsP, hs'.2⟩, rfl⟩,
      hcop.1, hcop.2⟩
  · rintro ⟨hq, hcop₁, hcop₂⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hs' := Finset.mem_powersetCard.mp hs
    have hsAllowed : s ⊆ certificateAllowedPrimesTwo P D₁ D₂ :=
      (subset_certificateAllowedPrimesTwo_iff_coprime
        hP hs'.1 D₁ D₂).mpr ⟨hcop₁, hcop₂⟩
    exact Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hsAllowed, hs'.2⟩, rfl⟩

/-- The same surviving family written in the manuscript's single-product
form. -/
theorem mem_certificateAllowedTwo_modulusReservoir_iff_coprime_mul
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {k q : ℕ} (D₁ D₂ : ℤ) :
    q ∈ modulusReservoir (certificateAllowedPrimesTwo P D₁ D₂) k ↔
      q ∈ modulusReservoir P k ∧
        Nat.Coprime q (D₁ * D₂).natAbs := by
  rw [mem_certificateAllowedTwo_modulusReservoir_iff hP D₁ D₂,
    ← coprime_two_natAbs_iff_coprime_mul]

/-- The count of directed one-exchange pairs is unchanged when prime subsets
are replaced by their integer products. -/
theorem card_modulusReservoirDirectedEdges_eq
    (P : Finset ℕ) (k : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (modulusReservoirDirectedEdges P k hP).card =
      (reservoirDirectedEdges P k).card := by
  classical
  let f : ReservoirModulus P k × ReservoirModulus P k →
      Finset ℕ × Finset ℕ := fun qr ↦
    (qr.1.1.primeFactors, qr.2.1.primeFactors)
  apply Finset.card_bij (s := modulusReservoirDirectedEdges P k hP)
    (t := reservoirDirectedEdges P k) (fun qr _ ↦ f qr)
  · intro qr hqr
    have hadj : OneExchange qr.1.1.primeFactors qr.2.1.primeFactors :=
      (Finset.mem_filter.mp hqr).2
    have hq := primeFactors_spec_of_mem_modulusReservoir hP qr.1.2
    have hr := primeFactors_spec_of_mem_modulusReservoir hP qr.2.2
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_product.mpr ⟨
        Finset.mem_powersetCard.mpr ⟨hq.1, hq.2.1⟩,
        Finset.mem_powersetCard.mpr ⟨hr.1, hr.2.1⟩⟩,
      hadj⟩
  · intro q₁ hq₁ q₂ hq₂ heq
    apply Prod.ext
    · apply Subtype.ext
      calc
        q₁.1.1 = primeProduct q₁.1.1.primeFactors :=
          (primeFactors_spec_of_mem_modulusReservoir hP q₁.1.2).2.2.symm
        _ = primeProduct q₂.1.1.primeFactors :=
          congrArg primeProduct (congrArg Prod.fst heq)
        _ = q₂.1.1 :=
          (primeFactors_spec_of_mem_modulusReservoir hP q₂.1.2).2.2
    · apply Subtype.ext
      calc
        q₁.2.1 = primeProduct q₁.2.1.primeFactors :=
          (primeFactors_spec_of_mem_modulusReservoir hP q₁.2.2).2.2.symm
        _ = primeProduct q₂.2.1.primeFactors :=
          congrArg primeProduct (congrArg Prod.snd heq)
        _ = q₂.2.1 :=
          (primeFactors_spec_of_mem_modulusReservoir hP q₂.2.2).2.2
  · intro st hst
    have hst' := Finset.mem_filter.mp hst
    have hs := Finset.mem_product.mp hst'.1
    let q : ReservoirModulus P k :=
      ⟨primeProduct st.1, Finset.mem_image.mpr ⟨st.1, hs.1, rfl⟩⟩
    let r : ReservoirModulus P k :=
      ⟨primeProduct st.2, Finset.mem_image.mpr ⟨st.2, hs.2, rfl⟩⟩
    refine ⟨(q, r), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        change OneExchange (primeProduct st.1).primeFactors
          (primeProduct st.2).primeFactors
        rw [primeFactors_primeProduct
            (fun p hp ↦ hP p ((Finset.mem_powersetCard.mp hs.1).1 hp)),
          primeFactors_primeProduct
            (fun p hp ↦ hP p ((Finset.mem_powersetCard.mp hs.2).1 hp))]
        exact hst'.2⟩
    · change ((primeProduct st.1).primeFactors,
        (primeProduct st.2).primeFactors) = st
      rw [primeFactors_primeProduct
          (fun p hp ↦ hP p ((Finset.mem_powersetCard.mp hs.1).1 hp)),
        primeFactors_primeProduct
          (fun p hp ↦ hP p ((Finset.mem_powersetCard.mp hs.2).1 hp))]

/-- The complete canonical manuscript reservoir, now stated on the literal
integer moduli.  The choices of `P` and `k` are the canonical choices from
`ManuscriptReservoir` and hence do not depend on `ε`.  The final two clauses
identify deletion by one or two certificates with the corresponding coprime
subfamilies and assert connectedness of their literal modulus graphs. -/
theorem eventually_exists_manuscriptModulusReservoir
    {A a Cres ε : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (haOne : a < 1)
    (hCres : 1 < Cres) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ H →
      ∃ (P : Finset ℕ) (k : ℕ) (hPprime : ∀ p ∈ P, p.Prime),
        P = manuscriptPrimePoolAt A a H ∧
        k = manuscriptCrossingAt A a Cres H T ∧
        P.card = reservoirDepth (manuscriptPoolDepthCoefficient A a) H ∧
        (∀ p ∈ P,
          ⌊manuscriptPrimeIntervalCoefficient A a * Real.log H⌋₊ < p ∧
            p ≤ ⌊2 * (manuscriptPrimeIntervalCoefficient A a *
              Real.log H)⌋₊) ∧
        k ≤ P.card ∧
        (∀ q : ReservoirModulus P k,
          Squarefree q.1 ∧
            Cres * T ^ a ≤ (q.1 : ℝ) ∧
            (q.1 : ℝ) ≤
              (4 * manuscriptPrimeIntervalCoefficient A a * (ε / 3)⁻¹) *
                Cres * T ^ a * H ^ ε) ∧
        (modulusReservoirGraph P k hPprime).Connected ∧
        ((((modulusReservoir P k).card +
            (modulusReservoirDirectedEdges P k hPprime).card : ℕ) : ℝ) ≤
          2 * H ^ ε) ∧
        (∀ q r : ReservoirModulus P k,
          (modulusReservoirGraph P k hPprime).Adj q r →
            Cres * T ^ a ≤ (Nat.lcm q.1 r.1 : ℝ) ∧
            (Nat.lcm q.1 r.1 : ℝ) ≤
              (16 * (manuscriptPrimeIntervalCoefficient A a) ^ 2 *
                ((ε / 3)⁻¹) ^ 2) * Cres * T ^ a * H ^ ε) ∧
        (∀ D : ℤ, D ≠ 0 → (D.natAbs : ℝ) ≤ H ^ A →
          (∀ q : ℕ,
            q ∈ modulusReservoir (certificateAllowedPrimes P D) k ↔
              q ∈ modulusReservoir P k ∧ Nat.Coprime q D.natAbs) ∧
          Nonempty (ReservoirModulus (certificateAllowedPrimes P D) k) ∧
          (modulusReservoirGraph (certificateAllowedPrimes P D) k
            (fun p hp ↦ hPprime p (Finset.mem_filter.mp hp).1)).Connected) ∧
        (∀ D₁ D₂ : ℤ, D₁ ≠ 0 → D₂ ≠ 0 →
          (D₁.natAbs : ℝ) ≤ H ^ A → (D₂.natAbs : ℝ) ≤ H ^ A →
          (∀ q : ℕ,
            q ∈ modulusReservoir
                (certificateAllowedPrimesTwo P D₁ D₂) k ↔
              q ∈ modulusReservoir P k ∧
                Nat.Coprime q (D₁ * D₂).natAbs) ∧
          Nonempty (ReservoirModulus
            (certificateAllowedPrimesTwo P D₁ D₂) k) ∧
          (modulusReservoirGraph
            (certificateAllowedPrimesTwo P D₁ D₂) k
            (fun p hp ↦ hPprime p (Finset.mem_filter.mp hp).1)).Connected) := by
  filter_upwards [eventually_exists_manuscriptReservoir
    hA ha haOne hCres hε] with H hH
  intro T hT hTH
  obtain ⟨P, k, hPcanonical, hkcanonical, hPcard, hPdata, hkP,
    hmoduli, hfamily, hlcm, hcertOne, hcertTwo⟩ := hH T hT hTH
  let hPprime : ∀ p ∈ P, p.Prime := fun p hp ↦ (hPdata p hp).1
  refine ⟨P, k, hPprime, hPcanonical, hkcanonical, hPcard, ?_, hkP,
    ?_, modulusReservoirGraph_connected hPprime hkP, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hPdata p hp).2
  · intro q
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp q.2
    have h := hmoduli s hs
    simpa only [hsq] using h
  · rw [card_modulusReservoir_of_primes hPprime k,
      card_modulusReservoirDirectedEdges_eq P k hPprime]
    simpa only [Finset.card_powersetCard] using hfamily
  · intro q r hqr
    have hq := primeFactors_spec_of_mem_modulusReservoir hPprime q.2
    have hr := primeFactors_spec_of_mem_modulusReservoir hPprime r.2
    have hqmem : q.1.primeFactors ∈ P.powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨hq.1, hq.2.1⟩
    have hrmem : r.1.primeFactors ∈ P.powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨hr.1, hr.2.1⟩
    have h := hlcm q.1.primeFactors hqmem r.1.primeFactors hrmem hqr
    simpa only [hq.2.2, hr.2.2] using h
  · intro D hD hDsize
    obtain ⟨-, hnonempty, -⟩ := hcertOne D hD hDsize
    let hAllowedPrime : ∀ p ∈ certificateAllowedPrimes P D, p.Prime :=
      fun p hp ↦ hPprime p (Finset.mem_filter.mp hp).1
    obtain ⟨s⟩ := hnonempty
    have hkAllowed : k ≤ (certificateAllowedPrimes P D).card := by
      calc
        k = s.1.card := s.2.2.symm
        _ ≤ (certificateAllowedPrimes P D).card :=
          Finset.card_le_card s.2.1
    refine ⟨fun q ↦ mem_certificateAllowed_modulusReservoir_iff
      hPprime D, ?_, ?_⟩
    · exact ⟨(reservoirVertexModulusEquiv
        (certificateAllowedPrimes P D) k hAllowedPrime) s⟩
    · exact modulusReservoirGraph_connected hAllowedPrime hkAllowed
  · intro D₁ D₂ hD₁ hD₂ hDsize₁ hDsize₂
    obtain ⟨-, hnonempty, -⟩ :=
      hcertTwo D₁ D₂ hD₁ hD₂ hDsize₁ hDsize₂
    let hAllowedPrime :
        ∀ p ∈ certificateAllowedPrimesTwo P D₁ D₂, p.Prime :=
      fun p hp ↦ hPprime p (Finset.mem_filter.mp hp).1
    obtain ⟨s⟩ := hnonempty
    have hkAllowed : k ≤
        (certificateAllowedPrimesTwo P D₁ D₂).card := by
      calc
        k = s.1.card := s.2.2.symm
        _ ≤ (certificateAllowedPrimesTwo P D₁ D₂).card :=
          Finset.card_le_card s.2.1
    refine ⟨fun q ↦ mem_certificateAllowedTwo_modulusReservoir_iff_coprime_mul
      hPprime D₁ D₂, ?_, ?_⟩
    · exact ⟨(reservoirVertexModulusEquiv
        (certificateAllowedPrimesTwo P D₁ D₂) k hAllowedPrime) s⟩
    · exact modulusReservoirGraph_connected hAllowedPrime hkAllowed

end

end TranslatedDepthSeven
