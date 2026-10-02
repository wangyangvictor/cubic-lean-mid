import TranslatedDepthSeven.FinitePrimeStratumGenericComponentCover
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.KrullDimension.Basic

/-! Numerical bounds assembled by the existing finite principal-open
Noetherian devissage. The dense-open bounds are explicit arguments to these
assembly lemmas; later component normalization supplies them. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.NoetherianPrimeFieldBound
open TranslatedDepthSeven MvPolynomial
open scoped BigOperators Classical

/-- The literal field-valued zero set of the fixed equation ideal. -/
def zeroSet {R : Type} [CommRing R] {N p : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R)) (ρ : R →+* ZMod p) :=
  {x : Fin N → ZMod p // ∀ f ∈ I, MvPolynomial.eval₂Hom ρ x f = 0}

/-- Uniformity at one parameter prime; the constant precedes the prime
field, parameter homomorphism and dimension threshold. -/
def BoundAtPrime {R : Type} [CommRing R] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R)) (C : ℕ) (T : Ideal R) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ρ : R →+* ZMod p), RingHom.ker ρ = T →
    ∀ j : ℕ,
      ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
        (j : WithBot ℕ∞) → Nat.card (zeroSet I ρ) ≤ C * p^j

/-- A genuine dense-open bound on each prime parameter stratum gives one
constant valid on every parameter specialization. The finite exceptional
strata and their constants are constructed by Noetherian induction. -/
theorem exists_uniform_of_prime_open
    {R : Type} [CommRing R] [IsNoetherianRing R] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R))
    (hopen : ∀ (P : Ideal R), P.IsPrime →
      ∃ s : R, s ∉ P ∧ ∃ C : ℕ, 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] (ρ : R →+* ZMod p),
          P ≤ RingHom.ker ρ → ρ s ≠ 0 → ∀ j : ℕ,
          ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
            (j : WithBot ℕ∞) → Nat.card (zeroSet I ρ) ≤ C * p^j) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (ρ : R →+* ZMod p) (j : ℕ),
      ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
        (j : WithBot ℕ∞) → Nat.card (zeroSet I ρ) ≤ C * p^j := by
  classical
  have hg : PrimeStratumGenericPrincipalOpenData (BoundAtPrime I) := by
    intro P hP
    obtain ⟨s, hs, C, _hC, hbound⟩ := hopen P hP
    refine ⟨s, hs, [C], ?_⟩
    intro T _hT hPT hsT
    refine ⟨C, by simp, ?_⟩
    intro p _ ρ hker j hdim
    apply hbound p ρ (hker ▸ hPT) _ j hdim
    intro hz
    exact hsT (hker ▸ (RingHom.mem_ker.mpr hz))
  obtain ⟨charts, _, hcover⟩ :=
    exists_finitePrincipalOpenStratifiedCover_of_primeGenericData
      (BoundAtPrime I) hg (⊥ : Ideal R)
  let C := 1 + ∑ chart ∈ charts.toFinset, chart.payload
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro p _ ρ j hdim
  obtain ⟨chart, hchart, _, hbound⟩ :=
    hcover (RingHom.ker ρ) (RingHom.ker_isPrime ρ) bot_le
  have hc : chart.payload ≤ C := by
    have hh := Finset.single_le_sum (s := charts.toFinset)
      (f := fun c => c.payload) (fun _ _ => Nat.zero_le _)
      (List.mem_toFinset.mpr hchart)
    change chart.payload ≤ ∑ c ∈ charts.toFinset, c.payload at hh
    exact hh.trans (Nat.le_add_left _ _)
  exact (hbound p ρ rfl j hdim).trans (Nat.mul_le_mul_right (p^j) hc)

/-- Quotient parameter specialization does not change the actual zero set. -/
theorem natCard_zeroSet_map
    {R S : Type} [CommRing R] [CommRing S] {N p : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R)) (q : R →+* S)
    (ρ : S →+* ZMod p) :
    Nat.card (zeroSet (I.map (MvPolynomial.map q)) ρ) =
      Nat.card (zeroSet I (ρ.comp q)) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun x => (vanishes_map_iff q ρ x I).symm

/-- It suffices to prove a dense-open bound over each integral quotient of
the parameter ring. Quotient specialization preserves the literal equations
and their dimension, so all closed exceptional strata are included. -/
theorem exists_uniform_of_quotient_open
    {R : Type} [CommRing R] [IsNoetherianRing R] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) R))
    (hopen : ∀ (P : Ideal R) [P.IsPrime],
      ∃ s : R ⧸ P, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] (ρ : (R ⧸ P) →+* ZMod p), ρ s ≠ 0 → ∀ j : ℕ,
          ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸
            (I.map (MvPolynomial.map (Ideal.Quotient.mk P))).map (MvPolynomial.map ρ)) ≤
            (j : WithBot ℕ∞) →
          Nat.card (zeroSet (I.map (MvPolynomial.map (Ideal.Quotient.mk P))) ρ) ≤ C * p^j) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] (ρ : R →+* ZMod p) (j : ℕ),
      ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
        (j : WithBot ℕ∞) → Nat.card (zeroSet I ρ) ≤ C * p^j := by
  apply exists_uniform_of_prime_open I
  intro P hP
  letI : P.IsPrime := hP
  obtain ⟨s, hs, C, hC, hbound⟩ := hopen P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective s
  refine ⟨a, ?_, C, hC, ?_⟩
  · intro haP
    exact hs (ha.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr haP))
  · intro p _ ρ hPρ haρ j hdim
    let barρ : R ⧸ P →+* ZMod p :=
      Ideal.Quotient.lift P ρ (fun _ hx => RingHom.mem_ker.mp (hPρ hx))
    have hcomp : barρ.comp (Ideal.Quotient.mk P) = ρ :=
      Ideal.Quotient.lift_comp_mk P ρ _
    have hsρ : barρ s ≠ 0 := by
      rw [← ha]
      exact haρ
    have hmaps : (MvPolynomial.map barρ).comp (MvPolynomial.map (Ideal.Quotient.mk P)) =
        (MvPolynomial.map ρ : MvPolynomial (Fin N) R →+* _) := by
      apply RingHom.ext
      intro f
      change MvPolynomial.map barρ (MvPolynomial.map (Ideal.Quotient.mk P) f) = _
      rw [MvPolynomial.map_map, hcomp]
    have heq : (I.map (MvPolynomial.map (Ideal.Quotient.mk P))).map (MvPolynomial.map barρ) =
        I.map (MvPolynomial.map ρ) := by
      rw [Ideal.map_map, hmaps]
    have hd := (ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq heq)).trans_le hdim
    have hc := hbound p barρ hsρ j hd
    rw [natCard_zeroSet_map, hcomp] at hc
    exact hc

/-- Bounds on the finitely many generic components combine on one dense
base open. The original zero locus is covered by their actual contractions;
no reducedness or equidimensionality assertion is used. -/
theorem exists_dense_open_of_component_bounds
    {B K : Type} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Field K] [Algebra B K] [IsFractionRing B K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) B))
    (hcomponent : ∀ Q ∈ (I.map (MvPolynomial.map (algebraMap B K))).minimalPrimes,
      ∃ s : B, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] (ρ : B →+* ZMod p), ρ s ≠ 0 → ∀ j : ℕ,
          ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
            (j : WithBot ℕ∞) →
          Nat.card (zeroSet (Q.comap (MvPolynomial.map (algebraMap B K))) ρ) ≤ C * p^j) :
    ∃ s : B, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime] (ρ : B →+* ZMod p), ρ s ≠ 0 → ∀ j : ℕ,
        ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
          (j : WithBot ℕ∞) → Nat.card (zeroSet I ρ) ≤ C * p^j := by
  classical
  let components := finiteMinimalPrimes (I.map (MvPolynomial.map (algebraMap B K)))
  have hb : ∀ Q : {Q // Q ∈ components},
      ∃ s : B, s ≠ 0 ∧ ∃ C : ℕ, 1 ≤ C ∧
        ∀ (p : ℕ) [Fact p.Prime] (ρ : B →+* ZMod p), ρ s ≠ 0 → ∀ j : ℕ,
          ringKrullDim (MvPolynomial (Fin N) (ZMod p) ⧸ I.map (MvPolynomial.map ρ)) ≤
            (j : WithBot ℕ∞) →
          Nat.card (zeroSet (Q.val.comap (MvPolynomial.map (algebraMap B K))) ρ) ≤ C * p^j := by
    intro Q
    exact hcomponent Q ((mem_finiteMinimalPrimes_iff _ _).mp Q.property)
  choose s hs C _hC hcount using hb
  obtain ⟨s₀, hs₀, hcover⟩ :=
    exists_nonzero_base_open_fieldPoint_zeroLocus_cover (K := K) I
  refine ⟨s₀ * ∏ Q, s Q, mul_ne_zero hs₀ (Finset.prod_ne_zero_iff.mpr (fun Q _ => hs Q)),
    1 + ∑ Q, C Q, by omega, ?_⟩
  intro p _ ρ hsρ j hdim
  have hprod : ρ s₀ ≠ 0 ∧ ∏ Q, ρ (s Q) ≠ 0 := by
    simpa only [map_mul, map_prod, mul_ne_zero_iff] using hsρ
  have hsi : ∀ Q, ρ (s Q) ≠ 0 :=
    fun Q => Finset.prod_ne_zero_iff.mp hprod.2 Q (Finset.mem_univ Q)
  let points : {Q // Q ∈ components} → Finset (Fin N → ZMod p) :=
    fun Q => Finset.univ.filter (fun x =>
      ∀ f ∈ Q.val.comap (MvPolynomial.map (algebraMap B K)), MvPolynomial.eval₂Hom ρ x f = 0)
  let original : Finset (Fin N → ZMod p) :=
    Finset.univ.filter (fun x => ∀ f ∈ I, MvPolynomial.eval₂Hom ρ x f = 0)
  have hsub : original ⊆ Finset.univ.biUnion points := by
    intro x hx
    have hzero := (Finset.mem_filter.mp hx).2
    obtain ⟨Q, hQ, hz⟩ := (hcover ρ x hprod.1).mp hzero
    exact Finset.mem_biUnion.mpr ⟨⟨Q, hQ⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
  have hpoint : ∀ Q, (points Q).card ≤ C Q * p^j := by
    intro Q
    have hc := hcount Q p ρ (hsi Q) j hdim
    simpa only [points, zeroSet, Nat.card_eq_fintype_card, Fintype.card_subtype] using hc
  have hcard : Nat.card (zeroSet I ρ) = original.card := by
    simp only [zeroSet, original, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  calc
    original.card ≤ (Finset.univ.biUnion points).card := Finset.card_le_card hsub
    _ ≤ ∑ Q, (points Q).card := Finset.card_biUnion_le
    _ ≤ ∑ Q, C Q * p^j := Finset.sum_le_sum (fun Q _ => hpoint Q)
    _ = (∑ Q, C Q) * p^j := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 + ∑ Q, C Q) * p^j := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

end CubicTenVariables.NoetherianPrimeFieldBound
