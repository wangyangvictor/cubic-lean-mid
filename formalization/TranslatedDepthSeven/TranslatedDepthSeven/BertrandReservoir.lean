import Mathlib

/-!
# A finite square-free prime reservoir from Bertrand's postulate

This file contains only elementary arithmetic and finite-set combinatorics.
In particular, no prime-number theorem is used.  Starting from a positive
integer `R`, Bertrand's postulate supplies one prime in each of the disjoint
dyadic intervals

`(R * 2^j, R * 2^(j+1)]`.

Products of fixed-cardinality subsets of these primes form a finite reservoir
of square-free moduli.  The lemmas below record injectivity of the product,
exact least-common-multiple formulae, uniform product bounds, and the elementary
one-prime-exchange property of the fixed-cardinality subsets.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The integer auxiliary scale attached to a manuscript height `mathcalH`
and a real loss exponent `δ`.  This is deliberately distinct from the
manuscript height itself. -/
def realAuxiliaryHeight (mathcalH δ : ℝ) : ℕ := ⌈mathcalH ^ δ⌉₊

theorem rpow_le_realAuxiliaryHeight (mathcalH δ : ℝ) :
    mathcalH ^ δ ≤ (realAuxiliaryHeight mathcalH δ : ℝ) := by
  exact Nat.le_ceil _

theorem realAuxiliaryHeight_lt_add_one {mathcalH δ : ℝ}
    (hmathcalH : 0 ≤ mathcalH) :
    (realAuxiliaryHeight mathcalH δ : ℝ) < mathcalH ^ δ + 1 := by
  exact Nat.ceil_lt_add_one (Real.rpow_nonneg hmathcalH _)

theorem realAuxiliaryHeight_pos {mathcalH δ : ℝ}
    (hmathcalH : 0 < mathcalH) : 0 < realAuxiliaryHeight mathcalH δ := by
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hmathcalH δ)

theorem nat_le_realAuxiliaryHeight {mathcalH δ : ℝ} {C : ℕ}
    (hC : (C : ℝ) ≤ mathcalH ^ δ) :
    C ≤ realAuxiliaryHeight mathcalH δ := by
  exact_mod_cast hC.trans (rpow_le_realAuxiliaryHeight mathcalH δ)

/-- Convert a real height inequality into the exact natural-power inequality
needed to choose the crossing cardinality. -/
theorem nat_le_realAuxiliaryHeight_pow {mathcalH δ : ℝ}
    (hmathcalH : 0 ≤ mathcalH) {Q K : ℕ}
    (hQ : (Q : ℝ) ≤ mathcalH ^ (δ * (K : ℝ))) :
    Q ≤ (realAuxiliaryHeight mathcalH δ) ^ K := by
  have hbase := rpow_le_realAuxiliaryHeight mathcalH δ
  have hp : (mathcalH ^ δ) ^ K ≤
      ((realAuxiliaryHeight mathcalH δ : ℕ) : ℝ) ^ K := by
    gcongr
  have hQ' : (Q : ℝ) ≤ (mathcalH ^ δ) ^ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmathcalH]
    exact hQ
  exact_mod_cast hQ'.trans hp

/-- The strict version used for the sizes of integer certificates. -/
theorem nat_lt_realAuxiliaryHeight_pow {mathcalH δ : ℝ}
    (hmathcalH : 0 ≤ mathcalH) {D b : ℕ}
    (hD : (D : ℝ) < mathcalH ^ (δ * (b : ℝ))) :
    D < (realAuxiliaryHeight mathcalH δ) ^ b := by
  have hbase := rpow_le_realAuxiliaryHeight mathcalH δ
  have hp : (mathcalH ^ δ) ^ b ≤
      ((realAuxiliaryHeight mathcalH δ : ℕ) : ℝ) ^ b := by
    gcongr
  have hD' : (D : ℝ) < (mathcalH ^ δ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmathcalH]
    exact hD
  exact_mod_cast hD'.trans_le hp

theorem realAuxiliaryHeight_cast_le_two_rpow {mathcalH δ : ℝ}
    (hmathcalH : 1 ≤ mathcalH) (hδ : 0 ≤ δ) :
    (realAuxiliaryHeight mathcalH δ : ℝ) ≤ 2 * mathcalH ^ δ := by
  have hone : 1 ≤ mathcalH ^ δ := Real.one_le_rpow hmathcalH hδ
  exact (realAuxiliaryHeight_lt_add_one (zero_le_one.trans hmathcalH)).le.trans <| by
    linarith

/-- A canonical choice of a Bertrand prime.  At `N = 0` we put the value equal
to `2`; every theorem below uses the positive case. -/
def bertrandPrime (N : ℕ) : ℕ :=
  if hN : N = 0 then 2 else Classical.choose (Nat.bertrand N hN)

theorem bertrandPrime_spec {N : ℕ} (hN : 0 < N) :
    (bertrandPrime N).Prime ∧ N < bertrandPrime N ∧ bertrandPrime N ≤ 2 * N := by
  rw [bertrandPrime, dif_neg hN.ne']
  exact Classical.choose_spec (Nat.bertrand N hN.ne')

/-- The prime selected from `(R * 2^j, R * 2^(j+1)]`. -/
def dyadicPrime (R j : ℕ) : ℕ := bertrandPrime (R * 2 ^ j)

theorem dyadicPrime_spec {R j : ℕ} (hR : 0 < R) :
    (dyadicPrime R j).Prime ∧
      R * 2 ^ j < dyadicPrime R j ∧
      dyadicPrime R j ≤ R * 2 ^ (j + 1) := by
  have hbase : 0 < R * 2 ^ j := Nat.mul_pos hR (pow_pos (by norm_num) _)
  obtain ⟨hp, hlo, hhi⟩ := bertrandPrime_spec hbase
  refine ⟨hp, hlo, ?_⟩
  calc
    dyadicPrime R j ≤ 2 * (R * 2 ^ j) := hhi
    _ = R * 2 ^ (j + 1) := by simp [pow_succ, mul_comm, mul_left_comm]

theorem dyadicPrime_prime {R j : ℕ} (hR : 0 < R) :
    (dyadicPrime R j).Prime := (dyadicPrime_spec hR).1

theorem dyadicPrime_strictMono {R i j : ℕ} (hR : 0 < R) (hij : i < j) :
    dyadicPrime R i < dyadicPrime R j := by
  have hij' : i + 1 ≤ j := by omega
  have hpow : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij'
  calc
    dyadicPrime R i ≤ R * 2 ^ (i + 1) := (dyadicPrime_spec hR).2.2
    _ ≤ R * 2 ^ j := Nat.mul_le_mul_left R hpow
    _ < dyadicPrime R j := (dyadicPrime_spec hR).2.1

theorem dyadicPrime_injective {R : ℕ} (hR : 0 < R) :
    Function.Injective (dyadicPrime R) := by
  intro i j hij
  apply le_antisymm
  · by_contra h
    have hji : j < i := Nat.lt_of_not_ge h
    exact (dyadicPrime_strictMono hR hji).ne hij.symm
  · by_contra h
    have hij' : i < j := Nat.lt_of_not_ge h
    exact (dyadicPrime_strictMono hR hij').ne hij

/-- The first `M` dyadically separated Bertrand primes. -/
def dyadicPrimePool (R M : ℕ) : Finset ℕ :=
  (Finset.range M).image (dyadicPrime R)

theorem card_dyadicPrimePool {R M : ℕ} (hR : 0 < R) :
    (dyadicPrimePool R M).card = M := by
  rw [dyadicPrimePool, Finset.card_image_of_injective _ (dyadicPrime_injective hR),
    Finset.card_range]

theorem mem_dyadicPrimePool_iff {R M p : ℕ} :
    p ∈ dyadicPrimePool R M ↔ ∃ j < M, dyadicPrime R j = p := by
  simp [dyadicPrimePool]

theorem prime_of_mem_dyadicPrimePool {R M p : ℕ} (hR : 0 < R)
    (hp : p ∈ dyadicPrimePool R M) : p.Prime := by
  obtain ⟨j, -, rfl⟩ := mem_dyadicPrimePool_iff.mp hp
  exact dyadicPrime_prime hR

theorem bounds_of_mem_dyadicPrimePool {R M p : ℕ} (hR : 0 < R)
    (hp : p ∈ dyadicPrimePool R M) : R < p ∧ p ≤ R * 2 ^ M := by
  obtain ⟨j, hjM, rfl⟩ := mem_dyadicPrimePool_iff.mp hp
  constructor
  · exact lt_of_le_of_lt (Nat.le_mul_of_pos_right R (pow_pos (by norm_num) j))
      (dyadicPrime_spec hR).2.1
  · have hj : j + 1 ≤ M := by omega
    exact (dyadicPrime_spec hR).2.2.trans
      (Nat.mul_le_mul_left R (Nat.pow_le_pow_right (by norm_num) hj))

/-- The modulus attached to a finite set of primes. -/
def primeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

theorem primeFactors_primeProduct {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) : (primeProduct s).primeFactors = s := by
  exact Nat.primeFactors_prod hs

theorem primeProduct_injective_on_prime_sets {s t : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (hst : primeProduct s = primeProduct t) : s = t := by
  rw [← primeFactors_primeProduct hs, ← primeFactors_primeProduct ht, hst]

theorem primeProduct_ne_zero {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    primeProduct s ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hs p hp).ne_zero

theorem pairwise_coprime_of_prime_set {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (s : Set ℕ).Pairwise Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq

theorem primeProduct_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (primeProduct s) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_iff.mp (hs p hp)).squarefree

theorem primeProduct_bounds {R M : ℕ} (hR : 0 < R)
    {s : Finset ℕ} (hs : s ⊆ dyadicPrimePool R M) :
    R ^ s.card ≤ primeProduct s ∧
      primeProduct s ≤ (R * 2 ^ M) ^ s.card := by
  constructor
  · simpa [primeProduct] using Finset.prod_le_prod
      (fun _ _ ↦ Nat.zero_le R)
      (fun p hp ↦ (bounds_of_mem_dyadicPrimePool hR (hs hp)).1.le)
  · exact Finset.prod_le_pow_card s id (R * 2 ^ M) fun p hp ↦
      (bounds_of_mem_dyadicPrimePool hR (hs hp)).2

theorem lcm_primeProducts {u s t : Finset ℕ}
    (hu : ∀ p ∈ u, p.Prime) (hs : s ⊆ u) (ht : t ⊆ u) :
    Nat.lcm (primeProduct s) (primeProduct t) = primeProduct (s ∪ t) := by
  have hsu : ∀ p ∈ s, p.Prime := fun p hp ↦ hu p (hs hp)
  have htu : ∀ p ∈ t, p.Prime := fun p hp ↦ hu p (ht hp)
  have hstu : ∀ p ∈ s ∪ t, p.Prime := fun p hp ↦ hu p <| by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hs hp
    · exact ht hp
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact Finset.prod_dvd_prod_of_subset s (s ∪ t) id Finset.subset_union_left
    · exact Finset.prod_dvd_prod_of_subset t (s ∪ t) id Finset.subset_union_right
  · apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hstu p hp) (hstu q hq)).mpr hpq)
    · intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.dvd_prod_of_mem id hp).trans (Nat.dvd_lcm_left _ _)
      · exact (Finset.dvd_prod_of_mem id hp).trans (Nat.dvd_lcm_right _ _)

/-- The product attached directly to a finite set of dyadic indices. -/
def dyadicIndexProduct (R : ℕ) (s : Finset ℕ) : ℕ :=
  ∏ j ∈ s, dyadicPrime R j

/-- The product of the first `k` dyadically selected primes. -/
def dyadicPrefixProduct (R k : ℕ) : ℕ :=
  dyadicIndexProduct R (Finset.range k)

theorem fin_val_le_of_strictMono {k : ℕ} (f : Fin k → ℕ)
    (hf : StrictMono f) (i : Fin k) : i.val ≤ f i := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          have hlt : f i.castSucc < f i.succ := hf Fin.castSucc_lt_succ
          simpa only [Fin.val_succ] using Nat.succ_le_of_lt (ih.trans_lt hlt)

theorem dyadicPrefixProduct_eq_fin_prod (R k : ℕ) :
    dyadicPrefixProduct R k = ∏ i : Fin k, dyadicPrime R i.val := by
  unfold dyadicPrefixProduct dyadicIndexProduct
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

theorem dyadicIndexProduct_eq_fin_prod {R k : ℕ} {s : Finset ℕ}
    (hs : s.card = k) :
    dyadicIndexProduct R s =
      ∏ i : Fin k, dyadicPrime R (s.orderEmbOfFin hs i) := by
  unfold dyadicIndexProduct
  calc
    (∏ j ∈ s, dyadicPrime R j) =
        ∏ j ∈ Finset.map (s.orderEmbOfFin hs).toEmbedding Finset.univ,
          dyadicPrime R j := by rw [Finset.map_orderEmbOfFin_univ]
    _ = ∏ i ∈ (Finset.univ : Finset (Fin k)),
        dyadicPrime R (s.orderEmbOfFin hs i) := Finset.prod_map _ _ _
    _ = ∏ i : Fin k, dyadicPrime R (s.orderEmbOfFin hs i) := rfl

/-- Among all products of `k` members of the ordered dyadic sequence, the
product of the first `k` is the smallest. -/
theorem dyadicPrefixProduct_le_indexProduct {R k : ℕ} (hR : 0 < R)
    {s : Finset ℕ} (hs : s.card = k) :
    dyadicPrefixProduct R k ≤ dyadicIndexProduct R s := by
  rw [dyadicPrefixProduct_eq_fin_prod, dyadicIndexProduct_eq_fin_prod hs]
  apply Finset.prod_le_prod
  · exact fun _ _ ↦ Nat.zero_le _
  · intro i _
    have hmono : StrictMono (dyadicPrime R) :=
      fun _ _ ↦ dyadicPrime_strictMono hR
    exact hmono.monotone
      (fin_val_le_of_strictMono (s.orderEmbOfFin hs)
        (s.orderEmbOfFin hs).strictMono i)

theorem dyadicPrime_two_le (R j : ℕ) : 2 ≤ dyadicPrime R j := by
  by_cases hR : R = 0
  · simp [dyadicPrime, bertrandPrime, hR]
  · exact (dyadicPrime_prime (Nat.pos_of_ne_zero hR)).two_le

theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

theorem two_pow_le_dyadicPrefixProduct (R k : ℕ) :
    2 ^ k ≤ dyadicPrefixProduct R k := by
  unfold dyadicPrefixProduct dyadicIndexProduct
  simpa [Finset.card_range, Finset.prod_const] using
    (Finset.prod_le_prod (s := Finset.range k)
      (fun _ _ ↦ Nat.zero_le 2) (fun j _ ↦ dyadicPrime_two_le R j))

theorem exists_dyadicPrefixProduct_ge (R Q : ℕ) :
    ∃ k, Q ≤ dyadicPrefixProduct R k := by
  exact ⟨Q, (self_le_two_pow Q).trans (two_pow_le_dyadicPrefixProduct R Q)⟩

/-- The least number of initial dyadic primes whose product is at least `Q`. -/
def firstCrossing (R Q : ℕ) : ℕ :=
  Nat.find (exists_dyadicPrefixProduct_ge R Q)

theorem firstCrossing_spec (R Q : ℕ) :
    Q ≤ dyadicPrefixProduct R (firstCrossing R Q) :=
  Nat.find_spec (exists_dyadicPrefixProduct_ge R Q)

theorem firstCrossing_minimal {R Q j : ℕ} (hj : j < firstCrossing R Q) :
    dyadicPrefixProduct R j < Q := by
  have hnot := Nat.find_min (exists_dyadicPrefixProduct_ge R Q) hj
  omega

theorem firstCrossing_le {R Q M : ℕ}
    (hroom : Q ≤ dyadicPrefixProduct R M) : firstCrossing R Q ≤ M :=
  Nat.find_min' (exists_dyadicPrefixProduct_ge R Q) hroom

theorem dyadicPrefixProduct_succ (R k : ℕ) :
    dyadicPrefixProduct R (k + 1) =
      dyadicPrefixProduct R k * dyadicPrime R k := by
  simp [dyadicPrefixProduct, dyadicIndexProduct, Finset.prod_range_succ]

theorem dyadicPrefixProduct_zero (R : ℕ) : dyadicPrefixProduct R 0 = 1 := by
  simp [dyadicPrefixProduct, dyadicIndexProduct]

/-- Minimality bounds the overshoot by the last selected prime. -/
theorem firstCrossing_prefix_le_overshoot {R Q : ℕ} (hR : 0 < R)
    (hQ : 0 < Q) :
    dyadicPrefixProduct R (firstCrossing R Q) ≤
      Q * (R * 2 ^ firstCrossing R Q) := by
  let k := firstCrossing R Q
  change dyadicPrefixProduct R k ≤ Q * (R * 2 ^ k)
  by_cases hk : k = 0
  · rw [hk, dyadicPrefixProduct_zero, pow_zero, mul_one]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hQ.ne' hR.ne')
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hprevlt : dyadicPrefixProduct R (k - 1) < Q := by
      apply firstCrossing_minimal
      omega
    have hfactor : dyadicPrime R (k - 1) ≤ R * 2 ^ k := by
      have h := (dyadicPrime_spec (j := k - 1) hR).2.2
      have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
      simpa [hk_eq] using h
    calc
      dyadicPrefixProduct R k =
          dyadicPrefixProduct R (k - 1) * dyadicPrime R (k - 1) := by
        nth_rw 1 [← Nat.sub_add_cancel hkpos]
        exact dyadicPrefixProduct_succ R (k - 1)
      _ ≤ Q * (R * 2 ^ k) := Nat.mul_le_mul hprevlt.le hfactor

theorem firstCrossing_prefix_le_room_overshoot {R Q M : ℕ}
    (hR : 0 < R) (hQ : 0 < Q)
    (hroom : Q ≤ dyadicPrefixProduct R M) :
    dyadicPrefixProduct R (firstCrossing R Q) ≤ Q * (R * 2 ^ M) := by
  have hkM := firstCrossing_le hroom
  calc
    dyadicPrefixProduct R (firstCrossing R Q) ≤
        Q * (R * 2 ^ firstCrossing R Q) :=
      firstCrossing_prefix_le_overshoot hR hQ
    _ ≤ Q * (R * 2 ^ M) := Nat.mul_le_mul_left Q
      (Nat.mul_le_mul_left R (Nat.pow_le_pow_right (by norm_num) hkM))

theorem dyadicIndexProduct_upper {R M : ℕ} (hR : 0 < R)
    {s : Finset ℕ} (hs : s ⊆ Finset.range M) :
    dyadicIndexProduct R s ≤ (R * 2 ^ M) ^ s.card := by
  apply Finset.prod_le_pow_card
  intro j hj
  have hjM : j < M := Finset.mem_range.mp (hs hj)
  exact (dyadicPrime_spec hR).2.2.trans
    (Nat.mul_le_mul_left R
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem dyadicIndexProduct_lower {R : ℕ} (hR : 0 < R)
    (s : Finset ℕ) : R ^ s.card ≤ dyadicIndexProduct R s := by
  unfold dyadicIndexProduct
  simpa [Finset.prod_const] using
    (Finset.prod_le_prod (s := s) (fun _ _ ↦ Nat.zero_le R)
      (fun j _ ↦ (lt_of_le_of_lt
        (Nat.le_mul_of_pos_right R (pow_pos (by norm_num) j))
        (dyadicPrime_spec hR).2.1).le))

/-- If the target is at most `R^K`, the crossing cardinality is at most the
fixed integer `K`.  This is the form that keeps the reservoir cardinality
independent of the main height parameter. -/
theorem firstCrossing_le_of_target_le_base_pow {R Q K : ℕ} (hR : 0 < R)
    (hQ : Q ≤ R ^ K) : firstCrossing R Q ≤ K := by
  apply firstCrossing_le
  exact hQ.trans <| by
    simpa only [Finset.card_range] using
      dyadicIndexProduct_lower hR (Finset.range K)

/-- Changing from the first `k` dyadic indices to any `k` indices below `M`
costs at most the dimensionless factor `2^(M*k)`.  In particular the base
scale `R` is not paid `k` additional times. -/
theorem dyadicIndexProduct_le_prefix_mul_twoPow {R M k : ℕ}
    (hR : 0 < R) {s : Finset ℕ} (hs : s ⊆ Finset.range M)
    (hcard : s.card = k) :
    dyadicIndexProduct R s ≤ dyadicPrefixProduct R k * 2 ^ (M * k) := by
  have hu := dyadicIndexProduct_upper hR hs
  rw [hcard] at hu
  have hl := dyadicIndexProduct_lower hR (Finset.range k)
  simp only [Finset.card_range] at hl
  calc
    dyadicIndexProduct R s ≤ (R * 2 ^ M) ^ k := hu
    _ = R ^ k * 2 ^ (M * k) := by rw [mul_pow, ← pow_mul]
    _ ≤ dyadicPrefixProduct R k * 2 ^ (M * k) :=
      Nat.mul_le_mul_right _ hl

/-- Tight minimal-crossing upper bound for every `k`-subset modulus. -/
theorem firstCrossing_indexProduct_tight_upper {R Q M : ℕ}
    (hR : 0 < R) (hQ : 0 < Q) {s : Finset ℕ}
    (hs : s ⊆ Finset.range M)
    (hcard : s.card = firstCrossing R Q) :
    dyadicIndexProduct R s ≤
      Q * R * 2 ^ (M * firstCrossing R Q + firstCrossing R Q) := by
  let k := firstCrossing R Q
  have hratio : dyadicIndexProduct R s ≤
      dyadicPrefixProduct R k * 2 ^ (M * k) :=
    dyadicIndexProduct_le_prefix_mul_twoPow hR hs hcard
  have hover : dyadicPrefixProduct R k ≤ Q * (R * 2 ^ k) :=
    firstCrossing_prefix_le_overshoot hR hQ
  calc
    dyadicIndexProduct R s ≤ dyadicPrefixProduct R k * 2 ^ (M * k) := hratio
    _ ≤ (Q * (R * 2 ^ k)) * 2 ^ (M * k) :=
      Nat.mul_le_mul_right _ hover
    _ = Q * R * 2 ^ (M * k + k) := by rw [pow_add]; ring

/-- Exact arithmetic absorption of the reservoir loss into a prescribed
height power.  Here `K`, `M`, and `e` may be fixed before the height `H`
varies. -/
theorem firstCrossing_indexProduct_auxiliaryNatScale {Haux R Q M K e : ℕ}
    (hR : 0 < R) (hQpos : 0 < Q) (hQ : Q ≤ R ^ K)
    (hRscale : R ≤ Haux ^ e)
    (hTwoScale : 2 ^ (M * K + K) ≤ Haux ^ e)
    {s : Finset ℕ} (hs : s ⊆ Finset.range M)
    (hcard : s.card = firstCrossing R Q) :
    dyadicIndexProduct R s ≤ Q * Haux ^ (2 * e) := by
  have hkK := firstCrossing_le_of_target_le_base_pow hR hQ
  have hexp : M * firstCrossing R Q + firstCrossing R Q ≤ M * K + K :=
    Nat.add_le_add (Nat.mul_le_mul_left M hkK) hkK
  calc
    dyadicIndexProduct R s ≤
        Q * R * 2 ^ (M * firstCrossing R Q + firstCrossing R Q) :=
      firstCrossing_indexProduct_tight_upper hR hQpos hs hcard
    _ ≤ Q * R * 2 ^ (M * K + K) :=
      Nat.mul_le_mul_left (Q * R)
        (Nat.pow_le_pow_right (by norm_num) hexp)
    _ ≤ (Q * Haux ^ e) * Haux ^ e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left Q hRscale) hTwoScale
    _ = Q * Haux ^ (2 * e) := by
      rw [show 2 * e = e + e by omega, pow_add]
      ring

/-- Real-height form of the fixed-reservoir estimate.  The auxiliary natural
height is `ceil(mathcalH^δ)`, not the manuscript height `mathcalH` itself. -/
theorem firstCrossing_indexProduct_realHeightScale
    {mathcalH δ : ℝ} (hmathcalH : 1 ≤ mathcalH) (hδ : 0 ≤ δ)
    {Q M K : ℕ} (hQpos : 0 < Q)
    (hQ : (Q : ℝ) ≤ mathcalH ^ (δ * (K : ℝ)))
    (hFinite : (2 ^ (M * K + K) : ℕ) ≤ mathcalH ^ δ)
    {s : Finset ℕ}
    (hs : s ⊆ Finset.range M)
    (hcard : s.card = firstCrossing (realAuxiliaryHeight mathcalH δ) Q) :
    (dyadicIndexProduct (realAuxiliaryHeight mathcalH δ) s : ℝ) ≤
      (Q : ℝ) * (2 * mathcalH ^ δ) ^ 2 := by
  let R := realAuxiliaryHeight mathcalH δ
  have hR : 0 < R :=
    realAuxiliaryHeight_pos (lt_of_lt_of_le zero_lt_one hmathcalH)
  have hQnat : Q ≤ R ^ K :=
    nat_le_realAuxiliaryHeight_pow (zero_le_one.trans hmathcalH) hQ
  have hFiniteNat : 2 ^ (M * K + K) ≤ R :=
    nat_le_realAuxiliaryHeight hFinite
  have hnat : dyadicIndexProduct R s ≤ Q * R ^ 2 := by
    simpa using firstCrossing_indexProduct_auxiliaryNatScale
      (Haux := R) (R := R) (e := 1) hR hQpos hQnat
      (by simp) (by simpa using hFiniteNat) hs hcard
  have hcast : (dyadicIndexProduct R s : ℝ) ≤ (Q : ℝ) * (R : ℝ) ^ 2 := by
    exact_mod_cast hnat
  exact hcast.trans <| by
    gcongr
    exact realAuxiliaryHeight_cast_le_two_rpow hmathcalH hδ

theorem dyadicIndexProduct_eq_primeProduct_image {R : ℕ} (hR : 0 < R)
    (s : Finset ℕ) :
    dyadicIndexProduct R s = primeProduct (s.image (dyadicPrime R)) := by
  unfold dyadicIndexProduct primeProduct
  symm
  exact Finset.prod_image (dyadicPrime_injective hR).injOn

theorem image_dyadicPrime_subset_pool {R M : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range M) :
    s.image (dyadicPrime R) ⊆ dyadicPrimePool R M := by
  intro p hp
  obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨j, hs hjs, rfl⟩

theorem lcm_dyadicIndexProducts {R M : ℕ} (hR : 0 < R)
    {s t : Finset ℕ} (hs : s ⊆ Finset.range M)
    (ht : t ⊆ Finset.range M) :
    Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) =
      dyadicIndexProduct R (s ∪ t) := by
  rw [dyadicIndexProduct_eq_primeProduct_image hR,
    dyadicIndexProduct_eq_primeProduct_image hR,
    lcm_primeProducts (fun p hp ↦ prime_of_mem_dyadicPrimePool hR hp)
      (image_dyadicPrime_subset_pool hs) (image_dyadicPrime_subset_pool ht),
    dyadicIndexProduct_eq_primeProduct_image hR, Finset.image_union]

/-- Exact fixed-pool bounds at the minimal crossing index.  The first
conclusion says that the crossing occurs inside the pool.  Every subset of
that cardinality has product at least `Q`; the last inequality is a completely
explicit uniform upper bound. -/
theorem firstCrossing_indexProduct_bounds {R Q M : ℕ} (hR : 0 < R)
    (hQ : 0 < Q) (hroom : Q ≤ dyadicPrefixProduct R M)
    {s : Finset ℕ} (hs : s ⊆ Finset.range M)
    (hcard : s.card = firstCrossing R Q) :
    firstCrossing R Q ≤ M ∧
      Q ≤ dyadicIndexProduct R s ∧
      dyadicIndexProduct R s ≤
        Q * R * 2 ^ (M * firstCrossing R Q + firstCrossing R Q) := by
  have hkM := firstCrossing_le hroom
  refine ⟨hkM, ?_, ?_⟩
  · exact (firstCrossing_spec R Q).trans
      (dyadicPrefixProduct_le_indexProduct hR hcard)
  · exact firstCrossing_indexProduct_tight_upper hR hQ hs hcard

theorem lcm_primeProducts_bound {R M : ℕ} (hR : 0 < R)
    {s t : Finset ℕ} (hs : s ⊆ dyadicPrimePool R M)
    (ht : t ⊆ dyadicPrimePool R M) :
    Nat.lcm (primeProduct s) (primeProduct t)
      ≤ (R * 2 ^ M) ^ (s ∪ t).card := by
  rw [lcm_primeProducts (fun p hp ↦ prime_of_mem_dyadicPrimePool hR hp) hs ht]
  exact (primeProduct_bounds hR (Finset.union_subset hs ht)).2

theorem threshold_lt_primeProduct {R M Q : ℕ} (hR : 0 < R)
    {s : Finset ℕ} (hs : s ⊆ dyadicPrimePool R M)
    (hQ : Q < R ^ s.card) : Q < primeProduct s :=
  hQ.trans_le (primeProduct_bounds hR hs).1

theorem primeProduct_dvd_of_each_dvd {u s : Finset ℕ}
    (hu : ∀ p ∈ u, p.Prime) (hs : s ⊆ u) {D : ℕ}
    (hdiv : ∀ p ∈ s, p ∣ D) : primeProduct s ∣ D := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hu p (hs hp)) (hu q (hs hq))).mpr hpq)
  · exact hdiv

/-- A certificate `D` smaller than `R^b` is divisible by fewer than `b`
members of the dyadic pool.  This is the elementary substitute for any
prime-density estimate in the deletion step. -/
theorem card_lt_of_dyadicPrimePool_dvd_certificate {R M D b : ℕ}
    (hR : 1 < R) (hD : 0 < D) {bad : Finset ℕ}
    (hbad : bad ⊆ dyadicPrimePool R M) (hdiv : ∀ p ∈ bad, p ∣ D)
    (hsize : D < R ^ b) : bad.card < b := by
  have hRpos : 0 < R := by omega
  have hprodD : primeProduct bad ∣ D := primeProduct_dvd_of_each_dvd
    (fun p hp ↦ prime_of_mem_dyadicPrimePool hRpos hp) hbad hdiv
  have hp_le_D : primeProduct bad ≤ D := Nat.le_of_dvd hD hprodD
  have hlower : R ^ bad.card ≤ primeProduct bad :=
    (primeProduct_bounds hRpos hbad).1
  exact (Nat.pow_lt_pow_iff_right hR).mp (hlower.trans_lt (hp_le_D.trans_lt hsize))

/-- The members of the dyadic pool that divide the nonzero integer `D`. -/
def integerBadPrimes (R M : ℕ) (D : ℤ) : Finset ℕ :=
  (dyadicPrimePool R M).filter fun p ↦ (p : ℤ) ∣ D

theorem mem_integerBadPrimes_iff {R M p : ℕ} {D : ℤ} :
    p ∈ integerBadPrimes R M D ↔ p ∈ dyadicPrimePool R M ∧ (p : ℤ) ∣ D := by
  simp [integerBadPrimes]

theorem card_integerBadPrimes_lt {R M b : ℕ} (hR : 1 < R)
    {D : ℤ} (hD : D ≠ 0) (hsize : D.natAbs < R ^ b) :
    (integerBadPrimes R M D).card < b := by
  apply card_lt_of_dyadicPrimePool_dvd_certificate (M := M)
      (bad := integerBadPrimes R M D) hR (Int.natAbs_pos.mpr hD)
  · intro p hp
    exact (Finset.mem_filter.mp hp).1
  · intro p hp
    exact Int.natCast_dvd.mp (Finset.mem_filter.mp hp).2
  · exact hsize

/-- The pool primes dividing at least one of two integer certificates. -/
def integerBadPrimesTwo (R M : ℕ) (D₁ D₂ : ℤ) : Finset ℕ :=
  integerBadPrimes R M D₁ ∪ integerBadPrimes R M D₂

theorem card_integerBadPrimesTwo_lt {R M b₁ b₂ : ℕ} (hR : 1 < R)
    {D₁ D₂ : ℤ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hsize₁ : D₁.natAbs < R ^ b₁) (hsize₂ : D₂.natAbs < R ^ b₂) :
    (integerBadPrimesTwo R M D₁ D₂).card < b₁ + b₂ := by
  have h₁ := card_integerBadPrimes_lt (M := M) hR hD₁ hsize₁
  have h₂ := card_integerBadPrimes_lt (M := M) hR hD₂ hsize₂
  have hu := Finset.card_union_le (integerBadPrimes R M D₁) (integerBadPrimes R M D₂)
  simpa only [integerBadPrimesTwo] using hu.trans_lt (Nat.add_lt_add h₁ h₂)

/-- Two finite sets differ by one exchange if the second is obtained by
deleting one member of the first and inserting one new member. -/
def OneExchange (s t : Finset ℕ) : Prop :=
  ∃ p ∈ s, ∃ q ∉ s, t = insert q (s.erase p)

theorem oneExchange_subset_card {u s t : Finset ℕ} (hs : s ⊆ u)
    {p q : ℕ} (hp : p ∈ s) (hq : q ∈ u) (hqnot : q ∉ s)
    (ht : t = insert q (s.erase p)) :
    t ⊆ u ∧ t.card = s.card ∧ OneExchange s t := by
  subst t
  refine ⟨?_, ?_, ⟨p, hp, q, hqnot, rfl⟩⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | hx
    · exact hq
    · exact hs hx.2
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem hp]
      have hcardpos : 0 < s.card := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    · simp [Finset.mem_erase, hqnot]

theorem card_union_eq_succ_of_oneExchange {s t : Finset ℕ}
    (hst : OneExchange s t) : (s ∪ t).card = s.card + 1 := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hst
  have hu : s ∪ insert q (s.erase p) = insert q s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    aesop
  rw [hu, Finset.card_insert_of_notMem hq]

theorem lcm_primeProducts_oneExchange_bound {R M : ℕ} (hR : 0 < R)
    {s t : Finset ℕ} (hs : s ⊆ dyadicPrimePool R M)
    (ht : t ⊆ dyadicPrimePool R M) (hst : OneExchange s t) :
    Nat.lcm (primeProduct s) (primeProduct t)
      ≤ (R * 2 ^ M) ^ (s.card + 1) := by
  simpa [card_union_eq_succ_of_oneExchange hst] using
    lcm_primeProducts_bound hR hs ht

/-- In one index exchange, the union product costs only the one newly inserted
prime. -/
theorem dyadicIndexProduct_union_oneExchange_le {R M : ℕ} (hR : 0 < R)
    {s t : Finset ℕ} (ht : t ⊆ Finset.range M) (hst : OneExchange s t) :
    dyadicIndexProduct R (s ∪ t) ≤
      dyadicIndexProduct R s * (R * 2 ^ M) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := hst
  have hqM : q < M :=
    Finset.mem_range.mp (ht (Finset.mem_insert_self q (s.erase p)))
  have hfactor : dyadicPrime R q ≤ R * 2 ^ M :=
    (dyadicPrime_spec hR).2.2.trans
      (Nat.mul_le_mul_left R
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hu : s ∪ insert q (s.erase p) = insert q s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    aesop
  rw [hu]
  unfold dyadicIndexProduct
  rw [Finset.prod_insert hq]
  simpa [mul_comm] using
    Nat.mul_le_mul_left (∏ j ∈ s, dyadicPrime R j) hfactor

/-- At the minimal crossing cardinality, adjacent index moduli have their
least common multiple between `Q` and the explicit `(k+1)`-factor pool bound. -/
theorem firstCrossing_oneExchange_lcm_bounds {R Q M : ℕ} (hR : 0 < R)
    (hQ : 0 < Q) (hroom : Q ≤ dyadicPrefixProduct R M)
    {s t : Finset ℕ} (hs : s ⊆ Finset.range M)
    (ht : t ⊆ Finset.range M) (hcard : s.card = firstCrossing R Q)
    (hst : OneExchange s t) :
    firstCrossing R Q ≤ M ∧
      Q ≤ Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) ∧
      Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) ≤
        Q * R ^ 2 *
          2 ^ (M * firstCrossing R Q + firstCrossing R Q + M) := by
  refine ⟨firstCrossing_le hroom, ?_, ?_⟩
  · have hprod : Q ≤ dyadicIndexProduct R s :=
      (firstCrossing_spec R Q).trans
        (dyadicPrefixProduct_le_indexProduct hR hcard)
    have hspos : 0 < dyadicIndexProduct R s :=
      Finset.prod_pos fun j _ ↦ lt_of_lt_of_le (by norm_num) (dyadicPrime_two_le R j)
    have htpos : 0 < dyadicIndexProduct R t :=
      Finset.prod_pos fun j _ ↦ lt_of_lt_of_le (by norm_num) (dyadicPrime_two_le R j)
    exact hprod.trans <| Nat.le_of_dvd (Nat.lcm_pos hspos htpos)
      (Nat.dvd_lcm_left _ _)
  · rw [lcm_dyadicIndexProducts hR hs ht]
    calc
      dyadicIndexProduct R (s ∪ t) ≤
          dyadicIndexProduct R s * (R * 2 ^ M) :=
        dyadicIndexProduct_union_oneExchange_le hR ht hst
      _ ≤ (Q * R *
          2 ^ (M * firstCrossing R Q + firstCrossing R Q)) *
          (R * 2 ^ M) :=
        Nat.mul_le_mul_right _
          (firstCrossing_indexProduct_tight_upper hR hQ hs hcard)
      _ = Q * R ^ 2 *
          2 ^ (M * firstCrossing R Q + firstCrossing R Q + M) := by
        rw [pow_add]
        ring

/-- Polynomial-scale form of the adjacent-lcm estimate for a fixed-size
reservoir.  It pays three copies of the chosen small height power: two for the
two base-scale prime factors and one for the dimensionless finite-pool loss. -/
theorem firstCrossing_oneExchange_lcm_auxiliaryNatScale
    {Haux R Q M K e : ℕ} (hR : 0 < R) (hQpos : 0 < Q)
    (hQ : Q ≤ R ^ K) (hKM : K ≤ M) (hRscale : R ≤ Haux ^ e)
    (hTwoScale : 2 ^ (M * K + K + M) ≤ Haux ^ e)
    {s t : Finset ℕ} (hs : s ⊆ Finset.range M)
    (ht : t ⊆ Finset.range M) (hcard : s.card = firstCrossing R Q)
    (hst : OneExchange s t) :
    Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) ≤
      Q * Haux ^ (3 * e) := by
  have hkK := firstCrossing_le_of_target_le_base_pow hR hQ
  have hbasepow : R ^ K ≤ R ^ M :=
    pow_le_pow_right₀ (Nat.one_le_iff_ne_zero.mpr hR.ne') hKM
  have hroom : Q ≤ dyadicPrefixProduct R M :=
    hQ.trans <| hbasepow.trans <| by
      simpa only [Finset.card_range] using
        dyadicIndexProduct_lower hR (Finset.range M)
  have hlcm :=
    (firstCrossing_oneExchange_lcm_bounds hR hQpos hroom hs ht hcard hst).2.2
  have hexp :
      M * firstCrossing R Q + firstCrossing R Q + M ≤ M * K + K + M :=
    Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul_left M hkK) hkK) M
  have hR2 : R ^ 2 ≤ (Haux ^ e) ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hRscale hRscale
  calc
    Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) ≤
        Q * R ^ 2 *
          2 ^ (M * firstCrossing R Q + firstCrossing R Q + M) := hlcm
    _ ≤ Q * R ^ 2 * 2 ^ (M * K + K + M) :=
      Nat.mul_le_mul_left (Q * R ^ 2)
        (Nat.pow_le_pow_right (by norm_num) hexp)
    _ ≤ (Q * (Haux ^ e) ^ 2) * Haux ^ e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left Q hR2) hTwoScale
    _ = Q * Haux ^ (3 * e) := by
      rw [show 3 * e = e + e + e by omega, pow_add, pow_add]
      ring

/-- Real-height adjacent-lcm estimate at the auxiliary scale
`ceil(mathcalH^δ)`. -/
theorem firstCrossing_oneExchange_lcm_realHeightScale
    {mathcalH δ : ℝ} (hmathcalH : 1 ≤ mathcalH) (hδ : 0 ≤ δ)
    {Q M K : ℕ} (hQpos : 0 < Q)
    (hQ : (Q : ℝ) ≤ mathcalH ^ (δ * (K : ℝ))) (hKM : K ≤ M)
    (hFinite : (2 ^ (M * K + K + M) : ℕ) ≤ mathcalH ^ δ)
    {s t : Finset ℕ}
    (hs : s ⊆ Finset.range M) (ht : t ⊆ Finset.range M)
    (hcard : s.card = firstCrossing (realAuxiliaryHeight mathcalH δ) Q)
    (hst : OneExchange s t) :
    (Nat.lcm
        (dyadicIndexProduct (realAuxiliaryHeight mathcalH δ) s)
        (dyadicIndexProduct (realAuxiliaryHeight mathcalH δ) t) : ℝ) ≤
      (Q : ℝ) * (2 * mathcalH ^ δ) ^ 3 := by
  let R := realAuxiliaryHeight mathcalH δ
  have hR : 0 < R :=
    realAuxiliaryHeight_pos (lt_of_lt_of_le zero_lt_one hmathcalH)
  have hQnat : Q ≤ R ^ K :=
    nat_le_realAuxiliaryHeight_pow (zero_le_one.trans hmathcalH) hQ
  have hFiniteNat : 2 ^ (M * K + K + M) ≤ R :=
    nat_le_realAuxiliaryHeight hFinite
  have hnat :
      Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) ≤ Q * R ^ 3 := by
    simpa using firstCrossing_oneExchange_lcm_auxiliaryNatScale
      (Haux := R) (R := R) (e := 1) hR hQpos hQnat hKM
      (by simp) (by simpa using hFiniteNat) hs ht hcard hst
  have hcast :
      (Nat.lcm (dyadicIndexProduct R s) (dyadicIndexProduct R t) : ℝ) ≤
        (Q : ℝ) * (R : ℝ) ^ 3 := by
    exact_mod_cast hnat
  exact hcast.trans <| by
    gcongr
    exact realAuxiliaryHeight_cast_le_two_rpow hmathcalH hδ

/-- If two equal-cardinality finite sets are distinct, one may make one
exchange toward the second set.  The exchanged set remains in the ambient
set and has one fewer element outside the target. -/
theorem exists_oneExchange_toward {u s t : Finset ℕ} (hs : s ⊆ u)
    (ht : t ⊆ u) (hcard : s.card = t.card) (hne : s ≠ t) :
    ∃ s', s' ⊆ u ∧ s'.card = s.card ∧ OneExchange s s' ∧
      (s' \ t).card < (s \ t).card := by
  have hst : (s \ t).Nonempty := by
    by_contra h
    have hsub : s ⊆ t := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.symm.le)
  have hts : (t \ s).Nonempty := by
    by_contra h
    have hsub : t ⊆ s := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard.le).symm
  obtain ⟨p, hp⟩ := hst
  obtain ⟨q, hq⟩ := hts
  have hps : p ∈ s := (Finset.mem_sdiff.mp hp).1
  have hpt : p ∉ t := (Finset.mem_sdiff.mp hp).2
  have hqt : q ∈ t := (Finset.mem_sdiff.mp hq).1
  have hqs : q ∉ s := (Finset.mem_sdiff.mp hq).2
  let s' := insert q (s.erase p)
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · exact (oneExchange_subset_card hs hps (ht hqt) hqs rfl).1
  · exact (oneExchange_subset_card hs hps (ht hqt) hqs rfl).2.1
  · exact (oneExchange_subset_card hs hps (ht hqt) hqs rfl).2.2
  · have heq : s' \ t = (s \ t).erase p := by
      ext x
      simp only [s', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      aesop
    rw [heq, Finset.card_erase_of_mem hp]
    have hpos : 0 < (s \ t).card := Finset.card_pos.mpr ⟨p, hp⟩
    omega

/-- Any two fixed-cardinality subsets of an ambient finite set are connected
by finitely many one-element exchanges.  This is the precise connectivity
statement used for the reservoir after any finite set of bad primes has been
deleted. -/
theorem oneExchange_connected {u s t : Finset ℕ} (hs : s ⊆ u)
    (ht : t ⊆ u) (hcard : s.card = t.card) :
    Relation.ReflTransGen OneExchange s t := by
  classical
  induction hn : (s \ t).card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hst : s = t
      · subst s
        exact Relation.ReflTransGen.refl
      · obtain ⟨s', hs', hcard', hex, hdec⟩ :=
          exists_oneExchange_toward hs ht hcard hst
        have hcard't : s'.card = t.card := hcard'.trans hcard
        exact (Relation.ReflTransGen.single hex).trans
          (ih (s' \ t).card (hn ▸ hdec) hs' hcard't rfl)

theorem card_allowed_dyadicPrimePool_ge {R M : ℕ} (hR : 0 < R)
    (bad : Finset ℕ) :
    M - bad.card ≤ (dyadicPrimePool R M \ bad).card := by
  have hdecomp := Finset.card_sdiff_add_card_inter (dyadicPrimePool R M) bad
  have hinter : (dyadicPrimePool R M ∩ bad).card ≤ bad.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [card_dyadicPrimePool hR] at hdecomp
  omega

theorem exists_fixedCard_subset_after_deletion {R M k : ℕ} (hR : 0 < R)
    (bad : Finset ℕ) (hroom : bad.card + k ≤ M) :
    ∃ s ⊆ dyadicPrimePool R M \ bad, s.card = k := by
  apply Finset.exists_subset_card_eq
  have hlower := card_allowed_dyadicPrimePool_ge (M := M) hR bad
  omega

theorem oneExchange_connected_after_deletion {R M k : ℕ} (bad : Finset ℕ)
    {s t : Finset ℕ} (hs : s ⊆ dyadicPrimePool R M \ bad)
    (ht : t ⊆ dyadicPrimePool R M \ bad) (hscard : s.card = k)
    (htcard : t.card = k) : Relation.ReflTransGen OneExchange s t := by
  exact oneExchange_connected hs ht (hscard.trans htcard.symm)

/-- The fixed-cardinality reservoir inside an allowed prime set. -/
def modulusReservoir (u : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (u.powersetCard k).image primeProduct

theorem card_modulusReservoir_of_primes {u : Finset ℕ} (hu : ∀ p ∈ u, p.Prime)
    (k : ℕ) : (modulusReservoir u k).card = Nat.choose u.card k := by
  rw [modulusReservoir, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard k u
  · intro s hs t ht hprod
    exact primeProduct_injective_on_prime_sets
      (fun p hp ↦ hu p ((Finset.mem_powersetCard.mp hs).1 hp))
      (fun p hp ↦ hu p ((Finset.mem_powersetCard.mp ht).1 hp)) hprod

theorem mem_modulusReservoir_iff {u : Finset ℕ} (hu : ∀ p ∈ u, p.Prime)
    {k q : ℕ} :
    q ∈ modulusReservoir u k ↔
      ∃! s : Finset ℕ, s ⊆ u ∧ s.card = k ∧ primeProduct s = q := by
  constructor
  · intro hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨s, ⟨(Finset.mem_powersetCard.mp hs).1, (Finset.mem_powersetCard.mp hs).2, rfl⟩, ?_⟩
    intro t ht
    exact primeProduct_injective_on_prime_sets
      (fun p hp ↦ hu p (ht.1 hp))
      (fun p hp ↦ hu p ((Finset.mem_powersetCard.mp hs).1 hp)) ht.2.2
  · rintro ⟨s, ⟨hs, hcard, rfl⟩, -⟩
    exact Finset.mem_image.mpr ⟨s, Finset.mem_powersetCard.mpr ⟨hs, hcard⟩, rfl⟩

theorem squarefree_of_mem_modulusReservoir {u : Finset ℕ} (hu : ∀ p ∈ u, p.Prime)
    {k q : ℕ} (hq : q ∈ modulusReservoir u k) : Squarefree q := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  exact primeProduct_squarefree fun p hp ↦ hu p ((Finset.mem_powersetCard.mp hs).1 hp)

/-- Deleting a bad set leaves exactly a fixed-cardinality reservoir on the
remaining primes.  Its cardinality is therefore a binomial coefficient. -/
theorem card_reservoir_after_deletion {u bad : Finset ℕ}
    (hu : ∀ p ∈ u, p.Prime) (k : ℕ) :
    (modulusReservoir (u \ bad) k).card = Nat.choose (u \ bad).card k := by
  exact card_modulusReservoir_of_primes (fun p hp ↦ hu p (Finset.mem_sdiff.mp hp).1) k

theorem card_dyadic_reservoir_after_deletion_le {R M k : ℕ} (hR : 0 < R)
    (bad : Finset ℕ) :
    (modulusReservoir (dyadicPrimePool R M \ bad) k).card ≤ 2 ^ M := by
  rw [card_reservoir_after_deletion
    (fun p hp ↦ prime_of_mem_dyadicPrimePool hR hp) k]
  have hcard : (dyadicPrimePool R M \ bad).card ≤ M := by
    have h := Finset.card_le_card (Finset.sdiff_subset :
      dyadicPrimePool R M \ bad ⊆ dyadicPrimePool R M)
    simpa [card_dyadicPrimePool hR] using h
  exact (Nat.choose_le_two_pow _ _).trans <|
    Nat.pow_le_pow_right (by norm_num) hcard

theorem exists_dyadic_reservoir_modulus_after_deletion {R M k : ℕ}
    (hR : 0 < R) (bad : Finset ℕ) (hroom : bad.card + k ≤ M) :
    ∃ q ∈ modulusReservoir (dyadicPrimePool R M \ bad) k,
      Squarefree q := by
  obtain ⟨s, hs, hcard⟩ := exists_fixedCard_subset_after_deletion hR bad hroom
  refine ⟨primeProduct s, ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨s, Finset.mem_powersetCard.mpr ⟨hs, hcard⟩, rfl⟩
  · exact primeProduct_squarefree fun p hp ↦
      prime_of_mem_dyadicPrimePool hR (Finset.mem_sdiff.mp (hs hp)).1

/-- A single nonzero integer certificate of size `< R^b` deletes fewer than
`b` pool primes; the surviving `k`-subsets are nonempty and connected when
`b + k ≤ M`. -/
theorem survivingReservoir_oneInteger {R M b k : ℕ} (hR : 1 < R)
    {D : ℤ} (hD : D ≠ 0) (hsize : D.natAbs < R ^ b)
    (hroom : b + k ≤ M) :
    (∃ q ∈ modulusReservoir
        (dyadicPrimePool R M \ integerBadPrimes R M D) k, Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ dyadicPrimePool R M \ integerBadPrimes R M D →
        t ⊆ dyadicPrimePool R M \ integerBadPrimes R M D →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  have hRpos : 0 < R := by omega
  have hbad := card_integerBadPrimes_lt (M := M) hR hD hsize
  have hroom' : (integerBadPrimes R M D).card + k ≤ M := by omega
  refine ⟨exists_dyadic_reservoir_modulus_after_deletion hRpos _ hroom', ?_⟩
  intro s t hs ht hscard htcard
  exact oneExchange_connected_after_deletion (integerBadPrimes R M D)
    hs ht hscard htcard

/-- The corresponding exact statement for two nonzero integer certificates. -/
theorem survivingReservoir_twoIntegers {R M b₁ b₂ k : ℕ} (hR : 1 < R)
    {D₁ D₂ : ℤ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hsize₁ : D₁.natAbs < R ^ b₁) (hsize₂ : D₂.natAbs < R ^ b₂)
    (hroom : b₁ + b₂ + k ≤ M) :
    (∃ q ∈ modulusReservoir
        (dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂) k,
      Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂ →
        t ⊆ dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂ →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  have hRpos : 0 < R := by omega
  have hbad := card_integerBadPrimesTwo_lt (M := M) hR hD₁ hD₂ hsize₁ hsize₂
  have hroom' : (integerBadPrimesTwo R M D₁ D₂).card + k ≤ M := by omega
  refine ⟨exists_dyadic_reservoir_modulus_after_deletion hRpos _ hroom', ?_⟩
  intro s t hs ht hscard htcard
  exact oneExchange_connected_after_deletion (integerBadPrimesTwo R M D₁ D₂)
    hs ht hscard htcard

/-- Fully explicit real-height choice of the reservoir size for two integer
certificates.  We take

`R = ceil(mathcalH^δ)`, `k = firstCrossing R Q`, and `M = K + b₁ + b₂`.

Thus `M` and `k ≤ K` are fixed once `K,b₁,b₂` are fixed; they do not grow
like `log mathcalH / log log mathcalH`. -/
theorem survivingReservoir_twoIntegers_realHeight
    {mathcalH δ : ℝ} (hmathcalH : 1 < mathcalH) (hδ : 0 < δ)
    {Q K b₁ b₂ : ℕ}
    (hQ : (Q : ℝ) ≤ mathcalH ^ (δ * (K : ℝ)))
    {D₁ D₂ : ℤ} (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hsize₁ : (D₁.natAbs : ℝ) < mathcalH ^ (δ * (b₁ : ℝ)))
    (hsize₂ : (D₂.natAbs : ℝ) < mathcalH ^ (δ * (b₂ : ℝ))) :
    let R := realAuxiliaryHeight mathcalH δ
    let M := K + b₁ + b₂
    let k := firstCrossing R Q
    (∃ q ∈ modulusReservoir
        (dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂) k,
      Squarefree q) ∧
      ∀ {s t : Finset ℕ},
        s ⊆ dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂ →
        t ⊆ dyadicPrimePool R M \ integerBadPrimesTwo R M D₁ D₂ →
        s.card = k → t.card = k →
        Relation.ReflTransGen OneExchange s t := by
  dsimp only
  let R := realAuxiliaryHeight mathcalH δ
  have hR : 1 < R := by
    apply Nat.lt_ceil.mpr
    norm_num only [Nat.cast_one]
    exact Real.one_lt_rpow hmathcalH hδ
  have hQnat : Q ≤ R ^ K :=
    nat_le_realAuxiliaryHeight_pow (zero_le_one.trans hmathcalH.le) hQ
  have hkK : firstCrossing R Q ≤ K :=
    firstCrossing_le_of_target_le_base_pow (by omega) hQnat
  have hsize₁nat : D₁.natAbs < R ^ b₁ :=
    nat_lt_realAuxiliaryHeight_pow (zero_le_one.trans hmathcalH.le) hsize₁
  have hsize₂nat : D₂.natAbs < R ^ b₂ :=
    nat_lt_realAuxiliaryHeight_pow (zero_le_one.trans hmathcalH.le) hsize₂
  have hroom : b₁ + b₂ + firstCrossing R Q ≤ K + b₁ + b₂ := by omega
  exact survivingReservoir_twoIntegers hR hD₁ hD₂ hsize₁nat hsize₂nat hroom

end

end TranslatedDepthSeven
