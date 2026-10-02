import CubicTenVariables.NumericalConductor

/-! Split squarefree factors according to the actual numerical depths at
an integer frequency. The high-depth radical is the manuscript's R₂,₂.
All decompositions and conductor identities are exact; no periodicity of
prime-square numerical depth is assumed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalConductorRadical
open MvPolynomial NumericalPrimeDepth
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private def selected (a : ℕ) (E : ℕ → Prop) [DecidablePred E] : ℕ :=
  ∏ p ∈ a.primeFactors with E p, p

private theorem selected_pos (a : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    0 < selected a E :=
  Finset.prod_pos (fun _p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

private theorem selected_primeFactors (a : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (selected a E).primeFactors = a.primeFactors.filter E := by
  exact Nat.primeFactors_prod
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

private theorem selected_dvd (a : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    selected a E ∣ a :=
  (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd a)

private theorem selected_reconstruction (a : ℕ) (ha : Squarefree a)
    (E : ℕ → Prop) [DecidablePred E] :
    a = selected a (fun p => ¬ E p) * selected a E := by
  rw [selected, selected, Finset.prod_filter_not_mul_prod_filter,
    Nat.prod_primeFactors_of_squarefree ha]

/-- Primes in a whose actual prime depth is at least two. -/
def primeHigh (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  selected a (fun p => 2 ≤ NumericalConductor.primeDepth h p v)

/-- The complementary primes of a, with actual depth zero or one. -/
def primeLow (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  selected a (fun p => ¬ 2 ≤ NumericalConductor.primeDepth h p v)

/-- Primes in b whose actual prime-square depth is at least two. -/
def squareHigh (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  selected b (fun p => 2 ≤ NumericalConductor.squareDepth h p v)

/-- The complementary primes of b, with actual square depth zero or one. -/
def squareLow (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  selected b (fun p => ¬ 2 ≤ NumericalConductor.squareDepth h p v)

/-- The actual R₂,₂ radical; for coprime squarefree a,b its two factors
are squarefree and coprime. -/
def R22 (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) : ℕ :=
  primeHigh h a v * squareHigh h b v

theorem R22_eq_filtered_products (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) :
    R22 h a b v =
      (∏ p ∈ a.primeFactors with 2 ≤ NumericalConductor.primeDepth h p v, p) *
      (∏ p ∈ b.primeFactors with 2 ≤ NumericalConductor.squareDepth h p v, p) := rfl

theorem primeHigh_pos (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) :
    0 < primeHigh h a v := selected_pos a _

theorem primeLow_pos (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) :
    0 < primeLow h a v := selected_pos a _

theorem squareHigh_pos (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) :
    0 < squareHigh h b v := selected_pos b _

theorem squareLow_pos (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) :
    0 < squareLow h b v := selected_pos b _

@[simp] theorem primeFactors_primeHigh (h : CoarseBounds F C) (a : ℕ)
    (v : Fin 10 → ℤ) :
    (primeHigh h a v).primeFactors =
      a.primeFactors.filter (fun p => 2 ≤ NumericalConductor.primeDepth h p v) :=
  selected_primeFactors a _

@[simp] theorem primeFactors_primeLow (h : CoarseBounds F C) (a : ℕ)
    (v : Fin 10 → ℤ) :
    (primeLow h a v).primeFactors =
      a.primeFactors.filter (fun p => ¬ 2 ≤ NumericalConductor.primeDepth h p v) :=
  selected_primeFactors a _

@[simp] theorem primeFactors_squareHigh (h : CoarseBounds F C) (b : ℕ)
    (v : Fin 10 → ℤ) :
    (squareHigh h b v).primeFactors =
      b.primeFactors.filter (fun p => 2 ≤ NumericalConductor.squareDepth h p v) :=
  selected_primeFactors b _

@[simp] theorem primeFactors_squareLow (h : CoarseBounds F C) (b : ℕ)
    (v : Fin 10 → ℤ) :
    (squareLow h b v).primeFactors =
      b.primeFactors.filter (fun p => ¬ 2 ≤ NumericalConductor.squareDepth h p v) :=
  selected_primeFactors b _

theorem prime_reconstruction (h : CoarseBounds F C) (a : ℕ) (ha : Squarefree a)
    (v : Fin 10 → ℤ) : a = primeLow h a v * primeHigh h a v :=
  selected_reconstruction a ha _

theorem square_reconstruction (h : CoarseBounds F C) (b : ℕ) (hb : Squarefree b)
    (v : Fin 10 → ℤ) : b = squareLow h b v * squareHigh h b v :=
  selected_reconstruction b hb _

theorem parts_dvd (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    primeLow h a v ∣ a ∧ primeHigh h a v ∣ a ∧
      squareLow h b v ∣ b ∧ squareHigh h b v ∣ b :=
  ⟨selected_dvd a _,selected_dvd a _,selected_dvd b _,selected_dvd b _⟩

theorem parts_squarefree (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) :
    Squarefree (primeLow h a v) ∧ Squarefree (primeHigh h a v) ∧
      Squarefree (squareLow h b v) ∧ Squarefree (squareHigh h b v) := by
  obtain ⟨hal,hah,hbl,hbh⟩ := parts_dvd h a b v
  exact ⟨ha.squarefree_of_dvd hal,ha.squarefree_of_dvd hah,
    hb.squarefree_of_dvd hbl,hb.squarefree_of_dvd hbh⟩

/-- All six coprimalities between the four parts are proved, including
the two complementary pairs and every pair from different original factors. -/
theorem parts_pairwise_coprime (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) :
    (primeLow h a v).Coprime (primeHigh h a v) ∧
      (squareLow h b v).Coprime (squareHigh h b v) ∧
      (primeLow h a v).Coprime (squareLow h b v) ∧
      (primeLow h a v).Coprime (squareHigh h b v) ∧
      (primeHigh h a v).Coprime (squareLow h b v) ∧
      (primeHigh h a v).Coprime (squareHigh h b v) := by
  obtain ⟨hal,hah,hbl,hbh⟩ := parts_dvd h a b v
  refine ⟨?_,?_,Nat.Coprime.of_dvd hal hbl hab,Nat.Coprime.of_dvd hal hbh hab,
    Nat.Coprime.of_dvd hah hbl hab,Nat.Coprime.of_dvd hah hbh hab⟩
  · apply Nat.coprime_of_squarefree_mul
    rw [← prime_reconstruction h a ha v]
    exact ha
  · apply Nat.coprime_of_squarefree_mul
    rw [← square_reconstruction h b hb v]
    exact hb

theorem R22_pos (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    0 < R22 h a b v := Nat.mul_pos (primeHigh_pos h a v) (squareHigh_pos h b v)

theorem R22_dvd_mul (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    R22 h a b v ∣ a*b :=
  Nat.mul_dvd_mul (parts_dvd h a b v).2.1 (parts_dvd h a b v).2.2.2

theorem R22_squarefree (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) : Squarefree (R22 h a b v) := by
  have hs := parts_squarefree h a b ha hb v
  exact (Nat.squarefree_mul (parts_pairwise_coprime h a b ha hb hab v).2.2.2.2.2).mpr
    ⟨hs.2.1,hs.2.2.2⟩

/-- Removing the actual low-depth factors leaves the conductor unchanged.
This holds even before requiring the two moduli to be squarefree. -/
theorem K_eq_high (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    NumericalConductor.K h a b v =
      NumericalConductor.K h (primeHigh h a v) (squareHigh h b v) v := by
  rw [NumericalConductor.K_eq_filtered_products, NumericalConductor.K,
    primeFactors_primeHigh, primeFactors_squareHigh]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [NumericalConductor.primeWeight,if_pos (Finset.mem_filter.mp hp).2]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [NumericalConductor.squareWeight,if_pos (Finset.mem_filter.mp hp).2]

/-- Every conductor weight from a low-depth part is exactly one. -/
theorem K_low_eq_one (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    NumericalConductor.K h (primeLow h a v) (squareLow h b v) v = 1 := by
  rw [NumericalConductor.K, primeFactors_primeLow, primeFactors_squareLow]
  have hp : (∏ p ∈ a.primeFactors.filter
      (fun p => ¬ 2 ≤ NumericalConductor.primeDepth h p v),
      NumericalConductor.primeWeight h p v) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact if_neg (Finset.mem_filter.mp hp).2
  have hs : (∏ p ∈ b.primeFactors.filter
      (fun p => ¬ 2 ≤ NumericalConductor.squareDepth h p v),
      NumericalConductor.squareWeight h p v) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact if_neg (Finset.mem_filter.mp hp).2
  rw [hp,hs,mul_one]

end CubicTenVariables.NumericalConductorRadical
