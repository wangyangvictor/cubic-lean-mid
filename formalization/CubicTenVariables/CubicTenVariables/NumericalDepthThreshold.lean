import CubicTenVariables.NumericalDepthAllocation
import CubicTenVariables.CompleteSumMultiplicativity

/-! Exact low/high splitting at any actual numerical-depth threshold.
The integer frequency is retained throughout; no depth periodicity is asserted. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalDepthThreshold
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

def primeHigh (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) (r : ℕ) : ℕ :=
  selected a (fun p => r ≤ NumericalConductor.primeDepth h p v)

def primeLow (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) (r : ℕ) : ℕ :=
  selected a (fun p => ¬ r ≤ NumericalConductor.primeDepth h p v)

def squareHigh (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) : ℕ :=
  selected b (fun p => r ≤ NumericalConductor.squareDepth h p v)

def squareLow (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) : ℕ :=
  selected b (fun p => ¬ r ≤ NumericalConductor.squareDepth h p v)

theorem parts_pos (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) :
    0 < primeLow h a v r ∧ 0 < primeHigh h a v r ∧
      0 < squareLow h b v r ∧ 0 < squareHigh h b v r :=
  ⟨selected_pos a _,selected_pos a _,selected_pos b _,selected_pos b _⟩

@[simp] theorem primeFactors_primeHigh (h : CoarseBounds F C) (a : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (primeHigh h a v r).primeFactors =
      a.primeFactors.filter (fun p => r ≤ NumericalConductor.primeDepth h p v) := by
  simpa only [primeLow, squareLow, Nat.not_le] using selected_primeFactors a
    (fun p => r ≤ NumericalConductor.primeDepth h p v)

@[simp] theorem primeFactors_primeLow (h : CoarseBounds F C) (a : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (primeLow h a v r).primeFactors =
      a.primeFactors.filter (fun p => NumericalConductor.primeDepth h p v < r) := by
  simpa only [primeLow, squareLow, Nat.not_le] using selected_primeFactors a
    (fun p => ¬ r ≤ NumericalConductor.primeDepth h p v)

@[simp] theorem primeFactors_squareHigh (h : CoarseBounds F C) (b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (squareHigh h b v r).primeFactors =
      b.primeFactors.filter (fun p => r ≤ NumericalConductor.squareDepth h p v) := by
  simpa only [primeLow, squareLow, Nat.not_le] using selected_primeFactors b
    (fun p => r ≤ NumericalConductor.squareDepth h p v)

@[simp] theorem primeFactors_squareLow (h : CoarseBounds F C) (b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (squareLow h b v r).primeFactors =
      b.primeFactors.filter (fun p => NumericalConductor.squareDepth h p v < r) := by
  simpa only [primeLow, squareLow, Nat.not_le] using selected_primeFactors b
    (fun p => ¬ r ≤ NumericalConductor.squareDepth h p v)

theorem prime_reconstruction (h : CoarseBounds F C) (a : ℕ) (ha : Squarefree a)
    (v : Fin 10 → ℤ) (r : ℕ) : a = primeLow h a v r * primeHigh h a v r :=
  selected_reconstruction a ha _

theorem square_reconstruction (h : CoarseBounds F C) (b : ℕ) (hb : Squarefree b)
    (v : Fin 10 → ℤ) (r : ℕ) : b = squareLow h b v r * squareHigh h b v r :=
  selected_reconstruction b hb _

theorem parts_dvd (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) :
    primeLow h a v r ∣ a ∧ primeHigh h a v r ∣ a ∧
      squareLow h b v r ∣ b ∧ squareHigh h b v r ∣ b :=
  ⟨selected_dvd a _,selected_dvd a _,selected_dvd b _,selected_dvd b _⟩

theorem parts_squarefree (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) (r : ℕ) :
    Squarefree (primeLow h a v r) ∧ Squarefree (primeHigh h a v r) ∧
      Squarefree (squareLow h b v r) ∧ Squarefree (squareHigh h b v r) := by
  obtain ⟨hal,hah,hbl,hbh⟩ := parts_dvd h a b v r
  exact ⟨ha.squarefree_of_dvd hal,ha.squarefree_of_dvd hah,
    hb.squarefree_of_dvd hbl,hb.squarefree_of_dvd hbh⟩

/-- Complementary pairs and all four cross-slot pairs are coprime. -/
theorem parts_pairwise_coprime (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (primeLow h a v r).Coprime (primeHigh h a v r) ∧
      (squareLow h b v r).Coprime (squareHigh h b v r) ∧
      (primeLow h a v r).Coprime (squareLow h b v r) ∧
      (primeLow h a v r).Coprime (squareHigh h b v r) ∧
      (primeHigh h a v r).Coprime (squareLow h b v r) ∧
      (primeHigh h a v r).Coprime (squareHigh h b v r) := by
  obtain ⟨hal,hah,hbl,hbh⟩ := parts_dvd h a b v r
  refine ⟨?_,?_,Nat.Coprime.of_dvd hal hbl hab,Nat.Coprime.of_dvd hal hbh hab,
    Nat.Coprime.of_dvd hah hbl hab,Nat.Coprime.of_dvd hah hbh hab⟩
  · apply Nat.coprime_of_squarefree_mul
    rw [← prime_reconstruction h a ha v r]
    exact ha
  · apply Nat.coprime_of_squarefree_mul
    rw [← square_reconstruction h b hb v r]
    exact hb

theorem high_eq_products (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    primeHigh h a v r = ∏ j ∈ Finset.Icc r 6, NumericalDepthAllocation.primePart h a v j ∧
    squareHigh h b v r = ∏ j ∈ Finset.Icc r 6, NumericalDepthAllocation.squarePart h b v j :=
  ⟨(NumericalDepthAllocation.threshold_products h a b v r).1.symm,
    (NumericalDepthAllocation.threshold_products h a b v r).2.symm⟩

theorem low_high_coprime (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (primeLow h a v r * (squareLow h b v r)^2).Coprime
      (primeHigh h a v r * (squareHigh h b v r)^2) := by
  obtain ⟨h1,h2,_,h4,h5,_⟩ := parts_pairwise_coprime h a b ha hb hab v r
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨h1,h4.pow_right 2⟩,
      Nat.coprime_mul_iff_right.mpr ⟨h5.symm.pow_left 2,(h2.pow_left 2).pow_right 2⟩⟩

theorem modulus_reconstruction (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) (r : ℕ) :
    a*b^2 = (primeLow h a v r * (squareLow h b v r)^2) *
      (primeHigh h a v r * (squareHigh h b v r)^2) := by
  calc
    a*b^2 = (primeLow h a v r * primeHigh h a v r) *
        (squareLow h b v r * squareHigh h b v r)^2 := by
      rw [← prime_reconstruction h a ha v r,← square_reconstruction h b hb v r]
    _ = _ := by ring

theorem norm_split (h : CoarseBounds F C) (hF : F.IsHomogeneous 3)
    (a b : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (r : ℕ) :
    ‖completeCubicSum F (a*b^2) v‖ =
      ‖completeCubicSum F (primeLow h a v r * (squareLow h b v r)^2) v‖ *
      ‖completeCubicSum F (primeHigh h a v r * (squareHigh h b v r)^2) v‖ := by
  rw [modulus_reconstruction h a b ha hb v r]
  exact CompleteSumMultiplicativity.norm_mul F hF _ _
    (low_high_coprime h a b ha hb hab v r) v

end CubicTenVariables.NumericalDepthThreshold
