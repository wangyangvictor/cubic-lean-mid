import CubicTenVariables.NumericalConductorRadical

/-! Exact allocation by the actual numerical depths at the original integer
frequency. All seven depth levels are retained. The filters are not asserted
to be periodic in the frequency, including at prime-square moduli. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.NumericalDepthAllocation
open MvPolynomial NumericalPrimeDepth
open scoped BigOperators

variable {F : MvPolynomial (Fin 10) ℤ} {C : ℝ}

private def block (a : ℕ) (depth : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∏ p ∈ a.primeFactors with depth p = j, p

private theorem block_pos (a : ℕ) (depth : ℕ → ℕ) (j : ℕ) :
    0 < block a depth j :=
  Finset.prod_pos (fun _ hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

private theorem block_primeFactors (a : ℕ) (depth : ℕ → ℕ) (j : ℕ) :
    (block a depth j).primeFactors = a.primeFactors.filter (fun p => depth p = j) :=
  Nat.primeFactors_prod (fun _ hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

private theorem filtered_dvd (a : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (∏ p ∈ a.primeFactors with E p, p) ∣ a :=
  (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) (Finset.filter_subset _ _)).trans
    (Nat.prod_primeFactors_dvd a)

private theorem block_dvd (a : ℕ) (depth : ℕ → ℕ) (j : ℕ) :
    block a depth j ∣ a := filtered_dvd a _

private theorem block_coprime (a : ℕ) (depth : ℕ → ℕ) (i j : ℕ) (hij : i ≠ j) :
    (block a depth i).Coprime (block a depth j) := by
  rw [← Nat.disjoint_primeFactors (block_pos a depth i).ne' (block_pos a depth j).ne',
    block_primeFactors,block_primeFactors]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact hij ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

private theorem block_reconstruction (a : ℕ) (ha : Squarefree a) (depth : ℕ → ℕ)
    (hdepth : ∀ p ∈ a.primeFactors, depth p ≤ 6) :
    a = ∏ j ∈ Finset.range 7, block a depth j := by
  symm
  calc
    _ = ∏ p ∈ a.primeFactors, p := Finset.prod_fiberwise_of_maps_to
      (fun p hp => Finset.mem_range.mpr (by have := hdepth p hp; omega)) _
    _ = a := Nat.prod_primeFactors_of_squarefree ha

private theorem block_threshold (a : ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ p ∈ a.primeFactors, depth p ≤ 6) (r : ℕ) :
    (∏ j ∈ Finset.Icc r 6, block a depth j) =
      ∏ p ∈ a.primeFactors with r ≤ depth p, p := by
  simp only [block]
  rw [Finset.prod_fiberwise_eq_prod_filter]
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hp,hr,_⟩
      exact ⟨hp,hr⟩
    · rintro ⟨hp,hr⟩
      exact ⟨hp,hr,hdepth p hp⟩
  · intro p _
    rfl

private theorem prime_depth_le (h : CoarseBounds F C) (p : ℕ) (hp : p.Prime)
    (v : Fin 10 → ℤ) : NumericalConductor.primeDepth h p v ≤ 6 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [NumericalConductor.primeDepth_of_prime] using primeDepth_le_six h p v

private theorem square_depth_le (h : CoarseBounds F C) (p : ℕ) (hp : p.Prime)
    (v : Fin 10 → ℤ) : NumericalConductor.squareDepth h p v ≤ 6 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [NumericalConductor.squareDepth_of_prime] using squareDepth_le_six h p v

/-- Ordinary-prime factor with exact numerical depth j. -/
def primePart (h : CoarseBounds F C) (a : ℕ) (v : Fin 10 → ℤ) (j : ℕ) : ℕ :=
  ∏ p ∈ a.primeFactors with NumericalConductor.primeDepth h p v = j, p

/-- Square-prime factor with exact numerical depth j at the integer v. -/
def squarePart (h : CoarseBounds F C) (b : ℕ) (v : Fin 10 → ℤ) (j : ℕ) : ℕ :=
  ∏ p ∈ b.primeFactors with NumericalConductor.squareDepth h p v = j, p

/-- The merged squarefree modulus used for the depth-j congruences. -/
def mergedPart (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (j : ℕ) : ℕ :=
  primePart h a v j * squarePart h b v j

theorem parts_pos (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (j : ℕ) :
    0 < primePart h a v j ∧ 0 < squarePart h b v j :=
  ⟨block_pos a _ j,block_pos b _ j⟩

theorem parts_primeFactors (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) (j : ℕ) :
    (primePart h a v j).primeFactors =
      a.primeFactors.filter (fun p => NumericalConductor.primeDepth h p v = j) ∧
    (squarePart h b v j).primeFactors =
      b.primeFactors.filter (fun p => NumericalConductor.squareDepth h p v = j) :=
  ⟨block_primeFactors a _ j,block_primeFactors b _ j⟩

theorem parts_dvd (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (j : ℕ) :
    primePart h a v j ∣ a ∧ squarePart h b v j ∣ b :=
  ⟨block_dvd a _ j,block_dvd b _ j⟩

theorem parts_squarefree (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) (j : ℕ) :
    Squarefree (primePart h a v j) ∧ Squarefree (squarePart h b v j) :=
  ⟨ha.squarefree_of_dvd (parts_dvd h a b v j).1,
    hb.squarefree_of_dvd (parts_dvd h a b v j).2⟩

/-- All distinct-depth coprimalities within a slot and every cross-slot
coprimality. No residue invariance is used. -/
theorem parts_coprime (h : CoarseBounds F C) (a b : ℕ) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (i j : ℕ) :
    (i ≠ j → (primePart h a v i).Coprime (primePart h a v j) ∧
      (squarePart h b v i).Coprime (squarePart h b v j)) ∧
    (primePart h a v i).Coprime (squarePart h b v j) := by
  refine ⟨fun hij => ⟨block_coprime a _ i j hij,block_coprime b _ i j hij⟩,?_⟩
  exact Nat.Coprime.of_dvd (parts_dvd h a b v i).1 (parts_dvd h a b v j).2 hab

theorem merged_squarefree (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (j : ℕ) : Squarefree (mergedPart h a b v j) :=
  (Nat.squarefree_mul (parts_coprime h a b hab v j j).2).mpr
    (parts_squarefree h a b ha hb v j)

theorem merged_coprime (h : CoarseBounds F C) (a b : ℕ) (hab : a.Coprime b)
    (v : Fin 10 → ℤ) (i j : ℕ) (hij : i ≠ j) :
    (mergedPart h a b v i).Coprime (mergedPart h a b v j) := by
  have hsame := (parts_coprime h a b hab v i j).1 hij
  have hcross := (parts_coprime h a b hab v i j).2
  have hcross' := ((parts_coprime h a b hab v j i).2).symm
  simp only [mergedPart,Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  tauto

/-- Reconstruction includes depths zero and one and every depth through six. -/
theorem reconstruction (h : CoarseBounds F C) (a b : ℕ)
    (ha : Squarefree a) (hb : Squarefree b) (v : Fin 10 → ℤ) :
    a = ∏ j ∈ Finset.range 7, primePart h a v j ∧
    b = ∏ j ∈ Finset.range 7, squarePart h b v j :=
  ⟨block_reconstruction a ha _ (fun p hp => prime_depth_le h p
      (Nat.prime_of_mem_primeFactors hp) v),
    block_reconstruction b hb _ (fun p hp => square_depth_le h p
      (Nat.prime_of_mem_primeFactors hp) v)⟩

/-- A threshold product of the exact allocations is literally the original
prime filter. This also covers thresholds above six, with empty products. -/
theorem threshold_products (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) :
    (∏ j ∈ Finset.Icc r 6, primePart h a v j) =
      (∏ p ∈ a.primeFactors with r ≤ NumericalConductor.primeDepth h p v, p) ∧
    (∏ j ∈ Finset.Icc r 6, squarePart h b v j) =
      (∏ p ∈ b.primeFactors with r ≤ NumericalConductor.squareDepth h p v, p) :=
  ⟨block_threshold a _ (fun p hp => prime_depth_le h p
      (Nat.prime_of_mem_primeFactors hp) v) r,
    block_threshold b _ (fun p hp => square_depth_le h p
      (Nat.prime_of_mem_primeFactors hp) v) r⟩

theorem R22_eq_product (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) :
    NumericalConductorRadical.R22 h a b v =
      ∏ j ∈ Finset.Icc 2 6, mergedPart h a b v j := by
  rw [NumericalConductorRadical.R22_eq_filtered_products]
  simp only [mergedPart,Finset.prod_mul_distrib]
  rw [(threshold_products h a b v 2).1,(threshold_products h a b v 2).2]

/-- The actual modulus contributed by the depths at least r. -/
def deepModulus (h : CoarseBounds F C) (a b : ℕ) (v : Fin 10 → ℤ) (r : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc r 6, primePart h a v j * (squarePart h b v j)^2

theorem deepModulus_pos (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) : 0 < deepModulus h a b v r :=
  Finset.prod_pos (fun j _ => Nat.mul_pos (parts_pos h a b v j).1
    (pow_pos (parts_pos h a b v j).2 2))

theorem deepModulus_dvd (h : CoarseBounds F C) (a b : ℕ)
    (v : Fin 10 → ℤ) (r : ℕ) : deepModulus h a b v r ∣ a*b^2 := by
  rw [deepModulus,Finset.prod_mul_distrib,Finset.prod_pow,
    (threshold_products h a b v r).1,(threshold_products h a b v r).2]
  exact Nat.mul_dvd_mul (filtered_dvd a _) (pow_dvd_pow_of_dvd (filtered_dvd b _) 2)

theorem deepModulus_le (h : CoarseBounds F C) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (v : Fin 10 → ℤ) (r : ℕ) : deepModulus h a b v r ≤ a*b^2 :=
  Nat.le_of_dvd (Nat.mul_pos ha (pow_pos hb 2)) (deepModulus_dvd h a b v r)

end CubicTenVariables.NumericalDepthAllocation
