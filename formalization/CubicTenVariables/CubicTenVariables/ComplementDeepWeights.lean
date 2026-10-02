import CubicTenVariables.ComplementProfileNumerics

/-! The monomial comparisons for the middle complementary sieve terms.
The inputs are the positive dyadic scales, not an arithmetic mean estimate.
The codimensions are exactly 2,3,4,6,7 at depths 2,...,6. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementDeepWeights
open scoped BigOperators

def codim (j : ℕ) : ℝ := (j : ℝ) + if 5 ≤ j then 1 else 0

def weight (r : ℕ) (A B : ℕ → ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc r 6, (A j)^(((j : ℝ)-(r : ℝ))/2)*
    (B j)^((j : ℝ)-(r : ℝ))

def modulus (r : ℕ) (A B : ℕ → ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc r 6, A j*(B j)^2

theorem codim_values :
    codim 2 = 2 ∧ codim 3 = 3 ∧ codim 4 = 4 ∧ codim 5 = 6 ∧ codim 6 = 7 := by
  norm_num [codim]

theorem codim_gap (h j : ℕ) (hhj : h ≤ j) :
    (j : ℝ)-(h : ℝ) ≤ codim j-codim h := by
  have hhj' : (h : ℝ) ≤ j := by exact_mod_cast hhj
  simp only [codim]
  split_ifs <;> first | omega | linarith

/-- A product comparison which retains the different ordinary-prime and
prime-square exponents. -/
theorem weighted_product_le (r : ℕ) (A B e : ℕ → ℝ) (κ : ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j)
    (heA : ∀ j ∈ Finset.Icc r 6, ((j : ℝ)-(r : ℝ))/2+e j ≤ κ)
    (heB : ∀ j ∈ Finset.Icc r 6, (j : ℝ)-(r : ℝ)+e j ≤ 2*κ) :
    weight r A B * (∏ j ∈ Finset.Icc r 6, (A j*B j)^(e j)) ≤
      (modulus r A B)^κ := by
  unfold weight modulus
  rw [← Finset.prod_mul_distrib,
    ← Real.finset_prod_rpow _ _ (fun j hj => mul_nonneg (zero_le_one.trans (hA j hj))
      (sq_nonneg _))]
  apply Finset.prod_le_prod
  · intro j hj
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hA j hj)) _)
      (Real.rpow_nonneg (zero_le_one.trans (hB j hj)) _))
      (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans (hA j hj))
        (zero_le_one.trans (hB j hj))) _)
  · intro j hj
    have ha : 0 < A j := zero_lt_one.trans_le (hA j hj)
    have hb : 0 < B j := zero_lt_one.trans_le (hB j hj)
    rw [Real.mul_rpow ha.le hb.le, Real.mul_rpow ha.le (sq_nonneg _),
      ← Real.rpow_natCast_mul hb.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (A j)^(((j : ℝ)-(r : ℝ))/2+e j)*
          (B j)^((j : ℝ)-(r : ℝ)+e j) := by
        rw [Real.rpow_add ha, Real.rpow_add hb]
        ring
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow_of_exponent_le (hA j hj) (heA j hj))
        (Real.rpow_le_rpow_of_exponent_le (hB j hj) (heB j hj))
        (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _)

/-- Each term indexed by h in the sieve profile absorbs the high-depth
weight at cost E^((h-r)/2). The conditional exponents are the tail product. -/
theorem tail_weight_le (r h : ℕ) (hrh : r ≤ h) (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j) :
    weight r A B *
        (∏ j ∈ Finset.Icc r 6, (A j*B j)^(if h < j then codim h-codim j else 0)) ≤
      (modulus r A B)^(((h : ℝ)-(r : ℝ))/2) := by
  apply weighted_product_le r A B _ _ hA hB
  · intro j hj
    have hrh' : (r : ℝ) ≤ h := by exact_mod_cast hrh
    by_cases hhj : h < j
    · rw [if_pos hhj]
      have hg := codim_gap h j hhj.le
      have hhj' : (h : ℝ) ≤ j := by exact_mod_cast hhj.le
      linarith
    · rw [if_neg hhj]
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (Nat.le_of_not_gt hhj)
      linarith
  · intro j hj
    by_cases hhj : h < j
    · rw [if_pos hhj]
      have hg := codim_gap h j hhj.le
      linarith
    · rw [if_neg hhj]
      have hjh : (j : ℝ) ≤ h := by exact_mod_cast (Nat.le_of_not_gt hhj)
      linarith

theorem constant_weight_le (r : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j) :
    weight r A B ≤ (modulus r A B)^((6-(r : ℝ))/2) := by
  have ht := weighted_product_le r A B (fun _ => 0) ((6-(r : ℝ))/2) hA hB
    (fun j hj => by have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
                    linarith)
    (fun j hj => by have hj6 : (j : ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
                    linarith)
  simpa only [Real.rpow_zero,Finset.prod_const_one,mul_one] using ht

/-- For the non-open pieces the first progression term costs no weight. -/
theorem first_weight_le_one (r : ℕ) (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j) :
    weight r A B *
        (∏ j ∈ Finset.Icc r 6, (A j*B j)^(11-codim j-(11-codim r))) ≤ 1 := by
  have ht := weighted_product_le r A B (fun j => 11-codim j-(11-codim r)) 0 hA hB
    (fun j hj => by
      have hrj := (Finset.mem_Icc.mp hj).1
      have hg := codim_gap r j hrj
      have hrj' : (r : ℝ) ≤ j := by exact_mod_cast hrj
      linarith)
    (fun j hj => by have hg := codim_gap r j (Finset.mem_Icc.mp hj).1; linarith)
  simpa only [Real.rpow_zero] using ht

/-- The open piece gains the reciprocal of the product of the merged scales. -/
theorem open_weight_le_inverse (A B : ℕ → ℝ)
    (hA : ∀ j ∈ Finset.Icc 2 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc 2 6, 1 ≤ B j) :
    weight 2 A B * (∏ j ∈ Finset.Icc 2 6, (A j*B j)^(1-codim j)) ≤
      (∏ j ∈ Finset.Icc 2 6, A j*B j)⁻¹ := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro j hj
    have ha := (zero_le_one.trans (hA j hj))
    have hb := (zero_le_one.trans (hB j hj))
    positivity
  · intro j hj
    have ha : 0 < A j := zero_lt_one.trans_le (hA j hj)
    have hb : 0 < B j := zero_lt_one.trans_le (hB j hj)
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hc : (j : ℝ) ≤ codim j := by simp only [codim]; split_ifs <;> linarith
    rw [Real.mul_rpow ha.le hb.le, mul_inv_rev]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = (A j)^(((j : ℝ)-2)/2+1-codim j)*
          (B j)^((j : ℝ)-2+1-codim j) := by
        rw [show ((j : ℝ)-2)/2+1-codim j = ((j : ℝ)-2)/2+(1-codim j) by ring,
          show (j : ℝ)-2+1-codim j = (j : ℝ)-2+(1-codim j) by ring,
          Real.rpow_add ha, Real.rpow_add hb]
        ring
      _ ≤ (A j)^(-1 : ℝ)*(B j)^(-1 : ℝ) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le (hA j hj) (by linarith))
          (Real.rpow_le_rpow_of_exponent_le (hB j hj) (by linarith))
          (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _)
      _ = _ := by rw [Real.rpow_neg_one, Real.rpow_neg_one, mul_comm]

/-- The retained R22>T condition of a nonempty open block removes its extra T. -/
theorem open_first_term_le (A B : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hA : ∀ j ∈ Finset.Icc 2 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc 2 6, 1 ≤ B j)
    (hcut : T ≤ 4^5*(∏ j ∈ Finset.Icc 2 6, A j*B j)) :
    T^10*(weight 2 A B * (∏ j ∈ Finset.Icc 2 6, (A j*B j)^(1-codim j))) ≤
      4^5*T^9 := by
  let P := ∏ j ∈ Finset.Icc 2 6, A j*B j
  have hP : 0 < P := Finset.prod_pos fun j hj =>
    mul_pos (zero_lt_one.trans_le (hA j hj)) (zero_lt_one.trans_le (hB j hj))
  have hTP : T*P⁻¹ ≤ 4^5 := (mul_inv_le_iff₀ hP).mpr hcut
  calc
    _ ≤ T^10*P⁻¹ := mul_le_mul_of_nonneg_left (open_weight_le_inverse A B hA hB)
      (pow_nonneg hT _)
    _ = T^9*(T*P⁻¹) := by ring
    _ ≤ T^9*4^5 := mul_le_mul_of_nonneg_left hTP (pow_nonneg hT _)
    _ = _ := by ring

/-- A block containing an actual R22>T pair supplies the cutoff used above.
The harmless weak dyadic endpoints suffice. -/
theorem dyadic_cutoff (a b : ℕ → ℕ) (A B : ℕ → ℝ) (T : ℝ)
    (ha : ∀ j ∈ Finset.Icc 2 6, (a j : ℝ) ≤ 2*A j)
    (hb : ∀ j ∈ Finset.Icc 2 6, (b j : ℝ) ≤ 2*B j)
    (hcut : T < ∏ j ∈ Finset.Icc 2 6, (a j : ℝ)*(b j : ℝ)) :
    T ≤ 4^5*(∏ j ∈ Finset.Icc 2 6, A j*B j) := by
  apply hcut.le.trans
  calc
    _ ≤ ∏ j ∈ Finset.Icc 2 6, 4*(A j*B j) := by
      apply Finset.prod_le_prod (fun j _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      intro j hj
      have hp := mul_le_mul (ha j hj) (hb j hj) (Nat.cast_nonneg (b j))
        ((Nat.cast_nonneg (a j)).trans (ha j hj))
      nlinarith
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]; norm_num

end CubicTenVariables.ComplementDeepWeights
