import CubicTenVariables.ComplementDeepWeights

/-! The complete numerical profile of a retained middle complementary block.
This is a bound for its right-hand side; counting and dyadic summation are
separate arithmetic obligations. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementDeepProfile
open ComplementDeepWeights
open scoped BigOperators

def exponent (r : ℕ) : ℝ := if r=2 then 10 else 11-codim r

def profile (r : ℕ) (A B : ℕ → ℝ) (T : ℝ) : ℝ :=
  1+T^(exponent r)*(∏ j ∈ Finset.Icc r 6, (A j*B j)^(11-codim j-exponent r))+
    ∑ h ∈ Finset.Icc r 6, T^(11-codim h)*
      (∏ j ∈ Finset.Icc r 6, (A j*B j)^(if h < j then codim h-codim j else 0))

def table (D T : ℝ) : ℝ :=
  ∑ h ∈ Finset.Icc 2 6, T^(11-codim h)*D^((11+(h : ℝ))/2)

theorem modulus_term_le (r h : ℕ) (hr : 2 ≤ r) (hrh : r ≤ h) (hh : h ≤ 6)
    (D E : ℝ) (hD : 1 ≤ D) (hE : 0 ≤ E) (hED : E ≤ 2*D) :
    D^((11+(r : ℝ))/2)*E^(((h : ℝ)-(r : ℝ))/2) ≤
      4*D^((11+(h : ℝ))/2) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrh' : (r : ℝ) ≤ h := by exact_mod_cast hrh
  have hh' : (h : ℝ) ≤ 6 := by exact_mod_cast hh
  have hκ : 0 ≤ ((h : ℝ)-(r : ℝ))/2 := by linarith
  have hκ2 : ((h : ℝ)-(r : ℝ))/2 ≤ 2 := by linarith
  have htwo : (2 : ℝ)^(((h : ℝ)-(r : ℝ))/2) ≤ 4 := by
    have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hκ2
    norm_num at ht ⊢
    exact ht
  calc
    _ ≤ D^((11+(r : ℝ))/2)*(2*D)^(((h : ℝ)-(r : ℝ))/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hED hκ) (Real.rpow_nonneg hD0.le _)
    _ = (2 : ℝ)^(((h : ℝ)-(r : ℝ))/2)*D^((11+(h : ℝ))/2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD0.le]
      calc
        _ = (2 : ℝ)^(((h : ℝ)-(r : ℝ))/2)*
            (D^((11+(r : ℝ))/2)*D^(((h : ℝ)-(r : ℝ))/2)) := by ring
        _ = _ := by rw [← Real.rpow_add hD0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD0.le _)

private theorem table_term_le (D T : ℝ) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (h : ℕ) (hh : h ∈ Finset.Icc 2 6) :
    T^(11-codim h)*D^((11+(h : ℝ))/2) ≤ table D T := by
  unfold table
  exact Finset.single_le_sum (fun j _ => mul_nonneg (Real.rpow_nonneg hT (11-codim j))
    (Real.rpow_nonneg hD ((11+(j : ℝ))/2))) hh

/-- The same five table terms control every retained block. The factor
1032 absorbs the bounded dyadic loss of the open piece and the constant term. -/
theorem weighted_profile_le (r : ℕ) (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (A B : ℕ → ℝ) (D T : ℝ) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j)
    (hED : modulus r A B ≤ 2*D)
    (hcut : r=2 → T ≤ 4^5*(∏ j ∈ Finset.Icc 2 6, A j*B j)) :
    D^((11+(r : ℝ))/2)*weight r A B*profile r A B T ≤ 1032*table D T := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hW0 : 0 ≤ weight r A B := Finset.prod_nonneg fun j hj =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hA j hj)) _)
      (Real.rpow_nonneg (zero_le_one.trans (hB j hj)) _)
  have hE0 : 0 ≤ modulus r A B := Finset.prod_nonneg fun j hj =>
    mul_nonneg (zero_le_one.trans (hA j hj)) (sq_nonneg _)
  have htable : 0 ≤ table D T := Finset.sum_nonneg fun j _ =>
    mul_nonneg (Real.rpow_nonneg hT0 _) (Real.rpow_nonneg hD0 _)
  have hconst : D^((11+(r : ℝ))/2)*weight r A B ≤ 4*table D T := by
    calc
      _ ≤ D^((11+(r : ℝ))/2)*(modulus r A B)^((6-(r : ℝ))/2) :=
        mul_le_mul_of_nonneg_left (constant_weight_le r A B hA hB) (Real.rpow_nonneg hD0 _)
      _ ≤ 4*D^((11+(6 : ℝ))/2) := by
        simpa only [Nat.cast_ofNat] using modulus_term_le r 6 hr hr6 (by decide)
          D (modulus r A B) hD hE0 hED
      _ ≤ 4*(T^(11-codim 6)*D^((11+(6 : ℝ))/2)) := by
        have ht : 1 ≤ T^(11-codim 6) := Real.one_le_rpow hT (by norm_num [codim])
        nlinarith [Real.rpow_nonneg hD0 ((11+(6 : ℝ))/2)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [Nat.cast_ofNat] using table_term_le D T hD0 hT0 6 (by decide)) (by norm_num)
  have hfirst : D^((11+(r : ℝ))/2)*weight r A B*
      (T^(exponent r)*(∏ j ∈ Finset.Icc r 6, (A j*B j)^(11-codim j-exponent r))) ≤
        1024*table D T := by
    by_cases hr2 : r=2
    · subst r
      have hop := open_first_term_le A B T hT0 hA hB (hcut rfl)
      calc
        _ = D^((11+(2 : ℝ))/2)*(T^10*(weight 2 A B*
            (∏ j ∈ Finset.Icc 2 6, (A j*B j)^(1-codim j)))) := by
          norm_num only [exponent, ite_true, Nat.cast_ofNat, Real.rpow_ofNat]
          try simp_rw [show ∀ j, (11-codim j-10 : ℝ)=1-codim j from fun j => by ring]
          ring
        _ ≤ D^((11+(2 : ℝ))/2)*(4^5*T^9) :=
          mul_le_mul_of_nonneg_left hop (Real.rpow_nonneg hD0 _)
        _ = 1024*(T^(11-codim 2)*D^((11+(2 : ℝ))/2)) := by norm_num [codim]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (by simpa only [Nat.cast_ofNat] using table_term_le D T hD0 hT0 2 (by decide)) (by norm_num)
    · have hfirst0 := first_weight_le_one r A B hA hB
      have he : exponent r=11-codim r := if_neg hr2
      rw [he]
      calc
        _ = (T^(11-codim r)*D^((11+(r : ℝ))/2))*
            (weight r A B*(∏ j ∈ Finset.Icc r 6, (A j*B j)^(11-codim j-(11-codim r)))) := by ring
        _ ≤ (T^(11-codim r)*D^((11+(r : ℝ))/2))*1 :=
          mul_le_mul_of_nonneg_left hfirst0 (by positivity)
        _ ≤ table D T := by rw [mul_one]; exact table_term_le D T hD0 hT0 r (Finset.mem_Icc.mpr ⟨hr,hr6⟩)
        _ ≤ _ := by nlinarith
  have hterms : D^((11+(r : ℝ))/2)*weight r A B*
      (∑ h ∈ Finset.Icc r 6, T^(11-codim h)*
        (∏ j ∈ Finset.Icc r 6, (A j*B j)^(if h < j then codim h-codim j else 0))) ≤
      4*table D T := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ h ∈ Finset.Icc r 6, 4*(T^(11-codim h)*D^((11+(h : ℝ))/2)) := by
        apply Finset.sum_le_sum
        intro h hh
        have htw := tail_weight_le r h (Finset.mem_Icc.mp hh).1 A B hA hB
        have hmod := modulus_term_le r h hr (Finset.mem_Icc.mp hh).1
          (Finset.mem_Icc.mp hh).2 D (modulus r A B) hD hE0 hED
        calc
          _ = T^(11-codim h)*(D^((11+(r : ℝ))/2)*(weight r A B*
              (∏ j ∈ Finset.Icc r 6, (A j*B j)^(if h < j then codim h-codim j else 0)))) := by ring
          _ ≤ T^(11-codim h)*(D^((11+(r : ℝ))/2)*(modulus r A B)^(((h : ℝ)-(r : ℝ))/2)) := by
            gcongr
          _ ≤ T^(11-codim h)*(4*D^((11+(h : ℝ))/2)) :=
            mul_le_mul_of_nonneg_left hmod (Real.rpow_nonneg hT0 _)
          _ = _ := by ring
      _ = 4*(∑ h ∈ Finset.Icc r 6, T^(11-codim h)*D^((11+(h : ℝ))/2)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc hr (le_refl 6))
          (fun j _ _ => mul_nonneg (Real.rpow_nonneg hT0 _) (Real.rpow_nonneg hD0 _))) (by norm_num)
  unfold profile
  nlinarith

theorem table_eq (D T : ℝ) :
    table D T = T^9*D^((13 : ℝ)/2)+T^8*D^7+T^7*D^((15 : ℝ)/2)+
      T^5*D^8+T^4*D^((17 : ℝ)/2) := by
  norm_num [table, Finset.sum_Icc_succ_top, codim]

theorem table_le (D T : ℝ) (hD : 1 ≤ D) (hT : 1 ≤ T) :
    table D T ≤ 6*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9) := by
  rw [table_eq]
  have ht := ComplementProfileNumerics.table_le D T hD hT
  have hTD : 0 ≤ T*D^9 := mul_nonneg (zero_le_one.trans hT) (pow_nonneg (zero_le_one.trans hD) _)
  linarith

/-- The entire weighted profile has the required complementary shape. -/
theorem weighted_profile_final_le (r : ℕ) (hr : 2 ≤ r) (hr6 : r ≤ 6)
    (A B : ℕ → ℝ) (D T : ℝ) (hD : 1 ≤ D) (hT : 1 ≤ T)
    (hA : ∀ j ∈ Finset.Icc r 6, 1 ≤ A j)
    (hB : ∀ j ∈ Finset.Icc r 6, 1 ≤ B j)
    (hED : modulus r A B ≤ 2*D)
    (hcut : r=2 → T ≤ 4^5*(∏ j ∈ Finset.Icc 2 6, A j*B j)) :
    D^((11+(r : ℝ))/2)*weight r A B*profile r A B T ≤
      6192*D^((59 : ℝ)/6)*(T/D^((1 : ℝ)/3)+(T/D^((1 : ℝ)/3))^9) := by
  have hw := weighted_profile_le r hr hr6 A B D T hD hT hA hB hED hcut
  have ht := mul_le_mul_of_nonneg_left (table_le D T hD hT) (by norm_num : (0 : ℝ) ≤ 1032)
  exact hw.trans (by convert ht using 1; ring)

end CubicTenVariables.ComplementDeepProfile
