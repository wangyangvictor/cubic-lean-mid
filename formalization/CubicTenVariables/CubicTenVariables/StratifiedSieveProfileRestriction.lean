import CubicTenVariables.StratifiedSieveRestriction

/-! The sieve profile changes by a fixed factor when bounded scales are
forgotten. No dimension ordering or arithmetic estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.StratifiedSieveProfileRestriction
open StratifiedSieveData StratifiedSieveRestriction
open scoped BigOperators
variable {s : ℕ}

theorem sum_index (A : Finset (Fin s)) (g : Fin s → ℝ) :
    (∑ i, g (index A i)) = ∑ i ∈ A, g i := by
  calc
    _ = ∑ i : A, g i := (A.orderIsoOfFin rfl).toEquiv.sum_comp (fun i : A => g i)
    _ = _ := Finset.sum_coe_sort A g

/-- Removing denominator factors bounded by W loses at most W^s. -/
theorem div_prod_subset_le (A : Finset (Fin s)) (g : Fin s → ℝ)
    (hg : ∀ i, 0 < g i) (W : ℝ) (hW : 1 ≤ W)
    (hsmall : ∀ i ∉ A, g i ≤ W) (x : ℝ) (hx : 0 ≤ x) :
    x/(∏ i ∈ A, g i) ≤ W^s*(x/(∏ i, g i)) := by
  classical
  have hpA : 0 < ∏ i ∈ A, g i := Finset.prod_pos (fun i _ => hg i)
  have hp : 0 < ∏ i, g i := Finset.prod_pos (fun i _ => hg i)
  have hcompl : (∏ i ∈ Aᶜ, g i) ≤ W^s := by
    calc
      _ ≤ ∏ i ∈ Aᶜ, W := Finset.prod_le_prod
        (fun i _ => (hg i).le) (fun i hi => hsmall i (Finset.mem_compl.mp hi))
      _ = W^(Aᶜ.card) := by simp
      _ ≤ W^s := pow_le_pow_right₀ hW (by simpa using Finset.card_le_univ Aᶜ)
  have he : (∏ i ∈ A, g i)*(∏ i ∈ Aᶜ, g i) = ∏ i, g i :=
    Finset.prod_mul_prod_compl A g
  have hmul : x/(∏ i ∈ A, g i) = (∏ i ∈ Aᶜ, g i)*(x/(∏ i, g i)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hp.ne').mpr
    calc
      _ = x*(∏ i ∈ Aᶜ, g i) := by rw [← he]; field_simp [hpA.ne']
      _ = _ := by ring
  rw [hmul]
  exact mul_le_mul_of_nonneg_right hcompl (div_nonneg hx hp.le)

theorem profile_nonneg (d : Fin s → ℕ) (R : Fin s → ℝ)
    (hR : ∀ i, 0 ≤ R i) (T α : ℝ) (hT : 0 ≤ T) :
    0 ≤ profile d R T α := by
  unfold profile
  apply add_nonneg
  · apply add_nonneg zero_le_one
    exact div_nonneg (Real.rpow_nonneg hT _)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hR i) _))
  · apply Finset.sum_nonneg
    intro j _
    apply div_nonneg (Real.rpow_nonneg hT _)
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact Real.rpow_nonneg (hR i) _
    · exact zero_le_one

/-- A uniform numerical comparison for every ordered subset of the same
finite table. The omitted scales lie between one and H. -/
theorem profile_le (d : Fin s → ℕ) (α H : ℝ) (hα : 0 ≤ α) (hH : 1 ≤ H)
    (A : Finset (Fin s)) (R : Fin s → ℝ) (hR : ∀ i, 1 ≤ R i)
    (hsmall : ∀ i ∉ A, R i ≤ H) (T : ℝ) (hT : 0 ≤ T) :
    profile (fun i => d (index A i)) (fun i => R (index A i)) T α ≤
      (H^(α+2*(∑ i, (d i : ℝ))+1))^s * profile d R T α := by
  classical
  let E : ℝ := α+2*(∑ i, (d i : ℝ))+1
  let W : ℝ := H^E
  have hsum : 0 ≤ ∑ i, (d i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hW : 1 ≤ W := Real.one_le_rpow hH hE
  have hWpow : 1 ≤ W^s := one_le_pow₀ hW
  have hd (j : Fin s) : (d j : ℝ) ≤ ∑ i, (d i : ℝ) :=
    Finset.single_le_sum (fun i _ => Nat.cast_nonneg _) (Finset.mem_univ j)
  have hrpow (i : Fin s) (hi : i ∉ A) (e : ℝ) (he : e ≤ E) : (R i)^e ≤ W := by
    calc
      _ ≤ (R i)^E := Real.rpow_le_rpow_of_exponent_le (hR i) he
      _ ≤ H^E := Real.rpow_le_rpow (zero_le_one.trans (hR i)) (hsmall i hi) hE
  have hfirst : T^α/(∏ i, (R (index A i))^(α-(d (index A i) : ℝ)-1)) ≤
      W^s*(T^α/(∏ i, (R i)^(α-(d i : ℝ)-1))) := by
    rw [prod_index A (fun i => (R i)^(α-(d i : ℝ)-1))]
    apply div_prod_subset_le A _ (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans_le (hR i)) _) W hW
      (fun i hi => hrpow i hi _ (by dsimp [E]; nlinarith [(Nat.cast_nonneg (d i) : (0 : ℝ) ≤ d i)])) _
      (Real.rpow_nonneg hT _)
  let term (j : Fin s) : ℝ := T^((d j : ℝ)+1)/
    (∏ i, if j < i then (R i)^((d j : ℝ)-(d i : ℝ)) else 1)
  have hterm0 (j : Fin s) : 0 ≤ term j := by
    apply div_nonneg (Real.rpow_nonneg hT _)
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact Real.rpow_nonneg (zero_le_one.trans (hR i)) _
    · exact zero_le_one
  have hterm (j : Fin A.card) :
      T^((d (index A j) : ℝ)+1)/
        (∏ i, if j < i then (R (index A i))^
          ((d (index A j) : ℝ)-(d (index A i) : ℝ)) else 1) ≤ W^s*term (index A j) := by
    have hden : (∏ i, if j < i then (R (index A i))^
        ((d (index A j) : ℝ)-(d (index A i) : ℝ)) else 1) =
        ∏ i ∈ A, if index A j < i then (R i)^((d (index A j) : ℝ)-(d i : ℝ)) else 1 := by
      rw [← prod_index A (fun i => if index A j < i then
        (R i)^((d (index A j) : ℝ)-(d i : ℝ)) else 1)]
      apply Finset.prod_congr rfl
      intro i _
      simp only [(index A).lt_iff_lt]
    rw [hden]
    apply div_prod_subset_le A _ ?_ W hW ?_ _ (Real.rpow_nonneg hT _)
    · intro i
      split_ifs
      · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le (hR i)) _
      · exact zero_lt_one
    · intro i hi
      split_ifs
      · apply hrpow i hi
        dsimp [E]
        nlinarith [hd (index A j),(Nat.cast_nonneg (d i) : (0 : ℝ) ≤ d i)]
      · exact hW
  have hterms : (∑ j, T^((d (index A j) : ℝ)+1)/
      (∏ i, if j < i then (R (index A i))^
        ((d (index A j) : ℝ)-(d (index A i) : ℝ)) else 1)) ≤ W^s*∑ j, term j := by
    calc
      _ ≤ ∑ j, W^s*term (index A j) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = W^s*(∑ j ∈ A, term j) := by rw [← Finset.mul_sum,sum_index]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun j _ _ => hterm0 j))
        (zero_le_one.trans hWpow)
  change 1+_+_ ≤ W^s*profile d R T α
  unfold profile
  dsimp only [term] at hterms
  nlinarith

end CubicTenVariables.StratifiedSieveProfileRestriction
