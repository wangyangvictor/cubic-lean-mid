import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Numerical assembly for finitely many dyadic counting blocks. Natural
logarithmic block counts are absorbed into half of a positive power saving.
The scalar delta-method order is selected before the counting scales.
Every assertion here is elementary and has no literature premise. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GlobalCountingNumerics

/-- A pointwise logarithm estimate, so no eventual threshold is needed. -/
theorem affine_log_le (P ε a : ℝ) (hP : 1 ≤ P) (hε : 0 < ε) (ha : 0 ≤ a) :
    1+a*Real.log P ≤ (1+a/ε)*P^ε := by
  have hp := Real.one_le_rpow hP hε.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hP) hε
  calc
    _ ≤ P^ε+a*(P^ε/ε) := add_le_add hp (mul_le_mul_of_nonneg_left hl ha)
    _ = _ := by ring

/-- A natural logarithmic index count for an integer at most P^t. -/
theorem nat_log_succ_le (m : ℕ) (P t : ℝ) (hm : 0 < m)
    (hP : 1 ≤ P) (ht : 0 ≤ t) (hmP : (m:ℝ) ≤ P^t) :
    ((Nat.log 2 m+1:ℕ):ℝ) ≤ (1+t/Real.log 2)*(1+Real.log P) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hl := Real.log_le_log hm0 hmP
  rw [Real.log_rpow hP0] at hl
  have hn : (Nat.log 2 m:ℝ) ≤ t*Real.log P/Real.log 2 := by
    apply (show (Nat.log 2 m:ℝ) ≤ Real.log (m:ℝ)/Real.log 2 by
      simpa only [Real.logb,Nat.cast_ofNat] using Real.natLog_le_logb m 2).trans
    exact div_le_div_of_nonneg_right hl hl2.le
  have hn' : (Nat.log 2 m:ℝ) ≤ (t/Real.log 2)*Real.log P := by
    calc
      _ ≤ t*Real.log P/Real.log 2 := hn
      _ = _ := by ring
  have ht2 : 0 ≤ t/Real.log 2 := div_nonneg ht hl2.le
  push_cast
  nlinarith

/-- Any two fixed affine logarithmic factors consume at most half the
given saving; the constant precedes every scale P. -/
theorem exists_affine_log_absorption (δ a b : ℝ) (hδ : 0 < δ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : ℝ, 1 ≤ P →
      (1+a*Real.log P)*(1+b*Real.log P)*P^(7-δ) ≤ C*P^(7-δ/2) := by
  let ε : ℝ := δ/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let C : ℝ := (1+a/ε)*(1+b/ε)
  have hCa : 1 ≤ 1+a/ε := le_add_of_nonneg_right (div_nonneg ha hε.le)
  have hCb : 1 ≤ 1+b/ε := le_add_of_nonneg_right (div_nonneg hb hε.le)
  refine ⟨C,one_le_mul_of_one_le_of_one_le hCa hCb,?_⟩
  intro P hP
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
  have hf : (1+a*Real.log P)*(1+b*Real.log P) ≤ C*(P^ε*P^ε) := by
    calc
      _ ≤ ((1+a/ε)*P^ε)*((1+b/ε)*P^ε) :=
        mul_le_mul (affine_log_le P ε a hP hε ha) (affine_log_le P ε b hP hε hb)
          (by positivity) (by positivity)
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ (C*(P^ε*P^ε))*P^(7-δ) := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = C*P^(7-δ/2) := by
      rw [mul_assoc,← Real.rpow_add hP0,← Real.rpow_add hP0]
      congr 2
      dsimp [ε]
      ring

/-- The exact two range sizes used by the finite dyadic cover. -/
theorem dyadic_count_le_log_square (P Q : ℕ) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hQP : (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2)) :
    (((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1):ℕ):ℝ) ≤
      ((1+((3:ℝ)/2)/Real.log 2)*(1+20/Real.log 2))*(1+Real.log (P:ℝ))^2 := by
  have hPr : (1:ℝ) ≤ P := by exact_mod_cast hP
  have hQcount := nat_log_succ_le Q (P:ℝ) ((3:ℝ)/2) hQ hPr (by norm_num) hQP
  have hPpow : 0 < P^20 := pow_pos (by omega) _
  have hKcount := nat_log_succ_le (P^20) (P:ℝ) 20 hPpow hPr (by norm_num)
    (by norm_cast)
  rw [Nat.cast_mul]
  calc
    _ ≤ ((1+((3:ℝ)/2)/Real.log 2)*(1+Real.log (P:ℝ)))*
        ((1+20/Real.log 2)*(1+Real.log (P:ℝ))) :=
      mul_le_mul hQcount hKcount (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- Uniform absorption of the literal dyadic block count into a genuine
power saving. This holds already for every positive natural P. -/
theorem exists_dyadic_count_absorption (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
      (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) →
      (((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1):ℕ):ℝ)*(P:ℝ)^(7-δ) ≤
        C*(P:ℝ)^(7-δ/2) := by
  let B : ℝ := (1+((3:ℝ)/2)/Real.log 2)*(1+20/Real.log 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 1 ≤ B := by
    exact one_le_mul_of_one_le_of_one_le
      (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
  obtain ⟨C,hC,habs⟩ := exists_affine_log_absorption δ 1 1 hδ (by norm_num) (by norm_num)
  refine ⟨B*C,one_le_mul_of_one_le_of_one_le hB hC,?_⟩
  intro P Q hP hQ hQP
  have hPr : (1:ℝ) ≤ P := by exact_mod_cast hP
  calc
    _ ≤ (B*(1+Real.log (P:ℝ))^2)*(P:ℝ)^(7-δ) :=
      mul_le_mul_of_nonneg_right (dyadic_count_le_log_square P Q hP hQ hQP) (by positivity)
    _ = B*((1+1*Real.log (P:ℝ))*(1+1*Real.log (P:ℝ))*(P:ℝ)^(7-δ)) := by ring
    _ ≤ B*(C*(P:ℝ)^(7-δ/2)) :=
      mul_le_mul_of_nonneg_left (habs (P:ℝ) hPr) (zero_le_one.trans hB)
    _ = _ := by ring

/-- The additional modulus-one block is included in this actual total
count: (J+1) phase families, each with K shells. -/
theorem exists_global_block_absorption (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
      (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2) →
      (((Nat.log 2 Q+2)*(Nat.log 2 (P^20)+1):ℕ):ℝ)*(P:ℝ)^(7-δ) ≤
        C*(P:ℝ)^(7-δ/2) := by
  obtain ⟨C,hC,h⟩ := exists_dyadic_count_absorption δ hδ
  refine ⟨2*C,by linarith,?_⟩
  intro P Q hP hQ hQP
  have hn : (Nat.log 2 Q+2)*(Nat.log 2 (P^20)+1) ≤
      2*((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1)) := by
    have hq : Nat.log 2 Q+2 ≤ 2*(Nat.log 2 Q+1) := by omega
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (Nat.log 2 (P^20)+1) hq
  have hr : (((Nat.log 2 Q+2)*(Nat.log 2 (P^20)+1):ℕ):ℝ) ≤
      2*(((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1):ℕ):ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (2*(((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1):ℕ):ℝ))*(P:ℝ)^(7-δ) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = 2*((((Nat.log 2 Q+1)*(Nat.log 2 (P^20)+1):ℕ):ℝ)*(P:ℝ)^(7-δ)) := by ring
    _ ≤ 2*(C*(P:ℝ)^(7-δ/2)) := mul_le_mul_of_nonneg_left (h P Q hP hQ hQP) (by norm_num)
    _ = _ := by ring

/-- A single natural truncation order, chosen before P and Q, makes the
ten-variable scalar delta-method error decay by any prescribed power. -/
theorem exists_delta_order (η A : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ P Q : ℝ, 1 ≤ P → Q=P^((3:ℝ)/2) →
      P^10*Q^(-(N:ℝ)*η) ≤ P^(-A) := by
  have hd : 0 < (3:ℝ)/2*η := by positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (max 1 ((10+A)/((3:ℝ)/2*η)))
  have hN1 : (1:ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNA : (10+A)/((3:ℝ)/2*η) ≤ N := (le_max_right _ _).trans hN
  refine ⟨N,by exact_mod_cast hN1,?_⟩
  intro P Q hP hQ
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have he : (10:ℝ)+(3/2)*(-(N:ℝ)*η) ≤ -A := by
    have h := (div_le_iff₀ hd).mp hNA
    nlinarith
  rw [hQ,← Real.rpow_mul hP0.le,← Real.rpow_natCast P 10,← Real.rpow_add hP0]
  exact Real.rpow_le_rpow_of_exponent_le hP he

end CubicTenVariables.GlobalCountingNumerics
