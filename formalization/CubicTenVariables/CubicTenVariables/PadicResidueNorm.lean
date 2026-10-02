import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic

/-!
# Congruences and p-adic distances

Reduction modulo `p^s` is expressed by the literal `PadicInt.toZModPow s` map.
The radius is the inverse of the natural power `(p : ℝ)^s`, so every statement
includes level zero. Finite products use their actual maximum norm. The final
lemmas turn a displayed lower-distance estimate into congruence at level `s-A`;
no local inverse estimate or finite-fibre estimate is assumed implicitly.
-/

namespace CubicTenVariables.PadicResidueNorm

open scoped NNReal

variable {p : ℕ} [Fact p.Prime]

/-- Equality modulo `p^s` is exactly the closed p-adic distance bound. -/
theorem toZModPow_eq_iff_norm_sub_le (s : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow s x = PadicInt.toZModPow s y ↔
      ‖x - y‖ ≤ ((p : ℝ) ^ s)⁻¹ := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simp only [zpow_neg, zpow_natCast]

/-- The same equivalence with literal coercions to the p-adic field. -/
theorem toZModPow_eq_iff_norm_coe_sub_le (s : ℕ) (x y : ℤ_[p]) :
    PadicInt.toZModPow s x = PadicInt.toZModPow s y ↔
      ‖(x : ℚ_[p]) - (y : ℚ_[p])‖ ≤ ((p : ℝ) ^ s)⁻¹ := by
  simpa only [PadicInt.norm_def, PadicInt.coe_sub] using
    toZModPow_eq_iff_norm_sub_le s x y

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Coordinatewise congruence is exactly the finite-product distance bound. -/
theorem pi_toZModPow_eq_iff_norm_sub_le (s : ℕ) (x y : ι → ℤ_[p]) :
    (∀ i, PadicInt.toZModPow s (x i) = PadicInt.toZModPow s (y i)) ↔
      ‖x - y‖ ≤ ((p : ℝ) ^ s)⁻¹ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  exact forall_congr' fun i => toZModPow_eq_iff_norm_sub_le s (x i) (y i)

/-- Coordinatewise congruence measured in the finite product of p-adic fields. -/
theorem pi_toZModPow_eq_iff_norm_coe_sub_le (s : ℕ) (x y : ι → ℤ_[p]) :
    (∀ i, PadicInt.toZModPow s (x i) = PadicInt.toZModPow s (y i)) ↔
      ‖(fun i => (x i : ℚ_[p])) - (fun i => (y i : ℚ_[p]))‖ ≤
        ((p : ℝ) ^ s)⁻¹ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  exact forall_congr' fun i => toZModPow_eq_iff_norm_coe_sub_le s (x i) (y i)

/-- Two finite blocks of congruences correspond to their product maximum norm. -/
theorem prod_pi_toZModPow_eq_iff_norm_sub_le (s : ℕ)
    (x y : ι → ℤ_[p]) (u v : κ → ℤ_[p]) :
    ((∀ i, PadicInt.toZModPow s (x i) = PadicInt.toZModPow s (y i)) ∧
      (∀ j, PadicInt.toZModPow s (u j) = PadicInt.toZModPow s (v j))) ↔
      ‖(x, u) - (y, v)‖ ≤ ((p : ℝ) ^ s)⁻¹ := by
  change _ ↔ max ‖x - y‖ ‖u - v‖ ≤ _
  rw [max_le_iff, ← pi_toZModPow_eq_iff_norm_sub_le,
    ← pi_toZModPow_eq_iff_norm_sub_le]

/-- The two-block equivalence after literal coercion into the p-adic field. -/
theorem prod_pi_toZModPow_eq_iff_norm_coe_sub_le (s : ℕ)
    (x y : ι → ℤ_[p]) (u v : κ → ℤ_[p]) :
    ((∀ i, PadicInt.toZModPow s (x i) = PadicInt.toZModPow s (y i)) ∧
      (∀ j, PadicInt.toZModPow s (u j) = PadicInt.toZModPow s (v j))) ↔
      ‖((fun i => (x i : ℚ_[p])), (fun j => (u j : ℚ_[p]))) -
        ((fun i => (y i : ℚ_[p])), (fun j => (v j : ℚ_[p])))‖ ≤
          ((p : ℝ) ^ s)⁻¹ := by
  change _ ↔ max ‖(fun i => (x i : ℚ_[p])) - (fun i => (y i : ℚ_[p]))‖
    ‖(fun j => (u j : ℚ_[p])) - (fun j => (v j : ℚ_[p]))‖ ≤ _
  rw [max_le_iff, ← pi_toZModPow_eq_iff_norm_coe_sub_le,
    ← pi_toZModPow_eq_iff_norm_coe_sub_le]

/-- Coercion of integral vectors preserves their actual maximum distance. -/
theorem norm_pi_coe_sub (x y : ι → ℤ_[p]) :
    ‖(fun i => (x i : ℚ_[p])) - (fun i => (y i : ℚ_[p]))‖ = ‖x - y‖ := rfl

/-- A difference of integral vectors has maximum norm at most one. -/
theorem norm_pi_sub_le_one (x y : ι → ℤ_[p]) : ‖x - y‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  exact fun i => PadicInt.norm_le_one (x i - y i)

/-- Elementary truncation of the congruence level, including `s < A`. -/
theorem le_inv_pow_sub_of_le_one_of_le_mul_inv_pow (b : ℝ) (A s : ℕ)
    (hb_one : b ≤ 1) (hb : b ≤ (p : ℝ) ^ A * ((p : ℝ) ^ s)⁻¹) :
    b ≤ ((p : ℝ) ^ (s - A))⁻¹ := by
  by_cases hAs : A ≤ s
  · have hp : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hpow : (p : ℝ) ^ s = (p : ℝ) ^ A * (p : ℝ) ^ (s - A) := by
      rw [← pow_add, Nat.add_sub_of_le hAs]
    have he : (p : ℝ) ^ A * ((p : ℝ) ^ s)⁻¹ = ((p : ℝ) ^ (s - A))⁻¹ := by
      rw [hpow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero A hp), one_mul]
    exact he ▸ hb
  · simpa only [Nat.sub_eq_zero_of_le (le_of_lt (Nat.lt_of_not_ge hAs)), pow_zero,
      inv_one] using hb_one

/-- A distance loss at most `p^A` costs at most `A` digits of congruence. -/
theorem pi_toZModPow_sub_eq_of_norm_sub_le_mul_inv_pow
    (x y : ι → ℤ_[p]) (C : ℝ≥0) (A s : ℕ)
    (hC : (C : ℝ) ≤ (p : ℝ) ^ A)
    (hdist : ‖x - y‖ ≤ (C : ℝ) * ((p : ℝ) ^ s)⁻¹) :
    ∀ i, PadicInt.toZModPow (s - A) (x i) = PadicInt.toZModPow (s - A) (y i) := by
  apply (pi_toZModPow_eq_iff_norm_sub_le (s - A) x y).mpr
  apply le_inv_pow_sub_of_le_one_of_le_mul_inv_pow _ A s (norm_pi_sub_le_one x y)
  exact hdist.trans (mul_le_mul_of_nonneg_right hC (by positivity))

/-- The congruence-loss lemma with the input distance measured in `ℚ_p`. -/
theorem pi_toZModPow_sub_eq_of_norm_coe_sub_le_mul_inv_pow
    (x y : ι → ℤ_[p]) (C : ℝ≥0) (A s : ℕ)
    (hC : (C : ℝ) ≤ (p : ℝ) ^ A)
    (hdist : ‖(fun i => (x i : ℚ_[p])) - (fun i => (y i : ℚ_[p]))‖ ≤
      (C : ℝ) * ((p : ℝ) ^ s)⁻¹) :
    ∀ i, PadicInt.toZModPow (s - A) (x i) = PadicInt.toZModPow (s - A) (y i) := by
  apply pi_toZModPow_sub_eq_of_norm_sub_le_mul_inv_pow x y C A s hC
  simpa only [norm_pi_coe_sub] using hdist

/-- A proved local lower-distance estimate transfers an output-distance bound to
input congruence. Both input points must actually belong to the displayed set. -/
theorem pi_toZModPow_sub_eq_of_antilipschitz
    {E : Type*} [SeminormedAddCommGroup E]
    (U : Set (ι → ℚ_[p])) (f : (ι → ℚ_[p]) → E) (C : ℝ≥0)
    (hf : AntilipschitzWith C (U.restrict f))
    (x y : ι → ℤ_[p]) (hx : (fun i => (x i : ℚ_[p])) ∈ U)
    (hy : (fun i => (y i : ℚ_[p])) ∈ U) (A s : ℕ)
    (hC : (C : ℝ) ≤ (p : ℝ) ^ A)
    (hout : ‖f (fun i => (x i : ℚ_[p])) - f (fun i => (y i : ℚ_[p]))‖ ≤
      ((p : ℝ) ^ s)⁻¹) :
    ∀ i, PadicInt.toZModPow (s - A) (x i) = PadicInt.toZModPow (s - A) (y i) := by
  apply pi_toZModPow_sub_eq_of_norm_coe_sub_le_mul_inv_pow x y C A s hC
  have hdist := hf.le_mul_dist ⟨_, hx⟩ ⟨_, hy⟩
  change dist (fun i => (x i : ℚ_[p])) (fun i => (y i : ℚ_[p])) ≤
    (C : ℝ) * dist (f (fun i => (x i : ℚ_[p]))) (f (fun i => (y i : ℚ_[p]))) at hdist
  simp only [dist_eq_norm] at hdist
  exact hdist.trans (mul_le_mul_of_nonneg_left hout C.coe_nonneg)

end CubicTenVariables.PadicResidueNorm
