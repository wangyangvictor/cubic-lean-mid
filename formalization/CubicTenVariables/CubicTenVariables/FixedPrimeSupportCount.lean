import CubicTenVariables.FinitePrimeWeightSum
import CubicTenVariables.CubeFullSmithProduct
import Mathlib.Analysis.SpecificLimits.Normed

/-! Positive integers supported on a fixed finite prime set have a
subpower counting bound. Constants precede the cutoff and finite family. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FixedPrimeSupportCount
open scoped BigOperators

/-- A finite-support Euler product and Rankin's inequality bound the
number of actual supported moduli, including the modulus one. -/
theorem exists_bound (s : Finset ℕ) (hprimes : ∀ p ∈ s, p.Prime)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → ∀ Q : Finset ℕ,
      (∀ g ∈ Q, 0 < g ∧ g.primeFactors ⊆ s ∧ (g : ℝ) ≤ X) →
      (Q.card : ℝ) ≤ C*X^ε := by
  classical
  let w (p k : ℕ) : ℝ :=
    if p ∈ s then ((p : ℝ)^(-ε))^k else if k = 0 then 1 else 0
  have hw (p k : ℕ) : 0 ≤ w p k := by dsimp [w]; split_ifs <;> positivity
  have hw0 (p : ℕ) : w p 0 = 1 := by simp [w]
  have hratio (p : ℕ) (hp : p.Prime) : (p : ℝ)^(-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  let b (p : ℕ) : ℝ := (1-(p : ℝ)^(-ε))⁻¹ / (p : ℝ)^(-2 : ℝ)
  have hb (p : ℕ) (hp : p ∈ s) : 0 ≤ b p := by
    have hh := hratio p (hprimes p hp)
    exact div_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hh.le))
      (Real.rpow_nonneg (Nat.cast_nonneg p) (-2))
  let K : ℝ := ∑ p ∈ s, b p
  have hK : 0 ≤ K := Finset.sum_nonneg hb
  have hlocal (p : ℕ) (hp : p.Prime) (E : Finset ℕ) :
      (∑ k ∈ E, w p k) ≤ 1+K*(p : ℝ)^(-1-(1 : ℝ)) := by
    rw [show (-1-(1 : ℝ)) = -2 by norm_num]
    by_cases hps : p ∈ s
    · have hgeom := hasSum_geometric_of_lt_one
        (Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)) (hratio p hp)
      have hsum : (∑ k ∈ E, ((p : ℝ)^(-ε))^k) ≤ (1-(p : ℝ)^(-ε))⁻¹ := by
        simpa only [hgeom.tsum_eq] using hgeom.summable.sum_le_tsum E
          (fun k _ => pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) (-ε)) k)
      have hsingle : b p ≤ K := Finset.single_le_sum hb hps
      have hden : 0 < (p : ℝ)^(-2 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
      have hbound : (1-(p : ℝ)^(-ε))⁻¹ ≤ K*(p : ℝ)^(-2 : ℝ) :=
        (div_le_iff₀ hden).mp hsingle
      simp only [w,if_pos hps]
      exact hsum.trans (hbound.trans (by linarith))
    · simp only [w,if_neg hps,Finset.sum_ite_eq']
      split_ifs <;> have hnonneg := mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg p) (-2))
      all_goals linarith
  obtain ⟨C,hC,hbound⟩ := FinitePrimeWeightSum.exists_uniform_bound w hw hw0
    1 K (by norm_num) hK hlocal
  refine ⟨C,hC,?_⟩
  intro X hX Q hQ
  have hprod (g : ℕ) (hg : g ∈ Q) :
      (∏ p ∈ g.primeFactors, w p (g.factorization p)) = (g : ℝ)^(-ε) := by
    rw [← CubeFullSmithProduct.prod_factorization_rpow g (hQ g hg).1 (-ε)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [w,if_pos ((hQ g hg).2.1 hp)]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    ring
  have hmass : (∑ g ∈ Q, (g : ℝ)^(-ε)) ≤ C := by
    calc
      _ = ∑ g ∈ Q, ∏ p ∈ g.primeFactors, w p (g.factorization p) :=
        Finset.sum_congr rfl (fun g hg => (hprod g hg).symm)
      _ ≤ C := hbound Q (fun g hg => (hQ g hg).1)
  have hterm (g : ℕ) (hg : g ∈ Q) : 1 ≤ X^ε*(g : ℝ)^(-ε) := by
    have hg0 : 0 < (g : ℝ) := by exact_mod_cast (hQ g hg).1
    calc
      1 = (g : ℝ)^ε*(g : ℝ)^(-ε) := by
        rw [← Real.rpow_add hg0,add_neg_cancel,Real.rpow_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hg0.le (hQ g hg).2.2 hε.le) (by positivity)
  calc
    _ = ∑ _g ∈ Q, (1 : ℝ) := by simp
    _ ≤ ∑ g ∈ Q, X^ε*(g : ℝ)^(-ε) := Finset.sum_le_sum hterm
    _ = X^ε*(∑ g ∈ Q, (g : ℝ)^(-ε)) := (Finset.mul_sum ..).symm
    _ ≤ X^ε*C := mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg (zero_le_one.trans hX) ε)
    _ = _ := mul_comm _ _

end CubicTenVariables.FixedPrimeSupportCount
