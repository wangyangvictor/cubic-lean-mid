import CubicTenVariables.CubeFullSmithProduct
import CubicTenVariables.PositiveReciprocalSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! The literal Smith weights in the mixed-modulus argument and their
local Rankin bounds. No cubic, geometry, or analytic-number-theory input
is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CubicTenVariables.CubefullSmithWeightLocal
open CubeFullSmithParameters
open scoped BigOperators

def omega (r : ℕ) : ℝ :=
  (z r 0 : ℝ)^(-2 : ℝ) * (z r 1 : ℝ)^(-4 : ℝ) * (z r 2 : ℝ)^(-1 : ℝ)
def u (r : ℕ) : ℝ := ((z r 1 : ℝ)/(z r 2 : ℝ))^((1 : ℝ)/3)
def weight (α : ℝ) (r : ℕ) : ℝ := omega r * u r ^ α
def threshold (α : ℝ) : ℝ := max 0 ((α-9)/12)
def penalty (α : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 2 else if i = 1 then 4-α/3 else 1+α/3
def localWeight (α s : ℝ) (p k : ℕ) : ℝ :=
  if k = 0 then 1 else if 3 ≤ k then
    (p : ℝ)^(-(k : ℝ)*s-penalty α (k%3)) else 0

theorem weight_nonneg (α : ℝ) (r : ℕ) : 0 ≤ weight α r := by
  unfold weight omega u
  positivity

theorem localWeight_nonneg (α s : ℝ) (p k : ℕ) : 0 ≤ localWeight α s p k := by
  unfold localWeight
  split_ifs <;> positivity

@[simp] theorem localWeight_zero (α s : ℝ) (p : ℕ) : localWeight α s p 0 = 1 := by
  simp [localWeight]

theorem threshold_nonneg (α : ℝ) : 0 ≤ threshold α := le_max_left _ _

/-- The three first local terms all have exponent at most `-1-ε`.
The exceptional loss at alpha=10 is exactly the source's `1/12`. -/
theorem first_exponent_le (α ε : ℝ) (hα : 0 ≤ α) (_hα10 : α ≤ 10)
    (hε : 0 < ε) (i : ℕ) (hi : i < 3) :
    -((3+i : ℕ) : ℝ)*(threshold α+ε)-penalty α i ≤ -1-ε := by
  have ht0 := threshold_nonneg α
  have ht1 : (α-9)/12 ≤ threshold α := le_max_right _ _
  interval_cases i <;> norm_num [penalty] <;> nlinarith

theorem geometricRatio_pos_lt_one (s : ℝ) (hs : 0 < s) :
    0 < (2 : ℝ)^(-3*s) ∧ (2 : ℝ)^(-3*s) < 1 := by
  exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

/-- A local exponent of any size is bounded by a convergent geometric
series after grouping its three possible residues modulo three. -/
theorem localWeight_le_geometric (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10)
    (hε : 0 < ε) (p k : ℕ) (hp : 2 ≤ p) (hk : 3 ≤ k) :
    localWeight α (threshold α+ε) p k ≤
      (p : ℝ)^(-1-ε) * ((2 : ℝ)^(-3*(threshold α+ε)))^(k/3-1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hs : 0 < threshold α+ε := by linarith [threshold_nonneg α]
  have hdecomp : k = (3+k%3)+3*(k/3-1) := by omega
  have hreal : (k : ℝ) = (3+k%3 : ℕ)+3*(k/3-1 : ℕ) := by exact_mod_cast hdecomp
  have heq : -(k : ℝ)*(threshold α+ε)-penalty α (k%3) =
      (-((3+k%3 : ℕ) : ℝ)*(threshold α+ε)-penalty α (k%3)) +
        (-3*(threshold α+ε))*(k/3-1 : ℕ) := by rw [hreal]; ring
  have hb := first_exponent_le α ε hα hα10 hε (k%3) (Nat.mod_lt _ (by norm_num))
  have hratio : (p : ℝ)^(-3*(threshold α+ε)) ≤ (2 : ℝ)^(-3*(threshold α+ε)) := by
    apply Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp)
    linarith
  rw [localWeight, if_neg (by omega), if_pos hk, heq, Real.rpow_add hp0,
    Real.rpow_mul hp0.le, Real.rpow_natCast]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hp1 hb)
    (pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hratio _)
    (by positivity) (by positivity)

/-- Exact combination of the original omega and u, using signed real
powers and the actual canonical residue-class prime products. -/
theorem weight_eq (α : ℝ) (r : ℕ) :
    weight α r = (z r 0 : ℝ)^(-2 : ℝ) *
      (z r 1 : ℝ)^(-4+α/3) * (z r 2 : ℝ)^(-1-α/3) := by
  have hz (i : ℕ) : 0 < (z r i : ℝ) := by exact_mod_cast z_pos r i
  unfold weight omega u
  rw [← Real.rpow_mul (div_nonneg (hz 1).le (hz 2).le)]
  rw [Real.div_rpow (hz 1).le (hz 2).le]
  rw [div_eq_mul_inv, ← Real.rpow_neg (hz 2).le]
  have h : (1 : ℝ)/3*α = α/3 := by ring
  rw [h]
  calc
    _ = (z r 0 : ℝ)^(-2 : ℝ) *
      ((z r 1 : ℝ)^(-4 : ℝ)*(z r 1 : ℝ)^(α/3)) *
      ((z r 2 : ℝ)^(-1 : ℝ)*(z r 2 : ℝ)^(-(α/3))) := by ring
    _ = _ := by rw [← Real.rpow_add (hz 1), ← Real.rpow_add (hz 2)]; congr 2

/-- The Rankin integrand is precisely the finite product of local
weights; all factors are tied to the original modulus. -/
theorem weighted_rankin_product (α s : ℝ) (r : ℕ) (hr : 0 < r) (hc : CubeFull r) :
    weight α r * (r : ℝ)^(-s) =
      ∏ p ∈ r.primeFactors, localWeight α s p (r.factorization p) := by
  rw [weight_eq]
  rw [← CubeFullSmithProduct.prod_residue_class_rpow r 0 (-2),
    ← CubeFullSmithProduct.prod_residue_class_rpow r 1 (-4+α/3),
    ← CubeFullSmithProduct.prod_residue_class_rpow r 2 (-1-α/3),
    ← CubeFullSmithProduct.prod_factorization_rpow r hr (-s)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hk := hc p hp
  have hk0 : r.factorization p ≠ 0 := by omega
  simp only [localWeight, if_neg hk0, if_pos hk]
  have hm := Nat.mod_lt (r.factorization p) (by norm_num : 0 < 3)
  interval_cases hi : r.factorization p%3
  all_goals simp only [penalty, Nat.reduceEqDiff, ↓reduceIte, mul_one, one_mul]
  all_goals rw [← Real.rpow_add hp0]
  all_goals congr 1; ring

/-- Finite geometric block sums have three terms in each block. -/
theorem sum_geometric_blocks_le (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (T : Finset ℕ) (hT : ∀ k ∈ T, 3 ≤ k) :
    (∑ k ∈ T, g^(k/3-1)) ≤ 3*(1-g)⁻¹ := by
  classical
  let f (k : ℕ) : ℕ × Fin 3 := (k/3-1, ⟨k%3, Nat.mod_lt _ (by norm_num)⟩)
  let A := T.image (fun k => k/3-1)
  have hinj : Set.InjOn f (T : Set ℕ) := by
    intro a ha b hb hab
    have h1 : a/3-1 = b/3-1 := congrArg Prod.fst hab
    have h2 : a%3 = b%3 := congrArg (fun x : ℕ × Fin 3 => x.2.val) hab
    have := hT a ha
    have := hT b hb
    omega
  have hsub : T.image f ⊆ A.product Finset.univ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k,hk,rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hk, Finset.mem_univ _⟩
  have hsum : (∑ a ∈ A, g^a) ≤ (1-g)⁻¹ := by
    have h := hasSum_geometric_of_lt_one hg0 hg1
    simpa only [h.tsum_eq] using h.summable.sum_le_tsum A (fun a _ => pow_nonneg hg0 a)
  calc
    _ = ∑ x ∈ T.image f, g^x.1 := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ A.product Finset.univ, g^x.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => pow_nonneg hg0 _)
    _ = 3*(∑ a ∈ A, g^a) := by
      simp [Finset.sum_product]
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- Uniform finite local sums, with a prime-independent constant. -/
theorem exists_local_bound (α ε : ℝ) (hα : 0 ≤ α) (hα10 : α ≤ 10) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℕ, 2 ≤ p → ∀ E : Finset ℕ,
      (∑ k ∈ E, localWeight α (threshold α+ε) p k) ≤
        1+K*(p : ℝ)^(-1-ε) := by
  classical
  let g := (2 : ℝ)^(-3*(threshold α+ε))
  have hg := geometricRatio_pos_lt_one (threshold α+ε) (by linarith [threshold_nonneg α])
  have hg1 : g < 1 := hg.2
  refine ⟨3*(1-g)⁻¹, mul_nonneg (by norm_num) (inv_nonneg.mpr (by linarith)), ?_⟩
  intro p hp E
  let T := E.filter (fun k => 3 ≤ k)
  have hb := sum_geometric_blocks_le g hg.1.le hg.2 T (fun k hk => (Finset.mem_filter.mp hk).2)
  calc
    _ ≤ (∑ k ∈ E, if k=0 then (1:ℝ) else 0) +
        (∑ k ∈ T, localWeight α (threshold α+ε) p k) := by
      simp only [T, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hk0 : k=0
      · subst k; simp
      · by_cases hk3 : 3 ≤ k <;> simp [localWeight, hk0, hk3]
    _ ≤ 1+(∑ k ∈ T, (p : ℝ)^(-1-ε)*g^(k/3-1)) := by
      apply add_le_add
      · simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      · exact Finset.sum_le_sum (fun k hk => localWeight_le_geometric α ε hα hα10 hε p k hp
          (Finset.mem_filter.mp hk).2)
    _ = 1+(p : ℝ)^(-1-ε)*(∑ k ∈ T, g^(k/3-1)) := by rw [Finset.mul_sum]
    _ ≤ 1+(p : ℝ)^(-1-ε)*(3*(1-g)⁻¹) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hb (by positivity)) 1
    _ = _ := by ring

end CubicTenVariables.CubefullSmithWeightLocal
