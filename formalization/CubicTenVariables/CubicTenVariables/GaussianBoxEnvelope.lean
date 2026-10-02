import CubicTenVariables.GoodHessianKernelAverage
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Full Gaussian summation from a nonnegative ten-variable box envelope. -/

noncomputable section
namespace CubicTenVariables.GaussianBoxEnvelope
open scoped BigOperators

/-- Real sup norm of an integer vector. -/
def height (x : Fin 10 → ℤ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |(x i : ℝ)|)

def energy (x : Fin 10 → ℤ) : ℝ := ∑ i, (x i : ℝ)^2

def gaussian (L : ℝ) (x : Fin 10 → ℤ) : ℝ := Real.exp (-energy x / L^2)

def shell (S : ℝ) (x : Fin 10 → ℤ) : ℕ := ⌊height x / S⌋₊

def shellWeight (k : ℕ) : ℝ := ((k : ℝ)+1)^15 * Real.exp (-(k : ℝ)^2)

theorem abs_le_height (x : Fin 10 → ℤ) (i : Fin 10) : |(x i : ℝ)| ≤ height x :=
  Finset.le_sup' (fun j : Fin 10 => |(x j : ℝ)|) (Finset.mem_univ i)

theorem height_nonneg (x : Fin 10 → ℤ) : 0 ≤ height x :=
  (abs_nonneg _).trans (abs_le_height x 0)

theorem height_sq_le_energy (x : Fin 10 → ℤ) : (height x)^2 ≤ energy x := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin 10 => |(x i : ℝ)|)
  change (height x)^2 ≤ ∑ j, (x j : ℝ)^2
  change height x = |(x i : ℝ)| at hi
  rw [hi, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j : ℝ)) (Finset.mem_univ i)

theorem shell_lower (S : ℝ) (hS : 0 < S) (x : Fin 10 → ℤ) :
    (shell S x : ℝ)*S ≤ height x := by
  exact (le_div_iff₀ hS).mp (Nat.floor_le (div_nonneg (height_nonneg x) hS.le))

theorem shell_upper (S : ℝ) (hS : 0 < S) (x : Fin 10 → ℤ) :
    height x < ((shell S x : ℝ)+1)*S := by
  exact (div_lt_iff₀ hS).mp (Nat.lt_floor_add_one (height x / S))

theorem gaussian_le_shell (L S : ℝ) (hL : 0 < L) (hS : 0 < S) (hLS : L ≤ S)
    (x : Fin 10 → ℤ) : gaussian L x ≤ Real.exp (-(shell S x : ℝ)^2) := by
  have hk : (shell S x : ℝ)*L ≤ height x :=
    (mul_le_mul_of_nonneg_left hLS (Nat.cast_nonneg _)).trans (shell_lower S hS x)
  have hs : (shell S x : ℝ)^2 * L^2 ≤ energy x := by
    calc
      _ = ((shell S x : ℝ)*L)^2 := by ring
      _ ≤ (height x)^2 := pow_le_pow_left₀ (by positivity) hk 2
      _ ≤ _ := height_sq_le_energy x
  have hq : (shell S x : ℝ)^2 ≤ energy x / L^2 := (le_div_iff₀ (by positivity)).mpr hs
  unfold gaussian
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hq

theorem shellWeight_nonneg (k : ℕ) : 0 ≤ shellWeight k := by unfold shellWeight; positivity

theorem summable_shellWeight : Summable shellWeight := by
  have h0 : Summable (fun k : ℕ => (k : ℝ)^15 * Real.exp (-(k : ℝ))) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 15 (r:=1) (by norm_num)
  have h1 : Summable (fun k : ℕ => ((k : ℝ)+1)^15 * Real.exp (-((k : ℝ)+1))) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      h0.comp_injective Nat.succ_injective
  have h2 : Summable (fun k : ℕ => ((k : ℝ)+1)^15 * Real.exp (-(k : ℝ))) := by
    apply (h1.mul_left (Real.exp 1)).congr
    intro k
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  apply h2.of_nonneg_of_le shellWeight_nonneg
  intro k
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hk : (k : ℝ) ≤ (k : ℝ)^2 := by
    by_cases hk : k = 0
    · simp [hk]
    · have hk1 : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      nlinarith
  linarith

/-- Scaling a box radius costs at most the fifteenth power. -/
theorem envelope_scale (m S k : ℝ) (hm : 0 ≤ m) (hS : 0 ≤ S) (hk : 1 ≤ k) :
    (m+(k*S)^3)^5 ≤ k^15*(m+S^3)^5 := by
  have hk3 : 1 ≤ k^3 := one_le_pow₀ hk
  have hm' : m ≤ k^3*m := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk3 hm
  have hb : m+(k*S)^3 ≤ k^3*(m+S^3) := by rw [mul_pow]; nlinarith
  calc
    _ ≤ (k^3*(m+S^3))^5 := pow_le_pow_left₀ (by positivity) hb 5
    _ = _ := by ring

/-- The radius-one fallback is uniformly absorbed by m>=1. -/
theorem max_envelope (m L : ℝ) (hm : 1 ≤ m) (hL : 0 ≤ L) :
    (m+(max 1 L)^3)^5 ≤ 32*(m+L^3)^5 := by
  have hmax : (max 1 L)^3 ≤ 1+L^3 := by
    rcases le_total L 1 with h | h
    · rw [max_eq_left h]
      norm_num
      positivity
    · rw [max_eq_right h]
      linarith
  have hb : m+(max 1 L)^3 ≤ 2*(m+L^3) := by nlinarith [pow_nonneg hL 3]
  calc
    _ ≤ (2*(m+L^3))^5 := pow_le_pow_left₀ (by positivity) hb 5
    _ = _ := by ring

/-- A finite shell is contained in its actual closed integer box. -/
theorem sum_shell_le (w : (Fin 10 → ℤ) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A m L S : ℝ) (hA : 0 ≤ A) (hm : 0 ≤ m) (hL : 0 < L)
    (hS : 1 ≤ S) (hLS : L ≤ S)
    (hbox : ∀ R : ℝ, 1 ≤ R →
      (∑ x ∈ GoodHessianKernelAverage.realBox R, w x) ≤ A*(m+R^3)^5)
    (T : Finset (Fin 10 → ℤ)) (k : ℕ) :
    (∑ x ∈ T.filter (fun x => shell S x = k), w x * gaussian L x) ≤
      A*(m+S^3)^5 * shellWeight k := by
  classical
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hR1 : 1 ≤ ((k:ℝ)+1)*S := by
    simpa only [one_mul] using mul_le_mul hk1 hS (by norm_num : (0:ℝ) ≤ 1) (by positivity)
  have hsub : T.filter (fun x => shell S x = k) ⊆
      GoodHessianKernelAverage.realBox (((k:ℝ)+1)*S) := by
    intro x hx
    rw [GoodHessianKernelAverage.mem_realBox (by positivity)]
    intro i
    have hu := shell_upper S hS0 x
    rw [(Finset.mem_filter.mp hx).2] at hu
    exact (abs_le_height x i).trans hu.le
  have hsum : (∑ x ∈ T.filter (fun x => shell S x = k), w x) ≤
      A*(m+(((k:ℝ)+1)*S)^3)^5 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x)).trans
      (hbox _ hR1)
  calc
    _ ≤ ∑ x ∈ T.filter (fun x => shell S x = k), w x * Real.exp (-(k:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro x hx
      have hg := gaussian_le_shell L S hL hS0 hLS x
      rw [(Finset.mem_filter.mp hx).2] at hg
      exact mul_le_mul_of_nonneg_left hg (hw x)
    _ = (∑ x ∈ T.filter (fun x => shell S x = k), w x) * Real.exp (-(k:ℝ)^2) :=
      (Finset.sum_mul ..).symm
    _ ≤ (A*(m+(((k:ℝ)+1)*S)^3)^5)*Real.exp (-(k:ℝ)^2) :=
      mul_le_mul_of_nonneg_right hsum (Real.exp_nonneg _)
    _ ≤ (A*(((k:ℝ)+1)^15*(m+S^3)^5))*Real.exp (-(k:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul_of_nonneg_left (envelope_scale m S ((k:ℝ)+1) hm hS0.le hk1) hA
    _ = _ := by unfold shellWeight; ring

/-- Uniform envelope for every finite subset; no truncation is fixed. -/
theorem finite_sum_le (w : (Fin 10 → ℤ) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A m L : ℝ) (hA : 0 ≤ A) (hm : 1 ≤ m) (hL : 0 < L)
    (hbox : ∀ R : ℝ, 1 ≤ R →
      (∑ x ∈ GoodHessianKernelAverage.realBox R, w x) ≤ A*(m+R^3)^5)
    (T : Finset (Fin 10 → ℤ)) :
    (∑ x ∈ T, w x * gaussian L x) ≤
      (32*A*(∑' k : ℕ, shellWeight k))*(m+L^3)^5 := by
  classical
  let S : ℝ := max 1 L
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hseries : 0 ≤ ∑' k : ℕ, shellWeight k := tsum_nonneg shellWeight_nonneg
  calc
    _ = ∑ k ∈ T.image (shell S),
        ∑ x ∈ T.filter (fun x => shell S x = k), w x * gaussian L x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
    _ ≤ ∑ k ∈ T.image (shell S), A*(m+S^3)^5*shellWeight k := by
      apply Finset.sum_le_sum
      intro k _
      exact sum_shell_le w hw A m L S hA (zero_le_one.trans hm) hL hS
        (le_max_right _ _) hbox T k
    _ = A*(m+S^3)^5*(∑ k ∈ T.image (shell S), shellWeight k) :=
      (Finset.mul_sum ..).symm
    _ ≤ A*(m+S^3)^5*(∑' k : ℕ, shellWeight k) := by
      apply mul_le_mul_of_nonneg_left
      · exact Summable.sum_le_tsum _ (fun k _ => shellWeight_nonneg k) summable_shellWeight
      · positivity
    _ = A*(∑' k : ℕ, shellWeight k)*(m+S^3)^5 := by ring
    _ ≤ A*(∑' k : ℕ, shellWeight k)*(32*(m+L^3)^5) :=
      mul_le_mul_of_nonneg_left (max_envelope m L hm hL.le) (mul_nonneg hA hseries)
    _ = _ := by ring

/-- The full nonnegative Gaussian is summable, with the same finite-sum bound. -/
theorem summable_and_tsum_le (w : (Fin 10 → ℤ) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A m L : ℝ) (hA : 0 ≤ A) (hm : 1 ≤ m) (hL : 0 < L)
    (hbox : ∀ R : ℝ, 1 ≤ R →
      (∑ x ∈ GoodHessianKernelAverage.realBox R, w x) ≤ A*(m+R^3)^5) :
    Summable (fun x => w x * gaussian L x) ∧
      (∑' x, w x * gaussian L x) ≤ (32*A*(∑' k : ℕ, shellWeight k))*(m+L^3)^5 := by
  have hfinite := finite_sum_le w hw A m L hA hm hL hbox
  have hs : Summable (fun x => w x * gaussian L x) :=
    summable_of_sum_le (fun x => mul_nonneg (hw x) (Real.exp_nonneg _)) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

end CubicTenVariables.GaussianBoxEnvelope

