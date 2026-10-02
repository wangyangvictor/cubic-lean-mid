import CubicTenVariables.GlobalCountingNumerics
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log

/-! Canonical dyadic covers for the actual positive allocation factors.
There are at most ten integer indices (two arrays on at most five depths).
Their finite number is uniformly absorbed into any positive power of the
modulus scale. No arithmetic estimate or literature premise is used. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.ComplementDyadicScales
open scoped BigOperators

/-- The indices needed for every positive integer at most `2*D`. -/
def indexCount (D : ℝ) : ℕ := Nat.log 2 ⌊2*D⌋₊+1

/-- Literal finite arrays of allowed dyadic indices. -/
def arrays (D : ℝ) (ι : Type*) [Fintype ι] : Finset (ι → ℕ) := by
  classical
  exact Fintype.piFinset (fun _ => Finset.range (indexCount D))

/-- The two index arrays for the depths `i+2,...,6`. -/
def pairArrays (D : ℝ) (i : Fin 5) :
    Finset ((Fin (5-i.val) → ℕ) × (Fin (5-i.val) → ℕ)) := by
  classical
  exact (arrays D (Fin (5-i.val))) ×ˢ (arrays D (Fin (5-i.val)))

theorem indexCount_pos (D : ℝ) : 1 ≤ indexCount D := by
  simp [indexCount]

theorem mem_arrays_iff (D : ℝ) {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    k ∈ arrays D ι ↔ ∀ j, k j < indexCount D := by
  classical
  simp [arrays]

theorem card_arrays (D : ℝ) (ι : Type*) [Fintype ι] :
    (arrays D ι).card = indexCount D ^ Fintype.card ι := by
  classical
  simp [arrays,Fintype.card_piFinset]

theorem card_pairArrays (D : ℝ) (i : Fin 5) :
    (pairArrays D i).card = indexCount D ^ (2*(5-i.val)) := by
  classical
  simp only [pairArrays,Finset.card_product,card_arrays,Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

/-- The canonical index belongs to the finite range; no rounding-up
choice or additional covering premise is needed. -/
theorem canonical_index_lt (D : ℝ) (a : ℕ) (haD : (a:ℝ) ≤ 2*D) :
    Nat.log 2 a < indexCount D := by
  have h := Nat.log_mono_right (b := 2) (Nat.le_floor haD)
  exact lt_of_le_of_lt h (Nat.lt_succ_self _)

/-- The cover uses the left-closed, right-open interval `[2^k,2^(k+1))`. -/
theorem canonical_scale_bounds (a : ℕ) (ha : 1 ≤ a) :
    1 ≤ (2:ℝ)^(Nat.log 2 a) ∧
    (2:ℝ)^(Nat.log 2 a) ≤ (a:ℝ) ∧
    (a:ℝ) < 2*(2:ℝ)^(Nat.log 2 a) := by
  refine ⟨one_le_pow₀ (by norm_num),?_,?_⟩
  · exact_mod_cast Nat.pow_log_le_self 2 (by omega : a ≠ 0)
  · have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
    have hr : (a:ℝ) < (2:ℝ)^(Nat.log 2 a+1) := by exact_mod_cast h
    simpa only [pow_succ,mul_comm] using hr

theorem canonical_mem (D : ℝ) {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (haD : ∀ j, (a j:ℝ) ≤ 2*D) :
    (fun j => Nat.log 2 (a j)) ∈ arrays D ι :=
  (mem_arrays_iff D _).mpr (fun j => canonical_index_lt D (a j) (haD j))

/-- Both canonical arrays lie in the same explicit finite family. -/
theorem canonical_pair_mem (D : ℝ) (i : Fin 5)
    (a b : Fin (5-i.val) → ℕ)
    (haD : ∀ j, (a j:ℝ) ≤ 2*D) (hbD : ∀ j, (b j:ℝ) ≤ 2*D) :
    ((fun j => Nat.log 2 (a j)),(fun j => Nat.log 2 (b j))) ∈ pairArrays D i := by
  classical
  exact Finset.mem_product.mpr ⟨canonical_mem D a haD,canonical_mem D b hbD⟩

/-- Uniform absorption of ten indices. The constant precedes every
scale, with no eventual lower threshold beyond `D≥1`. -/
theorem exists_count_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ D : ℝ, 1 ≤ D →
      (indexCount D:ℝ)^10 ≤ K*D^ε := by
  let δ : ℝ := ε/10
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let A : ℝ := (1+1/Real.log 2)*(1+1/δ)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right (by positivity))
    (le_add_of_nonneg_right (by positivity))
  refine ⟨A^10*(2:ℝ)^ε,one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hA) (Real.one_le_rpow (by norm_num) hε.le),?_⟩
  intro D hD
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have h2D : 1 ≤ 2*D := by linarith
  have hfloor : 0 < ⌊2*D⌋₊ := by
    have hf : 1 ≤ ⌊2*D⌋₊ := Nat.le_floor (n := 1) (by simpa using h2D)
    exact hf
  have hn := GlobalCountingNumerics.nat_log_succ_le ⌊2*D⌋₊ (2*D) 1 hfloor h2D
    (by norm_num) (by simpa using Nat.floor_le (show 0 ≤ 2*D by positivity))
  have hlog := GlobalCountingNumerics.affine_log_le (2*D) δ 1 h2D hδ (by norm_num)
  have hc : (indexCount D:ℝ) ≤ A*(2*D)^δ := by
    calc
      _ ≤ (1+1/Real.log 2)*(1+Real.log (2*D)) := hn
      _ ≤ (1+1/Real.log 2)*((1+1/δ)*(2*D)^δ) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hlog) (by positivity)
      _ = _ := by dsimp [A]; ring
  calc
    _ ≤ (A*(2*D)^δ)^10 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
    _ = A^10*((2*D)^δ)^10 := mul_pow ..
    _ = A^10*(2*D)^ε := by
      rw [← Real.rpow_mul_natCast (show 0 ≤ 2*D by positivity)]
      congr 2
      dsimp [δ]
      ring
    _ = (A^10*(2:ℝ)^ε)*D^ε := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hD0.le]
      ring

/-- An arbitrary finite index type with at most ten coordinates. -/
theorem exists_array_count_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ D : ℝ, 1 ≤ D →
      ∀ (ι : Type*) [Fintype ι], Fintype.card ι ≤ 10 →
        ((arrays D ι).card:ℝ) ≤ K*D^ε := by
  obtain ⟨K,hK,hbound⟩ := exists_count_bound ε hε
  refine ⟨K,hK,?_⟩
  intro D hD ι _ hι
  rw [card_arrays,Nat.cast_pow]
  exact (pow_le_pow_right₀ (by exact_mod_cast indexCount_pos D) hι).trans (hbound D hD)

/-- The exact two-array family used for each of the five complementary
pieces, with one constant before the choice of piece and scale. -/
theorem exists_pair_count_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ D : ℝ, 1 ≤ D → ∀ i : Fin 5,
      ((pairArrays D i).card:ℝ) ≤ K*D^ε := by
  obtain ⟨K,hK,hbound⟩ := exists_count_bound ε hε
  refine ⟨K,hK,?_⟩
  intro D hD i
  rw [card_pairArrays,Nat.cast_pow]
  exact (pow_le_pow_right₀ (by exact_mod_cast indexCount_pos D) (by omega : 2*(5-i.val) ≤ 10)).trans
    (hbound D hD)

end CubicTenVariables.ComplementDyadicScales
