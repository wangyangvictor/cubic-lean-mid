import HessianTheorem11.UnconditionalRationalIntervals
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-! Exact integral linear-form identities and elimination over arbitrary
linearly ordered additive commutative groups. -/
namespace HessianTheorem11.UnconditionalOrderedWeights
open Finset
variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

def value {n : ℕ} (c : Fin n → ℤ) (x : Fin n → Γ) : Γ := ∑ i, c i • x i

theorem value_add {n : ℕ} (a b : Fin n → ℤ) (x : Fin n → Γ) :
    value (a+b) x = value a x + value b x := by
  simp [value,add_smul,Finset.sum_add_distrib]

theorem value_smul {n : ℕ} (a : Fin n → ℤ) (k : ℤ) (x : Fin n → Γ) :
    value (k • a) x = k • value a x := by
  simp [value,smul_sum,smul_smul]

theorem value_succ {n : ℕ} (a : Fin (n+1) → ℤ) (x : Fin (n+1) → Γ) :
    value a x = a 0 • x 0 + value (a ∘ Fin.succ) (x ∘ Fin.succ) := by
  exact Fin.sum_univ_succ _

theorem holds_nonneg {s : Bool} {x : Γ} (h : Holds s x) : 0 ≤ x := by
  cases s <;> simp only [Holds,Bool.false_eq_true,↓reduceIte] at h
  · exact h
  · exact h.le

theorem holds_positive_combination {s t : Bool} {x y : Γ}
    (hx : Holds s x) (hy : Holds t y) {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    Holds (s || t) (a • x + b • y) := by
  have hx0 := zsmul_nonneg (holds_nonneg hx) ha.le
  have hy0 := zsmul_nonneg (holds_nonneg hy) hb.le
  cases s <;> cases t <;> simp only [Holds,Bool.false_or,Bool.true_or,↓reduceIte] at *
  · exact add_nonneg hx0 hy0
  · exact add_pos_of_nonneg_of_pos hx0 (zsmul_pos hy hb)
  · exact add_pos_of_pos_of_nonneg (zsmul_pos hx ha) hy0
  · exact add_pos (zsmul_pos hx ha) (zsmul_pos hy hb)

def eliminate {n : ℕ} (a b : Fin (n+1) → ℤ) : Fin n → ℤ :=
  fun i => (-b 0) * a i.succ + a 0 * b i.succ

theorem value_eliminate {n : ℕ} (a b : Fin (n+1) → ℤ) (x : Fin (n+1) → Γ) :
    value (eliminate a b) (x ∘ Fin.succ) =
      (-b 0) • value a x + a 0 • value b x := by
  have he : eliminate a b = (-b 0) • (a ∘ Fin.succ) + a 0 • (b ∘ Fin.succ) := rfl
  rw [he,value_add,value_smul,value_smul,value_succ a,value_succ b,smul_add,smul_add]
  have hc : (-b 0) • (a 0 • x 0) + a 0 • (b 0 • x 0) = 0 := by
    rw [smul_smul,smul_smul,← add_smul]
    have h : -b 0 * a 0 + a 0 * b 0 = 0 := by ring
    rw [h,zero_smul]
  calc
    _ = ((-b 0) • (a 0 • x 0) + a 0 • (b 0 • x 0)) +
        ((-b 0) • value (a ∘ Fin.succ) (x ∘ Fin.succ) +
          a 0 • value (b ∘ Fin.succ) (x ∘ Fin.succ)) := by rw [hc,zero_add]
    _ = _ := by abel

theorem value_eliminate_tail {n : ℕ} (a b : Fin (n+1) → ℤ) (x : Fin n → Γ) :
    value (eliminate a b) x = (-b 0) • value (a ∘ Fin.succ) x +
      a 0 • value (b ∘ Fin.succ) x := by
  change value ((-b 0) • (a ∘ Fin.succ) + a 0 • (b ∘ Fin.succ)) x = _
  rw [value_add,value_smul,value_smul]

theorem value_rat {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℚ) :
    value a x = ∑ i, (a i : ℚ) * x i := by simp [value,zsmul_eq_mul]

end HessianTheorem11.UnconditionalOrderedWeights
