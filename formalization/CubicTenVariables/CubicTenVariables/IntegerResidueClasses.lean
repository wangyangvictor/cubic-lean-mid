import Mathlib.Data.ZMod.Basic

/-! Canonical integer lifts for vector residue classes. -/
set_option autoImplicit false
namespace CubicTenVariables.IntegerResidueClasses

/-- Coordinatewise reduction of an integer vector modulo `m`. -/
def residue {n : ℕ} (m : ℕ) (v : Fin n → ℤ) : Fin n → ZMod m :=
  fun k => (v k : ZMod m)

/-- The canonical nonnegative integer representatives of a residue vector. -/
def lift {n m : ℕ} (b : Fin n → ZMod m) : Fin n → ℤ :=
  fun k => ((b k).val : ℤ)

theorem residue_lift {n : ℕ} (m : ℕ) [NeZero m] (b : Fin n → ZMod m) :
    residue m (lift b) = b := by
  funext k
  simp only [residue, lift, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Equality with a residue vector is the usual coordinatewise progression
condition around its canonical integer lift. -/
theorem residue_eq_iff_dvd_sub {n : ℕ} (m : ℕ) [NeZero m]
    (v : Fin n → ℤ) (b : Fin n → ZMod m) :
    residue m v = b ↔ ∀ k, (m : ℤ) ∣ v k - lift b k := by
  constructor
  · intro hv k
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    rw [Int.cast_sub]
    have hk := congrFun hv k
    change (v k : ZMod m) = b k at hk
    rw [hk]
    simp only [lift, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
  · intro hv
    funext k
    have hk := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr (hv k)
    rw [Int.cast_sub] at hk
    simpa only [residue, lift, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] using hk

end CubicTenVariables.IntegerResidueClasses
