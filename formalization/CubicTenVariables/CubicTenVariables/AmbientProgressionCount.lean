import CubicTenVariables.ConeComponentProgressionCount
import CubicTenVariables.ResidueBoxCount

/-! The ambient j=0 progression bound. It holds for every rational subset,
with an explicit absolute constant and no geometry or literature input. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.AmbientProgressionCount

/-- The literal points in any rational subset, real-centered box and
integral progression satisfy the ambient-dimensional count. -/
theorem card_le {n : ℕ} (P : Set (Fin n → ℚ)) (u : Fin n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : 0 < m) (b : Fin n → ℤ) :
    ((ConeComponentProgressionCount.points P u L m b).card : ℝ) ≤
      (4 : ℝ)^n * (1+L/(m : ℝ))^n := by
  letI : NeZero m := ⟨by omega⟩
  let S := ConeComponentProgressionCount.points P u L m b
  have hs (x) (hx : x ∈ S) :=
    (ConeComponentProgressionCount.mem_points P u L m b x).mp hx
  have hb := ResidueBoxCount.card_le_of_constant_residue m S u L hL
    (fun x hx => (hs x hx).1) (by
      intro x hx y hy i
      have hd : (m : ℤ) ∣ x i-y i := by
        convert dvd_sub ((hs x hx).2.1 i) ((hs y hy).2.1 i) using 1
        ring
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (x i-y i) m).mpr hd
      simpa only [Int.cast_sub,sub_eq_zero] using hz)
  apply hb.trans
  calc
    (4*L/(m : ℝ)+3)^n ≤ (4*(1+L/(m : ℝ)))^n := by
      apply pow_le_pow_left₀ (by positivity)
      have he : 4*L/(m : ℝ) = 4*(L/(m : ℝ)) := by ring
      rw [he]
      linarith
    _ = (4 : ℝ)^n * (1+L/(m : ℝ))^n := mul_pow _ _ _

/-- One constant works before every subset and all translated progression
data in the ten-variable ambient boundary case. -/
theorem exists_ten_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : Set (Fin 10 → ℚ)) (u : Fin 10 → ℝ)
      (L : ℝ), 0 ≤ L → ∀ (m : ℕ), 0 < m → ∀ b : Fin 10 → ℤ,
      ((ConeComponentProgressionCount.points P u L m b).card : ℝ) ≤
        C * (1+L/(m : ℝ))^10 := by
  exact ⟨4^10,by norm_num,fun P u L hL m hm b => card_le P u L hL m hm b⟩

end CubicTenVariables.AmbientProgressionCount
