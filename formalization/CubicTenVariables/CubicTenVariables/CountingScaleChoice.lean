import CubicTenVariables.CountingScaleRange
import Mathlib.Algebra.Order.Floor.Semifield

/-! Natural delta-method scales exist cofinally inside the lower-scale
window needed for the main term. The ceiling is controlled explicitly,
and Q^2/P^3 retains a strictly decaying upper bound. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.CountingScaleChoice

theorem exists_threshold (ν : ℝ) (hν : 0 < ν) :
    ∃ P₀ : ℝ, 4 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P → 2 ≤ P^(ν/2) := by
  refine ⟨max 4 ((2:ℝ)^((ν/2)⁻¹)),le_max_left _ _,?_⟩
  intro P hP
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4)
    ((le_max_left _ _).trans hP)
  exact (Real.rpow_inv_le_iff_of_pos (by norm_num : (0:ℝ) ≤ 2)
    hPpos.le (half_pos hν)).mp ((le_max_right _ _).trans hP)

/-- The literal natural ceiling lies in the desired nonempty window once
the small exponent supplies a factor two of slack. -/
theorem ceiling_bounds (P ν : ℝ) (hP : 1 ≤ P) (hν : ν ≤ 1/2)
    (hslack : 2 ≤ P^(ν/2)) :
    1 ≤ ⌈P^((3:ℝ)/2-ν)⌉₊ ∧
      P^((3:ℝ)/2-ν) ≤ (⌈P^((3:ℝ)/2-ν)⌉₊:ℝ) ∧
      (⌈P^((3:ℝ)/2-ν)⌉₊:ℝ) ≤ P^((3:ℝ)/2-ν/2) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hlo : 1 ≤ P^((3:ℝ)/2-ν) := Real.one_le_rpow hP (by linarith)
  refine ⟨Nat.one_le_ceil_iff.mpr (by positivity),Nat.le_ceil _,?_⟩
  calc
    _ ≤ 2*P^((3:ℝ)/2-ν) := Nat.ceil_le_two_mul (by linarith)
    _ ≤ P^(ν/2)*P^((3:ℝ)/2-ν) :=
      mul_le_mul_of_nonneg_right hslack (by positivity)
    _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring

/-- Every sufficiently large natural P admits a natural Q in the whole
stated scale window, so the subsequent asymptotic is not vacuous. -/
theorem exists_eventual_integer_window (ν : ℝ) (hν : 0 < ν) (hνhalf : ν ≤ 1/2) :
    ∃ P₀ : ℝ, 4 ≤ P₀ ∧ ∀ P : ℕ, P₀ ≤ (P:ℝ) →
      ∃ Q : ℕ, 1 ≤ Q ∧ (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ) ∧
        (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2-ν/2) := by
  obtain ⟨P₀,hP₀,hb⟩ := exists_threshold ν hν
  refine ⟨P₀,hP₀,?_⟩
  intro P hP
  exact ⟨⌈(P:ℝ)^((3:ℝ)/2-ν)⌉₊,
    ceiling_bounds P ν (by linarith) hνhalf (hb P hP)⟩

theorem exists_integer_window (ν : ℝ) (hν : 0 < ν) (hνhalf : ν ≤ 1/2) (B : ℝ) :
    ∃ P Q : ℕ, max 4 B ≤ (P:ℝ) ∧ 1 ≤ Q ∧
      (P:ℝ)^((3:ℝ)/2-ν) ≤ (Q:ℝ) ∧ (Q:ℝ) ≤ (P:ℝ)^((3:ℝ)/2-ν/2) := by
  obtain ⟨P₀,hP₀,hb⟩ := exists_eventual_integer_window ν hν hνhalf
  let P : ℕ := ⌈max P₀ (max 4 B)⌉₊
  have hP : max P₀ (max 4 B) ≤ (P:ℝ) := Nat.le_ceil _
  obtain ⟨Q,hQ⟩ := hb P ((le_max_left _ _).trans hP)
  exact ⟨P,Q,(le_max_right _ _).trans hP,hQ⟩

/-- The upper edge of the window makes the normalized kernel scale tend
to zero at a definite power, unlike Q=P^(3/2). -/
theorem normalized_square_le (P Q ν : ℝ) (hP : 0 < P) (hQ : 0 ≤ Q)
    (hupper : Q ≤ P^((3:ℝ)/2-ν/2)) : Q^2/P^3 ≤ P^(-ν) := by
  calc
    _ ≤ (P^((3:ℝ)/2-ν/2))^2/P^3 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hQ hupper 2) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (P^((3:ℝ)/2-ν/2)) 2,
        ← Real.rpow_mul hP.le,← Real.rpow_natCast P 3,← Real.rpow_sub hP]
      congr 1
      norm_num
      ring

end CubicTenVariables.CountingScaleChoice
