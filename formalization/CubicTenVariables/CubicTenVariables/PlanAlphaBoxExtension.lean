import CubicTenVariables.FiniteTranslatedBoxCover

/-! The benchmark radius Q^(1/3) estimate implies the translated-box
estimate with the correct volume factor. This purely analytic helper
keeps the benchmark estimate explicit as an input. -/
set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlanAlphaBoxExtension
open scoped BigOperators
open FiniteTranslatedBoxCover

/-- Covering introduces only a fixed constant and doubles the height-loss
exponent; the benchmark bound is uniform in the center and finite set. -/
theorem of_benchmark (a : (Fin 10 → ℤ) → ℝ) (Q b e K : ℝ)
    (hQ : 1 ≤ Q) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hbench : ∀ (u : Fin 10 → ℝ) (B : ℝ), 1 ≤ B → ‖u‖ ≤ B →
      ∀ V : Finset (Fin 10 → ℤ),
      (∀ v ∈ V, v ≠ 0 ∧ ∀ i, |(v i : ℝ)-u i| ≤ Q^((1 : ℝ)/3)) →
      (∑ v ∈ V, a v) ≤ K*(B*Q)^e*Q^(b+(10 : ℝ)/3))
    (u : Fin 10 → ℝ) (B L : ℝ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hu : ‖u‖ ≤ B) (V : Finset (Fin 10 → ℤ))
    (hV : ∀ v ∈ V, v ≠ 0 ∧ ∀ i, |(v i : ℝ)-u i| ≤ L) :
    (∑ v ∈ V, a v) ≤ (K*7^10*3^e)*(B*L*Q)^(2*e)*
      (L+Q^((1 : ℝ)/3))^10*Q^b := by
  classical
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  let A := Q^((1 : ℝ)/3)
  have hA : 0 < A := Real.rpow_pos_of_pos hQ0 _
  have hAQ : A ≤ Q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 : ℝ)/3 ≤ 1)
  let H := B+L+A
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hBL : 1 ≤ B*L := one_le_mul_of_one_le_of_one_le hB hL
  have hBprod : B ≤ B*L*Q := by
    calc
      B ≤ B*L := by simpa using mul_le_mul_of_nonneg_left hL hB0
      _ ≤ B*L*Q := by simpa using mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ B*L)
  have hLprod : L ≤ B*L*Q := by
    calc
      L ≤ B*L := by simpa using mul_le_mul_of_nonneg_right hB hL0
      _ ≤ B*L*Q := by simpa using mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ B*L)
  have hQprod : Q ≤ B*L*Q := by
    simpa using mul_le_mul_of_nonneg_right hBL hQ0.le
  have hHprod : H ≤ 3*(B*L*Q) := by dsimp [H]; linarith
  have hheight : (H*Q)^e ≤ 3^e*(B*L*Q)^(2*e) := by
    calc
      _ ≤ (3*(B*L*Q)^2)^e := by
        apply Real.rpow_le_rpow (by positivity) _ he
        calc
          H*Q ≤ (3*(B*L*Q))*Q := mul_le_mul_of_nonneg_right hHprod hQ0.le
          _ ≤ (3*(B*L*Q))*(B*L*Q) := mul_le_mul_of_nonneg_left hQprod (by positivity)
          _ = _ := by ring
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _),
          ← Real.rpow_natCast_mul (by positivity : 0 ≤ B*L*Q)]
        norm_num
  have hcover := sum_le_of_piece_bound V u L A
    (K*(H*Q)^e*Q^(b+(10 : ℝ)/3)) hL0 hA (by positivity)
    (fun v hv => (hV v hv).2) a (fun k hk =>
      hbench (center u A k) H hH
        ((center_norm_le V u L A hL0 hA (fun v hv => (hV v hv).2) k hk).trans
          (by dsimp [H]; linarith))
        (piece V u A k) (fun v hv =>
          ⟨(hV v (Finset.mem_filter.mp hv).1).1,piece_box V u A hA k v hv⟩))
  have hvolume : (7*(1+L/A))^10*Q^(b+(10 : ℝ)/3) =
      7^10*(L+A)^10*Q^b := by
    have hA10 : A^10 = Q^((10 : ℝ)/3) := by
      dsimp [A]
      rw [← Real.rpow_mul_natCast hQ0.le]
      norm_num
    have hratio : 1+L/A = (L+A)/A := by field_simp; ring
    rw [hratio,mul_pow,div_pow,Real.rpow_add hQ0,hA10.symm]
    field_simp
    <;> ring
  calc
    _ ≤ (7*(1+L/A))^10*(K*(H*Q)^e*Q^(b+(10 : ℝ)/3)) := hcover
    _ ≤ (7*(1+L/A))^10*(K*(3^e*(B*L*Q)^(2*e))*Q^(b+(10 : ℝ)/3)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheight hK)
          (Real.rpow_nonneg hQ0.le _)) (by positivity)
    _ = (K*3^e*(B*L*Q)^(2*e))*((7*(1+L/A))^10*Q^(b+(10 : ℝ)/3)) := by ring
    _ = _ := by rw [hvolume]; dsimp [A]; ring

end CubicTenVariables.PlanAlphaBoxExtension
