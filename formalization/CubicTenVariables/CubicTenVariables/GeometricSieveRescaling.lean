import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Fixed coordinate-change constants and epsilon factors in the translated
composite sieve. This file contains only real inequalities. -/
noncomputable section
namespace CubicTenVariables.GeometricSieveRescaling

theorem estimate (a L U V m S ε : ℝ) (s r : ℕ)
    (ha : 1 ≤ a) (hL : 1 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hVU : V ≤ a*U) (hm : 0 < m) (hS : 1 ≤ S)
    (hε : 0 < ε) (hsr : s ≤ r) :
    (a*L+V)^(ε/2)*(2*S)^(ε/2)*(4*(a*L)/m+3)^(s+1) ≤
      (a^(ε/2)*2^(ε/2)*(4*a)^(r+1))*
        (L*S+U)^ε*(1+L/m)^(r+1) := by
  let H := L*S+U
  let B := 1+L/m
  have ha0 : 0 ≤ a := by linarith
  have hH : 1 ≤ H := by dsimp [H]; nlinarith
  have hH0 : 0 ≤ H := by linarith
  have hB : 1 ≤ B := by dsimp [B]; linarith [div_nonneg (show 0 ≤ L by linarith) hm.le]
  have hη : 0 ≤ ε/2 := by positivity
  have hfirst : (a*L+V)^(ε/2) ≤ a^(ε/2)*H^(ε/2) := by
    rw [← Real.mul_rpow ha0 hH0]
    apply Real.rpow_le_rpow (by positivity) _ hη
    dsimp [H]
    nlinarith [mul_nonneg ha0 (mul_nonneg (show 0 ≤ L by linarith)
      (show 0 ≤ S-1 by linarith))]
  have hsecond : (2*S)^(ε/2) ≤ (2:ℝ)^(ε/2)*H^(ε/2) := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH0]
    apply Real.rpow_le_rpow (by positivity) _ hη
    dsimp [H]
    nlinarith
  have hbox : 4*(a*L)/m+3 ≤ (4*a)*B := by
    dsimp [B]
    have he : 4*(a*L)/m=4*a*(L/m) := by ring
    rw [he]
    nlinarith
  have hthird : (4*(a*L)/m+3)^(s+1) ≤ (4*a)^(r+1)*B^(r+1) := by
    rw [← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hbox _).trans
      (pow_le_pow_right₀ (by nlinarith : 1 ≤ 4*a*B) (by omega))
  have he : H^(ε/2)*H^(ε/2)=H^ε := by
    rw [← Real.rpow_add (by linarith : 0 < H)]
    congr 1
    ring
  calc
    _ ≤ (a^(ε/2)*H^(ε/2))*((2:ℝ)^(ε/2)*H^(ε/2))*
        ((4*a)^(r+1)*B^(r+1)) := by
      exact mul_le_mul (mul_le_mul hfirst hsecond (by positivity) (by positivity))
        hthird (by positivity) (by positivity)
    _ = (a^(ε/2)*2^(ε/2)*(4*a)^(r+1))*H^ε*B^(r+1) := by
      rw [← he]
      ring

end CubicTenVariables.GeometricSieveRescaling
