import CubicTenVariables.Literature.CubicSurfaceZetaFactors
import CubicTenVariables.Literature.SurfacePointCountAmplification
import CubicTenVariables.SurfacePowerSumAmplification
import Mathlib.FieldTheory.Finite.Extension

/-!
# Cubic-surface amplification from classical zeta-factor bounds

The finite fields used below are actual extensions of the intermediate
field supplied by potential goodness.  Their dimensions and cardinalities
are proved using mathlib.  The zeta-factor input therefore applies to the
same coefficient extensions that occur in the point-count hypothesis.

The only literature argument is `CubicSurfaceZetaFactorBounds`.  Potential
goodness, spectral amplification, and the uniform numerical conclusion are
connected here by Lean proofs.
-/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.CubicSurfaceAmplificationFromZeta

open MvPolynomial Literature ProjectiveFourierIdentity
open SurfacePowerSumAmplification
open scoped BigOperators

theorem proved (zeta : CubicSurfaceZetaFactorBounds) :
    CubicSurfacePointCountAmplification := by
  classical
  intro K _ _ F hF h2 h3 hI hpotential
  obtain ⟨n₁, n₂, n₃, a, b, c, hsize, ha, hb, htrace⟩ := zeta K F hF h2 h3 hI
  obtain ⟨C, _hC, E, hE, hEfin, hpotential⟩ := hpotential
  letI : FiniteDimensional K E := hE
  letI : Finite E := hEfin
  letI : Fintype E := Fintype.ofFinite E
  let q : ℝ := Fintype.card K
  let d : ℕ := Module.finrank K E
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast Fintype.card_pos (α := K)
  have hd : 1 ≤ d := Module.finrank_pos
  have hbound : ∀ m : ℕ, 1 ≤ m →
      ‖error q a b c (d * m)‖ ≤ C * (q ^ d) ^ m := by
    intro m hm
    letI : NeZero m := ⟨by omega⟩
    letI : CharP E (ringChar E) := ringChar.charP E
    letI : Fact (ringChar E).Prime := ⟨CharP.char_is_prime E (ringChar E)⟩
    let L := FiniteField.Extension E (ringChar E) m
    letI : Fintype L := Fintype.ofFinite L
    letI : Algebra K L := ((algebraMap E L).comp (algebraMap K E)).toAlgebra
    letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional K L := FiniteDimensional.trans K E L
    have hdim : Module.finrank K L = d * m := by
      rw [← Module.finrank_mul_finrank K E L, FiniteField.finrank_extension]
    have hcard : Fintype.card L = Fintype.card K ^ (d * m) := by
      simpa only [hdim] using (Module.card_eq_pow_finrank (K := K) (V := L))
    have hcardR : (Fintype.card L : ℝ) = q ^ (d * m) := by
      dsimp only [q]
      exact_mod_cast hcard
    have hcardC : (Fintype.card L : ℂ) = (q : ℂ) ^ (d * m) := by
      dsimp only [q]
      exact_mod_cast hcard
    have htraceL := htrace L
    rw [hdim] at htraceL
    have hqC : (Fintype.card K : ℂ) = (q : ℂ) := by
      simp only [q, Complex.ofReal_natCast]
    rw [hqC] at htraceL
    have hpower : (q : ℂ) ^ (2 * (d * m)) = ((q : ℂ) ^ (d * m)) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm (d * m) 2]
    have heq :
        (Nat.card (zeroPoints (map (algebraMap K L) F)) : ℂ) -
            (1 + (Fintype.card L : ℂ) + (Fintype.card L : ℂ) ^ 2) =
          error q a b c (d * m) := by
      rw [htraceL, hcardC, hpower]
      unfold error
      ring
    have hpot := hpotential L (algebraMap E L)
    have hmaps : (algebraMap E L).comp (algebraMap K E) = algebraMap K L := rfl
    rw [hmaps] at hpot
    have hnorm :
        ‖(Nat.card (zeroPoints (map (algebraMap K L) F)) : ℂ) -
            (1 + (Fintype.card L : ℂ) + (Fintype.card L : ℂ) ^ 2)‖ =
          |(Nat.card (zeroPoints (map (algebraMap K L) F)) : ℝ) -
            ((Fintype.card L : ℝ) ^ 2 + (Fintype.card L : ℝ) + 1)| := by
      rw [show (Nat.card (zeroPoints (map (algebraMap K L) F)) : ℂ) -
          (1 + (Fintype.card L : ℂ) + (Fintype.card L : ℂ) ^ 2) =
          (((Nat.card (zeroPoints (map (algebraMap K L) F)) : ℝ) -
            ((Fintype.card L : ℝ) ^ 2 + (Fintype.card L : ℝ) + 1)) : ℂ) by
        push_cast
        ring]
      convert (Complex.norm_real ((Nat.card (zeroPoints (map (algebraMap K L) F)) : ℝ) -
          ((Fintype.card L : ℝ) ^ 2 + (Fintype.card L : ℝ) + 1))).trans
          (Real.norm_eq_abs _) using 1 <;> push_cast <;> ring
    rw [← heq, hnorm]
    simpa only [hcardR, pow_mul] using hpot
  have hfinal := error_bound q hq a b c ha hb d hd C hbound 1
  have htraceK := htrace K
  simp only [Module.finrank_self, pow_one, mul_one] at htraceK
  have hqC : (Fintype.card K : ℂ) = (q : ℂ) := by
    simp only [q, Complex.ofReal_natCast]
  rw [hqC] at htraceK
  have heq : error q a b c 1 =
      (((Nat.card (zeroPoints F) : ℝ) - (q ^ 2 + q + 1)) : ℂ) := by
    simp only [Algebra.algebraMap_self, map_id] at htraceK
    simp only [error, pow_one]
    push_cast
    linear_combination -htraceK
  have hnorm : ‖error q a b c 1‖ =
      |(Nat.card (zeroPoints F) : ℝ) - (q ^ 2 + q + 1)| := by
    rw [heq]
    convert (Complex.norm_real ((Nat.card (zeroPoints F) : ℝ) - (q ^ 2 + q + 1))).trans
        (Real.norm_eq_abs _) using 1 <;> push_cast <;> ring
  rw [hnorm, pow_one] at hfinal
  have hsizeR : (n₁ : ℝ) + n₂ + n₃ + 1 ≤ 23328 := by
    have hs : (n₁ : ℝ) + n₂ + n₃ ≤ 23326 := by exact_mod_cast hsize
    linarith
  exact hfinal.trans (mul_le_mul_of_nonneg_right hsizeR hq.le)

end CubicTenVariables.CubicSurfaceAmplificationFromZeta
