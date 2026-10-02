import CubicTenVariables.WeightedGaussianPoisson
import CubicTenVariables.WeightedHessianRootCRT
import CubicTenVariables.SecondLiftSum

/-! Exact identification of the finite Fourier character produced by
Gaussian summation over the literal stationary congruence classes. -/

noncomputable section
namespace CubicTenVariables.OnionGaussianCharacter
open MvPolynomial WeightedGaussianPoisson WeightedHessianRootCRT PrimeSumAdapter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The integral center of the stationary class v = -a grad F(x) mod c. -/
def stationaryShift {n c : ℕ} (F : MvPolynomial (Fin n) ℤ) (a : ℤ)
    (x : Fin n → Fin c) : Fin n → ℤ :=
  fun i => -a * eval (SecondLiftSum.integerVector x) (pderiv i F)

/-- The actual Hessian weight with only the prescribed partial root condition. -/
def partialWeight {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (c d r : ℕ)
    (x : Fin n → Fin c) : ℝ :=
  if (r : ℤ) ∣ eval (SecondLiftSum.integerVector x) F then
    kernelWeight F d (fun i => ((x i).val : ZMod d)) else 0

theorem partialWeight_nonneg {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d r : ℕ) (x : Fin n → Fin c) : 0 ≤ partialWeight F c d r x := by
  unfold partialWeight
  split_ifs
  · exact kernelWeight_nonneg _ _ _
  · exact le_rfl

/-- Reduction of an integral evaluation allows a different target modulus. -/
theorem cast_eval_integerVector {n c : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (x : Fin n → Fin c) :
    (eval (SecondLiftSum.integerVector x) F : ZMod q) =
      eval₂ (Int.castRingHom (ZMod q)) (fun i => ((x i).val : ZMod q)) F := by
  simpa only [SecondLiftSum.integerVector, Function.comp_def,
    Int.coe_castRingHom, Int.cast_natCast] using
      eval₂_comp (Int.castRingHom (ZMod q)) (SecondLiftSum.integerVector x) F

/-- The Gaussian Fourier phase has precisely the positive 2π/c convention. -/
theorem phase_integer {n : ℕ} (c : ℕ) [NeZero c] (h b : Fin n → ℤ) :
    phase (c : ℝ) h (fun i => (b i : ℝ)) =
      ZMod.stdAddChar ((∑ i, h i*b i : ℤ) : ZMod c) := by
  rw [← residueExponential_eq_stdAddChar]
  unfold phase residueExponential
  congr 1
  push_cast
  rfl

/-- The stationary center contributes the sign -a in the directional phase. -/
theorem phase_stationaryShift {n c : ℕ} (F : MvPolynomial (Fin n) ℤ)
    [NeZero c] (a : ℤ) (x : Fin n → Fin c) (h : Fin n → ℤ) :
    phase (c : ℝ) h (fun i => (stationaryShift F a x i : ℝ)) =
      ZMod.stdAddChar ((-a : ZMod c) *
        WeightedCRTAdapters.directionalPhase F h (fun i => ((x i).val : ZMod c))) := by
  rw [phase_integer]
  congr 1
  simp only [stationaryShift, Int.cast_sum, Int.cast_mul, Int.cast_neg,
    cast_eval_integerVector, WeightedCRTAdapters.directionalPhase, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact character identification after the genuine coordinate residue
equivalence. No homogeneity, anisotropy or unit hypothesis is required. -/
theorem character_eq {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (c d r : ℕ) [NeZero c] (hdc : d ∣ c) (hrc : r ∣ c)
    (a : ℤ) (h : Fin n → ℤ) :
    character (c : ℝ) (fun x i => (stationaryShift F a x i : ℝ))
      (partialWeight F c d r) h =
      partialRootCharacterMass F c d r hdc hrc (-a : ZMod c) h := by
  unfold character partialRootCharacterMass
  apply Fintype.sum_equiv (vectorResidueEquiv c n)
  intro x
  have hz : (r : ℤ) ∣ eval (SecondLiftSum.integerVector x) F ↔
      eval₂ (Int.castRingHom (ZMod r)) (fun i => ((x i).val : ZMod r)) F = 0 := by
    rw [← cast_eval_integerVector, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [phase_stationaryShift, vectorResidueEquiv_apply, map_natCast,
    partialWeight, hz]
  split_ifs <;> simp

end CubicTenVariables.OnionGaussianCharacter
