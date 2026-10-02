import CubicTenVariables.AdmissiblePrimePowerCount
import CubicTenVariables.SecondLiftPhase

/-!
Exact prime-power kernel formulas for the actual coefficient reduction of an
integral Hessian. All formulas use the same displayed integral diagonalization.
There is no cubic, nonsingularity, odd-prime, or residue-ring PID premise.
-/

noncomputable section
namespace CubicTenVariables.HessianResidueKernel

open MvPolynomial HessianTheorem11 PrimePowerKernelProfile
open scoped BigOperators Matrix

/-- Coefficients, evaluation points, and both formal derivatives reduce by
the actual integer coefficient homomorphism. This also holds for modulus zero. -/
theorem hessian_intCast {n : ℕ} (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (y : Fin n → ℤ) :
    (hessian F y).map (Int.castRingHom (ZMod q)) =
      hessian (MvPolynomial.map (Int.castRingHom (ZMod q)) F)
        (fun i => (y i : ZMod q)) := by
  ext i j
  simp only [Matrix.map_apply, hessian, hessianPolynomial, pderiv_map,
    Int.coe_castRingHom, SecondLiftPhase.cast_eval_int]

/-- Truncating a previously truncated valuation gives the valuation at every
lower exponent. No primality is needed for this identity of definitions. -/
theorem truncatedValuation_truncate (p a t : ℕ) (d : ℤ) (ht : t ≤ a) :
    truncatedValuation p t d = min (truncatedValuation p a d) t := by
  by_cases hd : d = 0
  · simp [truncatedValuation, hd, Nat.min_eq_right ht]
  · simp only [truncatedValuation, if_neg hd]
    omega

/-- The literal reduced Hessian kernel from one integral diagonalization. -/
theorem card_hessian_primePower_kernel {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (t : ℕ) :
    Nat.card {x : Fin n → ZMod (p ^ t) //
      (hessian (MvPolynomial.map (Int.castRingHom (ZMod (p ^ t))) F)
        (fun i => (y i : ZMod (p ^ t)))).mulVec x = 0} =
      p ^ (∑ i, truncatedValuation p t (d i)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [← hessian_intCast F (p ^ t) y,
    SmithKernelFormula.card_kernel_eq_prod_gcd_of_int_equivalence
      (p ^ t) (hessian F y) d U V hD]
  simp only [gcd_primePower p t hp]
  exact Finset.prod_pow_eq_pow_sum Finset.univ _ p

/-- Lower prime-power levels use the same diagonal and its valuations already
truncated at the fixed exponent `a`, including zero diagonal entries. -/
theorem card_hessian_primePower_kernel_truncated {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a t : ℕ) (ht : t ≤ a) :
    Nat.card {x : Fin n → ZMod (p ^ t) //
      (hessian (MvPolynomial.map (Int.castRingHom (ZMod (p ^ t))) F)
        (fun i => (y i : ZMod (p ^ t)))).mulVec x = 0} =
      p ^ (∑ i, min (truncatedValuation p a (d i)) t) := by
  rw [card_hessian_primePower_kernel F y U V d hD p hp t]
  simp only [truncatedValuation_truncate p a t _ ht]

/-- Scaling the actual reduced Hessian by `p^b` adds `b` before truncation.
The integral row and column changes are exactly those in `hD`. -/
theorem card_scaled_hessian_primePower_kernel {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (y : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * hessian F y * V = Matrix.diagonal d)
    (p : ℕ) (hp : p.Prime) (a b : ℕ) :
    Nat.card {x : Fin n → ZMod (p ^ a) //
      ((p ^ b : ZMod (p ^ a)) •
        hessian (MvPolynomial.map (Int.castRingHom (ZMod (p ^ a))) F)
          (fun i => (y i : ZMod (p ^ a)))).mulVec x = 0} =
      p ^ (∑ i, min (b + truncatedValuation p a (d i)) a) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [← hessian_intCast F (p ^ a) y]
  have h := AdmissibleSmithCount.card_scaled_kernel_eq_prod_gcd
    (hessian F y) U V d hD (p ^ a) (p ^ b)
  simp_rw [gcd_primePower p a hp,
    AdmissiblePrimePowerCount.truncatedValuation_primePower_mul p a b hp] at h
  simp only [Nat.cast_pow] at h
  rw [h]
  exact Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin n))
    (fun i => min (b + truncatedValuation p a (d i)) a) p

end CubicTenVariables.HessianResidueKernel
