import CubicTenVariables.ExponentialSums
import CubicTenVariables.FiniteFieldFourier
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Exact normalization of the integer-representative sums at a prime.

The project exponential is proved equal to mathlib's standard additive
character, including its positive sign and factor `2π/p`. Explicit residue
equivalences and polynomial-evaluation reduction then identify the literal
finite sums. Character orthogonality supplies the factor `p` at every
frequency whose reduction modulo `p` is nonzero. No estimate or geometric
input is used. -/

noncomputable section
namespace CubicTenVariables.PrimeSumAdapter
open MvPolynomial
open scoped BigOperators

/-- The chosen `Fin q` representatives are bijective with actual residues. -/
def finResidueEquiv (q : ℕ) [NeZero q] : Fin q ≃ ZMod q where
  toFun a := (a.val : ZMod q)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.is_lt)
  right_inv a := ZMod.natCast_zmod_val a

@[simp] theorem finResidueEquiv_apply (q : ℕ) [NeZero q] (a : Fin q) :
    finResidueEquiv q a = (a.val : ZMod q) := rfl

/-- Coordinatewise reduction of the chosen finite representatives. -/
def vectorResidueEquiv (q n : ℕ) [NeZero q] :
    (Fin n → Fin q) ≃ (Fin n → ZMod q) :=
  Equiv.piCongrRight fun _ => finResidueEquiv q

@[simp] theorem vectorResidueEquiv_apply (q n : ℕ) [NeZero q]
    (x : Fin n → Fin q) :
    vectorResidueEquiv q n x = fun i => ((x i).val : ZMod q) := rfl

/-- Exact project-to-mathlib character normalization for every positive
modulus and every integer phase, including negative representatives. -/
theorem residueExponential_eq_stdAddChar (q : ℕ) [NeZero q] (b : ℤ) :
    residueExponential q b = ZMod.stdAddChar (b : ZMod q) := by
  simpa only [residueExponential] using (ZMod.stdAddChar_coe (N := q) b).symm

/-- Evaluating over the integer representatives and then reducing agrees
with reducing coefficients and coordinates before evaluation. -/
theorem cast_eval_fin {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (x : Fin n → Fin q) :
    ((eval (fun i => ((x i).val : ℤ)) F : ℤ) : ZMod q) =
      eval (fun i => ((x i).val : ZMod q)) (map (Int.castRingHom (ZMod q)) F) := by
  simpa only [Function.comp_def, Int.coe_castRingHom, Int.cast_natCast] using
    MvPolynomial.map_eval (Int.castRingHom (ZMod q)) (fun i => ((x i).val : ℤ)) F

theorem cast_completeSumPhase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (a : Fin q) (x : Fin n → Fin q) (v : Fin n → ℤ) :
    (completeSumPhase F a x v : ZMod q) =
      (a.val : ZMod q) *
        eval (fun i => ((x i).val : ZMod q)) (map (Int.castRingHom (ZMod q)) F) +
      dotProduct (fun i => (v i : ZMod q)) (fun i => ((x i).val : ZMod q)) := by
  simp only [completeSumPhase, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Int.cast_sum, cast_eval_fin, dotProduct]

theorem residueExponential_completeSumPhase {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) [NeZero q] (a : Fin q) (x : Fin n → Fin q) (v : Fin n → ℤ) :
    residueExponential q (completeSumPhase F a x v) =
      ZMod.stdAddChar ((a.val : ZMod q) *
        eval (fun i => ((x i).val : ZMod q)) (map (Int.castRingHom (ZMod q)) F) +
        dotProduct (fun i => (v i : ZMod q)) (fun i => ((x i).val : ZMod q))) := by
  rw [residueExponential_eq_stdAddChar, cast_completeSumPhase]

theorem coprime_prime_iff_residue_ne_zero (p : ℕ) [Fact p.Prime] (a : Fin p) :
    Nat.Coprime a.val p ↔ (a.val : ZMod p) ≠ 0 := by
  rw [Nat.coprime_comm, (Fact.out : p.Prime).coprime_iff_not_dvd,
    ne_eq, ZMod.natCast_eq_zero_iff]

/-- The standard prime-field character is nontrivial, with no character
nontriviality premise left to the caller. -/
theorem stdAddChar_ne_one (p : ℕ) [Fact p.Prime] :
    (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
  intro h
  have he : ZMod.stdAddChar (1 : ZMod p) = ZMod.stdAddChar (0 : ZMod p) := by
    simp [h]
  exact one_ne_zero (ZMod.injective_stdAddChar he)

/-- The literal integer-representative complete sum is exactly the
finite-field sum, without any change in exponential normalization. -/
theorem completeCubicSum_eq_finiteFieldCompleteSum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    completeCubicSum F p v = FiniteFieldFourier.completeSum ZMod.stdAddChar
      (map (Int.castRingHom (ZMod p)) F) (fun i => (v i : ZMod p)) := by
  classical
  unfold completeCubicSum FiniteFieldFourier.completeSum
  rw [Finset.sum_filter]
  apply Fintype.sum_equiv (finResidueEquiv p) _ _
  intro a
  simp only [finResidueEquiv_apply, coprime_prime_iff_residue_ne_zero]
  split_ifs
  · apply Fintype.sum_equiv (vectorResidueEquiv p n) _ _
    intro x
    exact residueExponential_completeSumPhase F p a x v
  · rfl

/-- The exact prime factor and actual affine zero-fiber sum at every
frequency whose reduction modulo the prime is nonzero. -/
theorem completeCubicSum_eq_prime_mul_zeroFiberSum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    completeCubicSum F p v = (p : ℂ) * FiniteFieldFourier.zeroFiberSum ZMod.stdAddChar
      (map (Int.castRingHom (ZMod p)) F) (fun i => (v i : ZMod p)) := by
  rw [completeCubicSum_eq_finiteFieldCompleteSum]
  simpa only [ZMod.card] using FiniteFieldFourier.completeSum_eq_card_mul_zeroFiberSum
    ZMod.stdAddChar (stdAddChar_ne_one p) (map (Int.castRingHom (ZMod p)) F)
    (fun i => (v i : ZMod p)) hv

/-- The same zero-fiber Fourier sum, using only the original finite integer
representatives and the project's literal complex exponential. -/
def representativeZeroFiberSum {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) (v : Fin n → ℤ) : ℂ := by
  classical
  exact ∑ x : Fin n → Fin q,
    if ((eval (fun i => ((x i).val : ℤ)) F : ℤ) : ZMod q) = 0 then
      residueExponential q (∑ i, v i * (x i).val)
    else 0

theorem representativeZeroFiberSum_eq_finiteFieldZeroFiberSum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ) :
    representativeZeroFiberSum F p v = FiniteFieldFourier.zeroFiberSum ZMod.stdAddChar
      (map (Int.castRingHom (ZMod p)) F) (fun i => (v i : ZMod p)) := by
  classical
  unfold representativeZeroFiberSum FiniteFieldFourier.zeroFiberSum
  rw [Finset.sum_filter]
  apply Fintype.sum_equiv (vectorResidueEquiv p n) _ _
  intro x
  simp only [cast_eval_fin, vectorResidueEquiv_apply]
  split_ifs
  · rw [residueExponential_eq_stdAddChar]
    congr 1
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, dotProduct]
  · rfl

/-- Entirely in the original integer-representative normalization, the
prime complete sum is `p` times the linear-phase sum over modular zeros. -/
theorem completeCubicSum_eq_prime_mul_representativeZeroFiberSum {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (p : ℕ) [Fact p.Prime] (v : Fin n → ℤ)
    (hv : (fun i => (v i : ZMod p)) ≠ 0) :
    completeCubicSum F p v = (p : ℂ) * representativeZeroFiberSum F p v := by
  rw [representativeZeroFiberSum_eq_finiteFieldZeroFiberSum]
  exact completeCubicSum_eq_prime_mul_zeroFiberSum F p v hv

end CubicTenVariables.PrimeSumAdapter
