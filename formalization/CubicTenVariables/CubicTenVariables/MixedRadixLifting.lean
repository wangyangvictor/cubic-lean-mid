import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual mixed-radix residue decompositions for lifting

The representative of `(y,h)` is the natural number `y + M*h` in `Fin(A*M)`.
These are finite-type equivalences, not ring homomorphisms from a smaller
residue ring to a larger one. The unit criterion requires only `A ∣ M`.
The equivalences themselves need no positivity assumptions and include
modulus one and empty coordinate types.
-/

namespace CubicTenVariables.MixedRadixLifting

open scoped BigOperators

/-- The actual base-`M` representative with low digit first. -/
def mixedRadixEquiv (A M : ℕ) : Fin M × Fin A ≃ Fin (A * M) :=
  (Equiv.prodComm (Fin M) (Fin A)).trans finProdFinEquiv

@[simp] theorem mixedRadixEquiv_val (A M : ℕ) (y : Fin M) (h : Fin A) :
    (mixedRadixEquiv A M (y, h)).val = y.val + M * h.val := rfl

@[simp] theorem mixedRadixEquiv_symm_fst_val (A M : ℕ) (x : Fin (A * M)) :
    ((mixedRadixEquiv A M).symm x).1.val = x.val % M := rfl

@[simp] theorem mixedRadixEquiv_symm_snd_val (A M : ℕ) (x : Fin (A * M)) :
    ((mixedRadixEquiv A M).symm x).2.val = x.val / M := rfl

/-- The same representative equality after the actual natural-to-integer cast. -/
theorem mixedRadixEquiv_intCast (A M : ℕ) (y : Fin M) (h : Fin A) :
    ((mixedRadixEquiv A M (y, h)).val : ℤ) = (y.val : ℤ) + (M : ℤ) * h.val := by
  rw [mixedRadixEquiv_val]
  push_cast
  rfl

/-- Coordinatewise mixed-radix decomposition, with low and high digit vectors separated. -/
def mixedRadixVectorEquiv (n A M : ℕ) :
    ((Fin n → Fin M) × (Fin n → Fin A)) ≃ (Fin n → Fin (A * M)) :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin M) (fun _ => Fin A)).symm.trans
    (Equiv.piCongrRight fun _ => mixedRadixEquiv A M)

@[simp] theorem mixedRadixVectorEquiv_apply (n A M : ℕ)
    (y : Fin n → Fin M) (h : Fin n → Fin A) (i : Fin n) :
    mixedRadixVectorEquiv n A M (y, h) i = mixedRadixEquiv A M (y i, h i) := rfl

@[simp] theorem mixedRadixVectorEquiv_val (n A M : ℕ)
    (y : Fin n → Fin M) (h : Fin n → Fin A) (i : Fin n) :
    (mixedRadixVectorEquiv n A M (y, h) i).val = (y i).val + M * (h i).val := rfl

/-- The actual integer lift of the decomposed vector is `y + M*h`. -/
theorem mixedRadixVectorEquiv_intCast (n A M : ℕ)
    (y : Fin n → Fin M) (h : Fin n → Fin A) :
    (fun i => ((mixedRadixVectorEquiv n A M (y, h) i).val : ℤ)) =
      (fun i => ((y i).val : ℤ)) + (M : ℤ) • (fun i => ((h i).val : ℤ)) := by
  ext i
  exact mixedRadixEquiv_intCast A M (y i) (h i)

/-- Literal finite-sum reindexing for one residue representative. -/
theorem sum_mixedRadix {S : Type*} [AddCommMonoid S] (A M : ℕ)
    (f : Fin (A * M) → S) :
    (∑ x, f x) = ∑ y : Fin M, ∑ h : Fin A, f (mixedRadixEquiv A M (y, h)) := by
  rw [← (mixedRadixEquiv A M).sum_comp f, Fintype.sum_prod_type]

/-- Literal finite-sum reindexing for the entire vector. -/
theorem sum_mixedRadixVector {S : Type*} [AddCommMonoid S] (n A M : ℕ)
    (f : (Fin n → Fin (A * M)) → S) :
    (∑ x, f x) = ∑ y : Fin n → Fin M, ∑ h : Fin n → Fin A,
      f (mixedRadixVectorEquiv n A M (y, h)) := by
  rw [← (mixedRadixVectorEquiv n A M).sum_comp f, Fintype.sum_prod_type]

/-- Since `A ∣ M`, adjoining `M*e` creates no new prime divisor obstruction
to being a unit modulo `A*M`. This is the exact unit criterion for first lifting. -/
theorem coprime_add_mul_iff_of_dvd (A M a₀ e : ℕ) (hAM : A ∣ M) :
    Nat.Coprime (a₀ + M * e) (A * M) ↔ Nat.Coprime a₀ M := by
  rw [Nat.coprime_mul_iff_right, Nat.coprime_add_mul_left_left]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    exact ((Nat.coprime_add_mul_left_left a₀ M e).mpr h).of_dvd_right hAM

/-- The unit test on the actual mixed-radix representative depends only on its low digit. -/
theorem coprime_mixedRadix_iff (A M : ℕ) (hAM : A ∣ M)
    (a₀ : Fin M) (e : Fin A) :
    Nat.Coprime (mixedRadixEquiv A M (a₀, e)).val (A * M) ↔
      Nat.Coprime a₀.val M := by
  rw [mixedRadixEquiv_val]
  exact coprime_add_mul_iff_of_dvd A M a₀.val e.val hAM

/-- In the source's split `M=A*T`, the only divisibility hypothesis is automatic. -/
theorem coprime_firstLift_iff (A T a₀ e : ℕ) :
    Nat.Coprime (a₀ + (A * T) * e) (A ^ 2 * T) ↔ Nat.Coprime a₀ (A * T) := by
  simpa only [pow_two, mul_assoc] using
    coprime_add_mul_iff_of_dvd A (A * T) a₀ e (dvd_mul_right A T)

end CubicTenVariables.MixedRadixLifting
