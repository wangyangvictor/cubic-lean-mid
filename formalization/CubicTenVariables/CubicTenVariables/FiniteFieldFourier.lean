import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Mul

/-! Exact finite-field Fourier identities for a polynomial zero set.

Both sums are literal finite sums with the positive phase `a F(x) + v·x`.
At nonzero frequency, the complete sum over nonzero `a` is the field
cardinality times the Fourier sum over the polynomial's zero set. No degree,
smoothness, sheaf, or literature input is used. The adapter to this project's
integer-representative complex exponential sums is a separate statement and
is not supplied or assumed here.
-/

noncomputable section
namespace CubicTenVariables.FiniteFieldFourier
open MvPolynomial
open scoped BigOperators

variable {k : Type*} [Field k] [Fintype k] {n : ℕ}

/-- Sum over every nonzero scalar and every affine vector, with the literal
positive polynomial and linear phases. -/
def completeSum (ψ : AddChar k ℂ) (F : MvPolynomial (Fin n) k)
    (v : Fin n → k) : ℂ := by
  classical
  exact ∑ a ∈ Finset.univ.filter (fun a : k => a ≠ 0),
    ∑ x : Fin n → k, ψ (a * eval x F + dotProduct v x)

/-- Fourier sum over all affine zeros of `F`, including the origin when it
is a zero. This definition imposes no homogeneity assumption. -/
def zeroFiberSum (ψ : AddChar k ℂ) (F : MvPolynomial (Fin n) k)
    (v : Fin n → k) : ℂ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x : Fin n → k => eval x F = 0),
    ψ (dotProduct v x)

/-- The character obtained by composing with the actual linear phase. -/
def linearCharacter (ψ : AddChar k ℂ) (v : Fin n → k) :
    AddChar (Fin n → k) ℂ where
  toFun x := ψ (dotProduct v x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [dotProduct_add, ψ.map_add_eq_mul]

omit [Fintype k] in
@[simp] theorem linearCharacter_apply (ψ : AddChar k ℂ) (v x : Fin n → k) :
    linearCharacter ψ v x = ψ (dotProduct v x) := rfl

omit [Fintype k] in
/-- A nonzero linear phase maps onto the field, so it preserves
nontriviality of the given character. -/
theorem linearCharacter_ne_one (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (v : Fin n → k) (hv : v ≠ 0) : linearCharacter ψ v ≠ 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hz
    exact hv (funext hz)
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.mp hψ
  apply AddChar.ne_one_iff.mpr
  refine ⟨Pi.single j (c / v j), ?_⟩
  change ψ (dotProduct v (Pi.single j (c / v j))) ≠ 1
  have he : dotProduct v (Pi.single j (c / v j)) = c := by
    rw [dotProduct_single]
    field_simp
  rw [he]
  exact hc

/-- Character orthogonality on the full affine vector space at every
nonzero frequency. -/
theorem sum_linear_phase_eq_zero (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (v : Fin n → k) (hv : v ≠ 0) :
    (∑ x : Fin n → k, ψ (dotProduct v x)) = 0 :=
  AddChar.sum_eq_zero_of_ne_one (linearCharacter_ne_one ψ hψ v hv)

/-- Scalar character orthogonality with its cardinality normalization. -/
theorem sum_scalar_phase [DecidableEq k] (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (b : k) :
    (∑ a : k, ψ (a * b)) = if b = 0 then (Fintype.card k : ℂ) else 0 := by
  classical
  by_cases hb : b = 0
  · simp [hb]
  · simpa [hb] using (AddChar.sum_mulShift b (AddChar.IsPrimitive.of_ne_one hψ))

/-- The exact identity at every frequency, retaining the contribution of
the omitted scalar `a=0` explicitly. -/
theorem completeSum_add_linear_phase (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (v : Fin n → k) :
    completeSum ψ F v + ∑ x : Fin n → k, ψ (dotProduct v x) =
      (Fintype.card k : ℂ) * zeroFiberSum ψ F v := by
  classical
  calc
    completeSum ψ F v + ∑ x : Fin n → k, ψ (dotProduct v x) =
        ∑ a : k, ∑ x : Fin n → k, ψ (a * eval x F + dotProduct v x) := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun a : k => a ≠ 0)
        (fun a => ∑ x : Fin n → k, ψ (a * eval x F + dotProduct v x))
      simpa [completeSum, Finset.sum_filter] using h
    _ = ∑ x : Fin n → k, ∑ a : k, ψ (a * eval x F + dotProduct v x) :=
      Finset.sum_comm
    _ = (Fintype.card k : ℂ) * zeroFiberSum ψ F v := by
      simp_rw [ψ.map_add_eq_mul, ← Finset.sum_mul, sum_scalar_phase ψ hψ]
      simp [zeroFiberSum, Finset.sum_filter, Finset.mul_sum, ite_mul, mul_ite]

/-- The complete finite-field exponential sum is exactly `q` times the
Fourier sum over the polynomial zero set when the frequency is nonzero. -/
theorem completeSum_eq_card_mul_zeroFiberSum (ψ : AddChar k ℂ) (hψ : ψ ≠ 1)
    (F : MvPolynomial (Fin n) k) (v : Fin n → k) (hv : v ≠ 0) :
    completeSum ψ F v = (Fintype.card k : ℂ) * zeroFiberSum ψ F v := by
  have h := completeSum_add_linear_phase ψ hψ F v
  rw [sum_linear_phase_eq_zero ψ hψ v hv, add_zero] at h
  exact h

end CubicTenVariables.FiniteFieldFourier
