import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact cardinalities of prime-power reduction fibers

The reduction map is the actual `ZMod.castHom`. Every scalar fiber from
modulus `p^s` to modulus `p^t` has cardinality `p^(s-t)` when `t ≤ s`.
The coordinatewise product fibers therefore have cardinality
`p^((s-t)*r)`. In particular reduction to `p^(s-A)` has at most `p^(A*r)`
lifts of any fixed `r`-coordinate residue vector. The statements include
`t = 0`, `r = 0`, and `A > s`, with natural-number truncated subtraction.
No local-solubility, analytic, or literature input is used.
-/

noncomputable section

namespace CubicTenVariables.PrimePowerFibers

/-- Literal reduction of residue classes along divisibility of prime powers. -/
def reduction (p : ℕ) {s t : ℕ} (hts : t ≤ s) :
    ZMod (p ^ s) →+* ZMod (p ^ t) :=
  ZMod.castHom (pow_dvd_pow p hts) (ZMod (p ^ t))

theorem reduction_surjective (p : ℕ) {s t : ℕ} (hts : t ≤ s) :
    Function.Surjective (reduction p hts) :=
  ZMod.castHom_surjective _

/-- Every fiber of a surjective homomorphism of finite additive groups
has the common cardinality determined by the two group cardinalities. -/
theorem card_fiber_mul_card_of_surjective
    {G H : Type*} [AddGroup G] [AddGroup H] [Finite G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (b : H) :
    Nat.card {x : G // f x = b} * Nat.card H = Nat.card G := by
  classical
  have hsame (c : H) : Nat.card {x : G // f x = c} = Nat.card {x : G // f x = b} :=
    Nat.card_congr (AddMonoidHom.fiberEquivOfSurjective hf c b)
  have hsum := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at hsum
  simpa only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, mul_comm] using hsum

/-- Exact scalar fiber cardinality, also for the one-element target `ZMod 1`. -/
theorem card_reduction_fiber (p : ℕ) [Fact p.Prime] {s t : ℕ}
    (hts : t ≤ s) (b : ZMod (p ^ t)) :
    Nat.card {x : ZMod (p ^ s) // reduction p hts x = b} = p ^ (s - t) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hmul := card_fiber_mul_card_of_surjective (reduction p hts).toAddMonoidHom
    (reduction_surjective p hts) b
  rw [Nat.card_zmod, Nat.card_zmod] at hmul
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hp) t)
  calc
    Nat.card {x : ZMod (p ^ s) // reduction p hts x = b} * p ^ t = p ^ s := hmul
    _ = p ^ (s - t) * p ^ t := by rw [← pow_add, Nat.sub_add_cancel hts]

/-- Exact cardinality of a coordinatewise reduction fiber. -/
theorem card_vector_reduction_fiber (p : ℕ) [Fact p.Prime] {s t : ℕ}
    (hts : t ≤ s) (r : ℕ) (b : Fin r → ZMod (p ^ t)) :
    Nat.card {v : Fin r → ZMod (p ^ s) // ∀ i, reduction p hts (v i) = b i} =
      p ^ ((s - t) * r) := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : Fin r) (x : ZMod (p ^ s)) => reduction p hts x = b i)), Nat.card_pi]
  simp only [card_reduction_fiber p hts, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]

/-- Uniform bound for truncating at `s-A`; no restriction `A ≤ s` is needed. -/
theorem card_vector_truncation_fiber_le (p : ℕ) [Fact p.Prime]
    (s A r : ℕ) (b : Fin r → ZMod (p ^ (s - A))) :
    Nat.card {v : Fin r → ZMod (p ^ s) //
      ∀ i, reduction p (Nat.sub_le s A) (v i) = b i} ≤ p ^ (A * r) := by
  rw [card_vector_reduction_fiber]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  exact Nat.mul_le_mul_right r (by omega : s - (s - A) ≤ A)

/-- The same exact vector count expressed as the cardinality of a literal
finite filter, for applications to finite residue-class counts. -/
theorem card_filter_vector_reduction_fiber (p : ℕ) [Fact p.Prime] {s t : ℕ}
    (hts : t ≤ s) (r : ℕ) (b : Fin r → ZMod (p ^ t)) :
    (Finset.univ.filter (fun v : Fin r → ZMod (p ^ s) =>
      ∀ i, reduction p hts (v i) = b i)).card = p ^ ((s - t) * r) := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    card_vector_reduction_fiber p hts r b

/-- The literal finite-filter truncation bound. -/
theorem card_filter_vector_truncation_fiber_le (p : ℕ) [Fact p.Prime]
    (s A r : ℕ) (b : Fin r → ZMod (p ^ (s - A))) :
    (Finset.univ.filter (fun v : Fin r → ZMod (p ^ s) =>
      ∀ i, reduction p (Nat.sub_le s A) (v i) = b i)).card ≤ p ^ (A * r) := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    card_vector_truncation_fiber_le p s A r b

end CubicTenVariables.PrimePowerFibers
