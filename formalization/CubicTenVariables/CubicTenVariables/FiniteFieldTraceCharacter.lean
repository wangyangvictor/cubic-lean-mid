import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Actual additive characters pulled back by finite-field trace. Trace
surjectivity follows from mathlib's proved finite separable extension
theorem; it is not supplied as an assumption. The tower and cardinality
adapters keep the actual algebra trace and the canonical prime-field map. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.FiniteFieldTraceCharacter

open scoped BigOperators

/-- Pullback along the actual field trace, with no scalar normalization. -/
def traceCharacter {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ψ : AddChar K ℂ) : AddChar L ℂ :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

@[simp] theorem traceCharacter_apply {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ψ : AddChar K ℂ) (x : L) :
    traceCharacter (L := L) ψ x = ψ (Algebra.trace K L x) := rfl

/-- Every extension between finite fields has surjective trace, even
when the characteristic divides the extension degree. -/
theorem trace_surjective (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L] :
    Function.Surjective (Algebra.trace K L) := by
  haveI : Finite K := Finite.of_injective (algebraMap K L) (algebraMap K L).injective
  exact Algebra.trace_surjective K L

theorem traceCharacter_ne_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Finite L] (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) : traceCharacter (L := L) ψ ≠ 1 := by
  intro hc
  apply hψ
  ext x
  obtain ⟨y,hy⟩ := trace_surjective K L x
  have he := congrArg (fun χ : AddChar L ℂ => χ y) hc
  simpa only [traceCharacter_apply,hy,AddChar.one_apply] using he

/-- Trace in a finite-field tower is exactly transitive. -/
theorem trace_tower {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Finite M]
    (x : M) : Algebra.trace K L (Algebra.trace L M x) = Algebra.trace K M x := by
  haveI : Finite L := Finite.of_injective (algebraMap L M) (algebraMap L M).injective
  exact Algebra.trace_trace x

/-- Character extension in stages agrees with direct extension. -/
theorem traceCharacter_tower {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Finite M]
    (ψ : AddChar K ℂ) :
    traceCharacter (L := M) (traceCharacter (L := L) ψ) = traceCharacter (L := M) ψ := by
  ext x
  simp only [traceCharacter_apply,trace_tower]

/-- The extension of a character of F_p by the trace along the canonical
F_p-algebra structure on a field of characteristic p. -/
def primeTraceCharacter (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    (ψ : AddChar (ZMod p) ℂ) : AddChar K ℂ :=
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  traceCharacter ψ

theorem primeTraceCharacter_ne_one (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Finite K] [CharP K p]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) : primeTraceCharacter p K ψ ≠ 1 := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  exact traceCharacter_ne_one ψ hψ

/-- The exact extension-degree adapter, with the canonical prime field. -/
theorem finrank_eq_of_card (p a : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [CharP K p] (hcard : Fintype.card K = p^a) :
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    Module.finrank (ZMod p) K = a := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  exact (FiniteField.pow_finrank_eq_card p K).trans hcard

/-- On a degree-a finite extension, the trace is literally the sum of
the first a iterates of the p-power Frobenius. -/
theorem prime_trace_eq_sum_pow (p a : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Fintype K] [CharP K p] (hcard : Fintype.card K = p^a)
    (x : K) :
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    algebraMap (ZMod p) K (Algebra.trace (ZMod p) K x) =
      ∑ i ∈ Finset.range a, x^(p^i) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  simpa only [finrank_eq_of_card p a K hcard, Nat.card_zmod] using
    FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) K x

/-- The actual Artin--Schreier extension characters in any family of
finite extensions remain nontrivial, with no cardinality assumption at zero. -/
theorem family_nontrivial (p : ℕ) [Fact p.Prime]
    (K : ℕ → Type*) [∀ a, Field (K a)] [∀ a, Finite (K a)] [∀ a, CharP (K a) p]
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1) :
    ∀ a, primeTraceCharacter p (K a) ψ ≠ 1 :=
  fun a => primeTraceCharacter_ne_one p (K a) ψ hψ

end CubicTenVariables.FiniteFieldTraceCharacter
