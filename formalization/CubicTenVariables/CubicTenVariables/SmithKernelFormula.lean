import CubicTenVariables.MatrixSmithExistence
import CubicTenVariables.ModularKernelCardinality

/-! Exact kernel cardinalities for reductions of arbitrary integer matrices.
The diagonal and both unimodular changes are proved to exist over ℤ; the
same diagonal works simultaneously for every positive residue modulus. -/

noncomputable section
namespace CubicTenVariables.SmithKernelFormula
open MatrixSmithKernel MatrixSmithExistence ModularKernelCardinality
open scoped BigOperators

/-- The exact gcd formula from a displayed actual integral diagonalization. -/
theorem card_kernel_eq_prod_gcd_of_int_equivalence (q : ℕ) [NeZero q] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d) :
    Nat.card {x : Fin n → ZMod q //
      (B.map (Int.castRingHom (ZMod q))).mulVec x = 0} =
      ∏ i, Nat.gcd (d i).natAbs q :=
  (card_kernel_eq_diagonal_of_int_equivalence q B d U V hD).trans
    (card_diagonal_int_kernel q d)

/-- For every integer matrix there are actual integral unimodular changes
and a single diagonal, valid for the exact kernel count at all positive moduli. -/
theorem exists_diagonalization_and_kernel_formula {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) (d : Fin n → ℤ),
      (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d ∧
      ∀ q : ℕ, 0 < q →
        Nat.card {x : Fin n → ZMod q //
          (B.map (Int.castRingHom (ZMod q))).mulVec x = 0} =
          ∏ i, Nat.gcd (d i).natAbs q := by
  obtain ⟨U, V, d, hD⟩ := exists_integer_diagonalization B
  refine ⟨U, V, d, hD, ?_⟩
  intro q hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  exact card_kernel_eq_prod_gcd_of_int_equivalence q B d U V hD

/-- The modulus-independent diagonal kernel-count endpoint, with no
normal-form data, rank bound, or nonsingularity assumption supplied as input. -/
theorem exists_kernel_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ d : Fin n → ℤ, ∀ q : ℕ, 0 < q →
      Nat.card {x : Fin n → ZMod q //
        (B.map (Int.castRingHom (ZMod q))).mulVec x = 0} =
        ∏ i, Nat.gcd (d i).natAbs q := by
  obtain ⟨U, V, d, hD, hd⟩ := exists_diagonalization_and_kernel_formula B
  exact ⟨d, hd⟩

end CubicTenVariables.SmithKernelFormula
