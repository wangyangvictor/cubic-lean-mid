import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Integral matrix changes of basis preserve literal modular kernels

The transformations are actual units in the integer matrix ring. Their
reductions remain units over every residue ring, so their action gives an
explicit equivalence of the finite kernels. Neither nonsingularity of the
matrix being transformed nor a domain/PID structure on the residue ring
is required.
-/

noncomputable section
namespace CubicTenVariables.MatrixSmithKernel

open Matrix

section Ring
variable {R : Type*} [CommRing R] {n : ℕ}

/-- An invertible matrix kills only the zero vector, over any commutative ring. -/
theorem unit_mulVec_eq_zero_iff (U : (Matrix (Fin n) (Fin n) R)ˣ)
    (x : Fin n → R) : (U : Matrix (Fin n) (Fin n) R).mulVec x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h := congrArg (fun y => (↑U⁻¹ : Matrix (Fin n) (Fin n) R).mulVec y) hx
    simpa only [Matrix.mulVec_mulVec, Units.inv_val, Units.val_inv, Units.inv_mul,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- The equivalence is the literal change of variables `x ↦ V*x`.
The left unit removes redundant invertible equations. -/
def kernelMulEquiv (B : Matrix (Fin n) (Fin n) R)
    (U V : (Matrix (Fin n) (Fin n) R)ˣ) :
    {x : Fin n → R // ((U : Matrix (Fin n) (Fin n) R) * B * V).mulVec x = 0} ≃
      {x : Fin n → R // B.mulVec x = 0} where
  toFun x := ⟨(V : Matrix (Fin n) (Fin n) R).mulVec x,
    (unit_mulVec_eq_zero_iff U _).mp (by
      simpa only [Matrix.mulVec_mulVec, mul_assoc] using x.property)⟩
  invFun x := ⟨(↑V⁻¹ : Matrix (Fin n) (Fin n) R).mulVec x, by
    rw [Matrix.mulVec_mulVec]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← Matrix.mulVec_mulVec, x.property, Matrix.mulVec_zero]⟩
  left_inv x := by
    apply Subtype.ext
    change (↑V⁻¹ : Matrix (Fin n) (Fin n) R).mulVec
      ((V : Matrix (Fin n) (Fin n) R).mulVec x) = x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    apply Subtype.ext
    change (V : Matrix (Fin n) (Fin n) R).mulVec
      ((↑V⁻¹ : Matrix (Fin n) (Fin n) R).mulVec x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/-- The finite-cardinality statement does not require a nonsingular matrix. -/
theorem card_kernel_mul_units (B : Matrix (Fin n) (Fin n) R)
    (U V : (Matrix (Fin n) (Fin n) R)ˣ) :
    Nat.card {x : Fin n → R // ((U : Matrix (Fin n) (Fin n) R) * B * V).mulVec x = 0} =
      Nat.card {x : Fin n → R // B.mulVec x = 0} :=
  Nat.card_congr (kernelMulEquiv B U V)

end Ring

/-- Reduction of an integral unimodular matrix is still invertible,
including composite moduli and modulus one. -/
def reduceUnit (q : ℕ) {n : ℕ} (U : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    (Matrix (Fin n) (Fin n) (ZMod q))ˣ :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod q)) U

@[simp] theorem reduceUnit_val (q : ℕ) {n : ℕ}
    (U : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    (reduceUnit q U : Matrix (Fin n) (Fin n) (ZMod q)) =
      (U : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom (ZMod q)) := rfl

/-- Literal modular-kernel invariance under integer row and column basis changes. -/
theorem card_kernel_int_mul_units (q : ℕ) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    Nat.card {x : Fin n → ZMod q //
      (((U : Matrix (Fin n) (Fin n) ℤ) * B * V).map
        (Int.castRingHom (ZMod q))).mulVec x = 0} =
    Nat.card {x : Fin n → ZMod q //
      (B.map (Int.castRingHom (ZMod q))).mulVec x = 0} := by
  simpa only [reduceUnit_val, Matrix.map_mul] using
    card_kernel_mul_units (B.map (Int.castRingHom (ZMod q))) (reduceUnit q U) (reduceUnit q V)

/-- An actual integral diagonalization identifies the modular kernel with
the kernel of the actual diagonal entries, with no invertibility premise on them. -/
theorem card_kernel_eq_diagonal_of_int_equivalence (q : ℕ) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ)
    (hD : (U : Matrix (Fin n) (Fin n) ℤ) * B * V = Matrix.diagonal d) :
    Nat.card {x : Fin n → ZMod q //
      (B.map (Int.castRingHom (ZMod q))).mulVec x = 0} =
    Nat.card {x : Fin n → ZMod q //
      (Matrix.diagonal (fun i => (d i : ZMod q))).mulVec x = 0} := by
  rw [← card_kernel_int_mul_units q B U V, hD]
  rw [Matrix.diagonal_map (map_zero (Int.castRingHom (ZMod q)))]
  rfl

/-- Smith data for the actual image of an arbitrary integer matrix. Zero and
singular matrices are included. This is an inclusion-diagonalization; it
is not yet a square row/column diagonalization of the original matrix. -/
theorem exists_image_smith_data {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ (r : ℕ) (hr : r ≤ n)
      (b : Module.Basis (Fin n) ℤ (Fin n → ℤ))
      (c : Module.Basis (Fin r) ℤ (LinearMap.range B.mulVecLin))
      (f : Fin r ↪ Fin n) (d : Fin r → ℤ),
      (∀ i, d i ≠ 0) ∧ ∀ i, (c i : Fin n → ℤ) = d i • b (f i) := by
  classical
  obtain ⟨r, s⟩ := (LinearMap.range B.mulVecLin).smithNormalForm (Pi.basisFun ℤ (Fin n))
  have hr : r ≤ n := by
    simpa using Fintype.card_le_of_injective s.f s.f.injective
  refine ⟨r, hr, s.bM, s.bN, s.f, s.a, ?_, s.snf⟩
  intro i hi
  have h := s.snf i
  rw [hi, zero_smul] at h
  exact s.bN.ne_zero i (Subtype.ext h)

end CubicTenVariables.MatrixSmithKernel
