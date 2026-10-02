import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! The generic tuple of at most n normal vectors has full row rank.
The proof uses the determinant of its first k columns, specialized to the
identity matrix. No Bertini or geometric-existence theorem is involved. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GenericNormalTupleRank
open MvPolynomial Matrix

def genericNormalMatrix (k n : ℕ) :
    Matrix (Fin k) (Fin n) (MvPolynomial (Fin (k * n)) ℤ) :=
  fun j i ↦ X (finProdFinEquiv (j, i))

/-- A displayed maximal minor is already a nonzero integer polynomial. -/
theorem first_minor_ne_zero {k n : ℕ} (hkn : k ≤ n) :
    Matrix.det ((genericNormalMatrix k n).submatrix id (Fin.castLE hkn)) ≠ 0 := by
  classical
  let ε : MvPolynomial (Fin (k * n)) ℤ →+* ℤ :=
    eval (fun a ↦ if (finProdFinEquiv.symm a).1.val =
      (finProdFinEquiv.symm a).2.val then 1 else 0)
  have hidentity : ε.mapMatrix
      ((genericNormalMatrix k n).submatrix id (Fin.castLE hkn)) = 1 := by
    ext j i
    change ε (X (finProdFinEquiv (j, Fin.castLE hkn i))) = if j = i then 1 else 0
    simp only [ε, eval_X, Equiv.symm_apply_apply]
    change (if j.val = i.val then (1 : ℤ) else 0) = _
    simp only [Fin.ext_iff]
  have he : ε (Matrix.det
      ((genericNormalMatrix k n).submatrix id (Fin.castLE hkn))) = 1 := by
    rw [RingHom.map_det, hidentity, Matrix.det_one]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

/-- Algebraically independent normal coefficients give full row rank over
every field into which their parameter polynomial ring embeds. -/
theorem rank_map_genericNormalMatrix {k n : ℕ} {K : Type*} [Field K]
    (ι : MvPolynomial (Fin (k * n)) ℤ →+* K) (hι : Function.Injective ι)
    (hkn : k ≤ n) :
    Matrix.rank (Matrix.map (genericNormalMatrix k n) ι) = k := by
  classical
  let A : Matrix (Fin k) (Fin n) K := Matrix.map (genericNormalMatrix k n) ι
  let M := A.submatrix id (Fin.castLE hkn)
  have hdet : Matrix.det M ≠ 0 := by
    have he : Matrix.det M = ι (Matrix.det
        ((genericNormalMatrix k n).submatrix id (Fin.castLE hkn))) :=
      (ι.map_det _).symm
    rw [he]
    exact fun h ↦ first_minor_ne_zero hkn (hι (h.trans (map_zero ι).symm))
  have hrankM : Matrix.rank M = k := by
    simpa using Matrix.rank_of_isUnit M
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hle : Matrix.rank M ≤ Matrix.rank A := by
    have h := Matrix.rank_submatrix_le (Fin.castLE hkn) (Equiv.refl (Fin k)) A.transpose
    change Matrix.rank M.transpose ≤ Matrix.rank A.transpose at h
    simpa only [Matrix.rank_transpose] using h
  have hup : Matrix.rank A ≤ k := Matrix.rank_le_height A
  change Matrix.rank A = k
  omega

end CubicTenVariables.GenericNormalTupleRank
