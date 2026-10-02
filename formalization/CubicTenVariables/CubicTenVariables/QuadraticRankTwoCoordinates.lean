import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Coordinate reduction of an actual symmetric matrix of rank at least two.
The two nondegenerate coordinates are selected inside a full invertible
basis. The finite-field basis is then lifted entrywise to an integral matrix.
No diagonalization or coordinate-reduction premise is assumed. -/

noncomputable section
namespace CubicTenVariables.QuadraticRankTwoCoordinates
open Matrix Module

/-- Over a field of characteristic different from two, two coordinates of
an invertible basis have a nonsingular principal Gram block whenever the
actual symmetric matrix has rank at least two. -/
theorem field_coordinates {K : Type*} [Field K] [Invertible (2 : K)]
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : M.IsSymm)
    (hrank : 2 ≤ M.rank) :
    ∃ A : Matrix (Fin n) (Fin n) K, ∃ e : Fin 2 ↪ Fin n,
      A.det ≠ 0 ∧ ((A.transpose * M * A).submatrix e e).det ≠ 0 := by
  classical
  let B := M.toBilin'
  have hB : LinearMap.IsSymm B := by
    constructor
    intro x y
    change B x y = B y x
    simp only [B, Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM.apply i j]
    ring
  obtain ⟨b, hb⟩ : ∃ b : Basis (Fin n) K (Fin n → K), LinearMap.IsOrthoᵢ B b := by
    have hd : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
    have h := LinearMap.BilinForm.exists_orthogonal_basis hB
    rw [hd] at h
    exact h
  let b₀ := Pi.basisFun K (Fin n)
  let A := b₀.toMatrix b
  have hA : IsUnit A.det := Matrix.isUnit_det_of_right_inverse
    (b₀.toMatrix_mul_toMatrix_flip b)
  let d : Fin n → K := fun i => B (b i) (b i)
  have hdiag : A.transpose * M * A = Matrix.diagonal d := by
    have he := BilinForm.toMatrix_mul_basis_toMatrix b₀ b B
    have hbase : BilinForm.toMatrix b₀ B = M := by
      change BilinForm.toMatrix b₀ (Matrix.toBilin' M) = M
      rw [show b₀ = Pi.basisFun K (Fin n) from rfl,
        ← Matrix.toBilin_basisFun, BilinForm.toMatrix_toBilin]
    rw [hbase] at he
    rw [show A = b₀.toMatrix b from rfl, he]
    ext i j
    rw [BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact hb hij
  have hdiagRank : (Matrix.diagonal d).rank = M.rank := by
    rw [← hdiag, Matrix.rank_mul_eq_left_of_isUnit_det A _ hA,
      Matrix.rank_mul_eq_right_of_isUnit_det A.transpose M]
    simpa using hA
  have hcard : 1 < Fintype.card {i : Fin n // d i ≠ 0} := by
    rw [← Matrix.rank_diagonal, hdiagRank]
    omega
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  let e : Fin 2 ↪ Fin n :=
    ⟨![i.val, j.val], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩
  refine ⟨A, e, hA.ne_zero, ?_⟩
  rw [hdiag, Matrix.det_fin_two]
  simpa [e, Matrix.submatrix_apply, hij', Ne.symm hij'] using mul_ne_zero i.property j.property

/-- The finite-field endpoint has only primality, oddness, symmetry, and
the actual matrix rank hypothesis. -/
theorem prime_coordinates (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p)) (hM : M.IsSymm)
    (hrank : 2 ≤ M.rank) :
    ∃ A : Matrix (Fin n) (Fin n) (ZMod p), ∃ e : Fin 2 ↪ Fin n,
      A.det ≠ 0 ∧ ((A.transpose * M * A).submatrix e e).det ≠ 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := by simpa using (ZMod.natCast_eq_zero_iff 2 p).mp h
    have he : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left ((Fact.out : p.Prime).ne_one)
    exact hp he
  letI : Invertible (2 : ZMod p) := invertibleOfNonzero htwo
  exact field_coordinates M hM hrank

/-- An integral coordinate matrix invertible modulo p, with an actual
nondegenerate two-coordinate block of its integral congruence matrix. -/
theorem integral_coordinates (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.IsSymm)
    (hrank : 2 ≤ (M.map (Int.castRingHom (ZMod p))).rank) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, ∃ e : Fin 2 ↪ Fin n,
      (A.det : ZMod p) ≠ 0 ∧
      (((A.transpose * M * A).submatrix e e).det : ZMod p) ≠ 0 := by
  classical
  let φ := Int.castRingHom (ZMod p)
  have hM' : (M.map φ).IsSymm := by
    ext i j
    exact congrArg φ (hM.apply i j)
  obtain ⟨U, e, hU, hblock⟩ := prime_coordinates p hp (M.map φ) hM' hrank
  let A : Matrix (Fin n) (Fin n) ℤ := fun i j => (U i j).cast
  have hAU : A.map φ = U := by
    ext i j
    exact ZMod.intCast_zmod_cast (U i j)
  refine ⟨A, e, ?_, ?_⟩
  · change φ A.det ≠ 0
    rw [RingHom.map_det]
    change (A.map φ).det ≠ 0
    rw [hAU]
    exact hU
  · change φ ((A.transpose * M * A).submatrix e e).det ≠ 0
    rw [RingHom.map_det]
    change (((A.transpose * M * A).map φ).submatrix e e).det ≠ 0
    rw [Matrix.map_mul, Matrix.map_mul]
    change (((A.map φ).transpose * M.map φ * A.map φ).submatrix e e).det ≠ 0
    rwa [hAU]

/-- Nonvanishing modulo the prime makes an integral scalar a unit at every
prime-power level, including the one-element level p^0. -/
theorem integer_unit_prime_power (p : ℕ) [Fact p.Prime] (d : ℤ)
    (hd : (d : ZMod p) ≠ 0) (s : ℕ) : IsUnit (d : ZMod (p^s)) := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg d
  all_goals
    have ha : (a : ZMod p) ≠ 0 := by simpa using hd
    have hcop : a.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => ha ((ZMod.natCast_eq_zero_iff a p).mpr h))).symm
    have hu : IsUnit (a : ZMod (p^s)) :=
      (ZMod.isUnit_iff_coprime a (p^s)).mpr (hcop.pow_right s)
    simpa using hu

/-- The lifted integral coordinate change is a bijection on actual residue
vectors at every prime-power level. -/
theorem integral_matrix_bijective_prime_power (p : ℕ) [Fact p.Prime]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : (A.det : ZMod p) ≠ 0)
    (s : ℕ) : Function.Bijective (A.map (Int.castRingHom (ZMod (p^s)))).mulVec := by
  have hdet : IsUnit (A.map (Int.castRingHom (ZMod (p^s)))).det := by
    change IsUnit ((Int.castRingHom (ZMod (p^s))).mapMatrix A).det
    rw [← RingHom.map_det]
    exact integer_unit_prime_power p A.det hA s
  have hsur := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  exact ⟨Finite.injective_iff_surjective.mpr hsur, hsur⟩

/-- Full coordinate package: an actual integral congruence has a
nondegenerate embedded two-coordinate block modulo p, and the chosen
coordinates permute all actual residue vectors modulo every p^s. -/
theorem integral_coordinates_all_levels (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : M.IsSymm)
    (hrank : 2 ≤ (M.map (Int.castRingHom (ZMod p))).rank) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, ∃ e : Fin 2 ↪ Fin n,
      (A.det : ZMod p) ≠ 0 ∧
      (((A.transpose * M * A).submatrix e e).det : ZMod p) ≠ 0 ∧
      ∀ s : ℕ, Function.Bijective (A.map (Int.castRingHom (ZMod (p^s)))).mulVec := by
  obtain ⟨A, e, hA, hblock⟩ := integral_coordinates p hp M hM hrank
  exact ⟨A, e, hA, hblock, integral_matrix_bijective_prime_power p A hA⟩

end CubicTenVariables.QuadraticRankTwoCoordinates
