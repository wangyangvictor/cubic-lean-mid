import HessianTheorem11.Geometry
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Basic

/-! Polynomial Schur vanishing along actual maps into an integral hypersurface.
The proof uses bordered minors and mathlib's Nullstellensatz. -/

noncomputable section
namespace HessianTheorem11.PolynomialSchurVanishing
open Matrix MvPolynomial

section Rank
variable {K : Type*} [Field K]
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

omit [Fintype α] in
/-- Restricting both rows and columns cannot increase the actual matrix rank. -/
theorem rank_submatrix_le (M : Matrix α β K) (f : γ → α) (g : δ → β) :
    (M.submatrix f g).rank ≤ M.rank := by
  calc
    (M.submatrix f g).rank =
        ((M.submatrix f id).transpose.submatrix g id).rank := by
      rw [← Matrix.rank_transpose (M.submatrix f g)]
      rfl
    _ ≤ (M.submatrix f id).transpose.rank :=
      Matrix.rank_submatrix_le g (Equiv.refl γ) _
    _ = (M.submatrix f id).rank := Matrix.rank_transpose _
    _ ≤ M.rank := Matrix.rank_submatrix_le f (Equiv.refl β) M

theorem det_eq_zero_of_rank_lt [DecidableEq α] (M : Matrix α α K)
    (h : M.rank < Fintype.card α) : M.det = 0 := by
  by_contra hn
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hn)
  have hr := Matrix.rank_of_isUnit M hu
  omega

end Rank

section Nullstellensatz
variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]

/-- A polynomial vanishing at every geometric point of a prime hypersurface
vanishes under every ring homomorphism annihilating its defining equation. -/
theorem map_eq_zero_of_hypersurface_vanishing
    (F P : MvPolynomial σ GeometricField) (hF : Irreducible F)
    (φ : MvPolynomial σ GeometricField →+* R) (hφ : φ F = 0)
    (hP : ∀ x : σ → GeometricField, eval x F = 0 → eval x P = 0) : φ P = 0 := by
  let I : Ideal (MvPolynomial σ GeometricField) := Ideal.span {F}
  letI : I.IsPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
  have hm : P ∈ vanishingIdeal GeometricField (zeroLocus GeometricField I) := by
    intro x hx
    apply hP x
    exact hx F (Ideal.subset_span (by simp))
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hm
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hm
  rw [hQ, map_mul, hφ, zero_mul]

end Nullstellensatz

section Bordered
variable {R : Type*} [CommRing R]
variable {α κ : Type*} [Fintype α] [Fintype κ]

/-- A single row and column adjoining the complementary square block. -/
def bordered (A : Matrix α α R) (C : Matrix α κ R)
    (D : Matrix κ α R) (K : Matrix κ κ R) (i j : α) :
    Matrix (Fin 1 ⊕ κ) (Fin 1 ⊕ κ) R :=
  Matrix.fromBlocks (fun _ _ => A i j) (fun _ b => C i b) (fun a _ => D a j) K

omit [CommRing R] [Fintype α] [Fintype κ] in
theorem bordered_eq_submatrix (A : Matrix α α R) (C : Matrix α κ R)
    (D : Matrix κ α R) (K : Matrix κ κ R) (i j : α) :
    bordered A C D K i j =
      (Matrix.fromBlocks A C D K).submatrix
        (Sum.elim (fun _ => Sum.inl i) Sum.inr)
        (Sum.elim (fun _ => Sum.inl j) Sum.inr) := by
  ext a b
  cases a <;> cases b <;> rfl

omit [Fintype α] [Fintype κ] in
theorem bordered_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix α α R) (C : Matrix α κ R)
    (D : Matrix κ α R) (K : Matrix κ κ R) (i j : α) :
    (bordered A C D K i j).map φ =
      bordered (A.map φ) (C.map φ) (D.map φ) (K.map φ) i j := by
  ext a b
  cases a <;> cases b <;> rfl

omit [Fintype α] in
theorem det_bordered [DecidableEq κ]
    (A : Matrix α α R) (C : Matrix α κ R)
    (D : Matrix κ α R) (K J : Matrix κ κ R) (hKJ : K * J = 1) (i j : α) :
    (bordered A C D K i j).det = K.det * (A - C * J * D) i j := by
  letI : Invertible K := invertibleOfRightInverse K J hKJ
  have hJ : ⅟K = J := rfl
  rw [bordered, Matrix.det_fromBlocks₂₂, hJ, Matrix.det_unique (n := Fin 1)]
  congr 1

end Bordered

section SchurVanishing
variable {σ α κ : Type*} [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ]
variable {R : Type*} [CommRing R]

/-- Geometric rank bounded by the complementary block size forces every
bordered minor to vanish after mapping into the prime hypersurface. -/
theorem map_det_bordered_eq_zero
    (F : MvPolynomial σ GeometricField) (hF : Irreducible F)
    (A : Matrix α α (MvPolynomial σ GeometricField))
    (C : Matrix α κ (MvPolynomial σ GeometricField))
    (D : Matrix κ α (MvPolynomial σ GeometricField))
    (K : Matrix κ κ (MvPolynomial σ GeometricField))
    (hRank : ∀ x : σ → GeometricField, eval x F = 0 →
      ((Matrix.fromBlocks A C D K).map (eval x)).rank ≤ Fintype.card κ)
    (φ : MvPolynomial σ GeometricField →+* R) (hφ : φ F = 0) (i j : α) :
    φ (bordered A C D K i j).det = 0 := by
  apply map_eq_zero_of_hypersurface_vanishing F _ hF φ hφ
  intro x hx
  rw [RingHom.map_det]
  apply det_eq_zero_of_rank_lt
  rw [bordered_eq_submatrix]
  change (((Matrix.fromBlocks A C D K).map (eval x)).submatrix
    (Sum.elim (fun _ : Fin 1 => Sum.inl i) Sum.inr)
    (Sum.elim (fun _ : Fin 1 => Sum.inl j) Sum.inr)).rank < Fintype.card (Fin 1 ⊕ κ)
  have hr := (rank_submatrix_le ((Matrix.fromBlocks A C D K).map (eval x))
    (Sum.elim (fun _ : Fin 1 => Sum.inl i) Sum.inr)
    (Sum.elim (fun _ : Fin 1 => Sum.inl j) Sum.inr)).trans (hRank x hx)
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_comm] using
    Nat.lt_of_le_of_lt hr (Nat.lt_add_one (Fintype.card κ))

/-- The actual Schur complement vanishes under every ring-valued point of a
prime hypersurface whenever the geometric matrix rank is at most the size of
the invertible complementary block. In particular this applies to formal
power-series curves, and requires no AG input beyond mathlib Nullstellensatz. -/
theorem schur_eq_zero_of_geometric_rank_le
    (F : MvPolynomial σ GeometricField) (hF : Irreducible F)
    (A : Matrix α α (MvPolynomial σ GeometricField))
    (C : Matrix α κ (MvPolynomial σ GeometricField))
    (D : Matrix κ α (MvPolynomial σ GeometricField))
    (K : Matrix κ κ (MvPolynomial σ GeometricField))
    (hRank : ∀ x : σ → GeometricField, eval x F = 0 →
      ((Matrix.fromBlocks A C D K).map (eval x)).rank ≤ Fintype.card κ)
    (φ : MvPolynomial σ GeometricField →+* R) (hφ : φ F = 0)
    (J : Matrix κ κ R) (hKJ : K.map φ * J = 1) :
    A.map φ - C.map φ * J * D.map φ = 0 := by
  ext i j
  have h := map_det_bordered_eq_zero F hF A C D K hRank φ hφ i j
  rw [RingHom.map_det] at h
  change ((bordered A C D K i j).map φ).det = 0 at h
  rw [bordered_map,
    det_bordered (A.map φ) (C.map φ) (D.map φ) (K.map φ) J hKJ i j] at h
  apply (Matrix.isUnit_det_of_right_inverse hKJ).mul_left_cancel
  simpa only [Matrix.zero_apply, mul_zero] using h

end SchurVanishing

end HessianTheorem11.PolynomialSchurVanishing
