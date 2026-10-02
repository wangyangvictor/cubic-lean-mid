import HessianTheorem11.MatrixRankMinors
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators

/-! Literal column augmentation, image membership, and maximal minors.
These finite linear algebra statements are used to encode the existence of
a linear factor of a cubic by homogeneous polynomial equations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace CubicTenVariables.MatrixAugmentedColumn
open Matrix Module

/-- Adjoin the displayed vector as the `none` column. -/
def augment {R α β : Type*} [CommRing R]
    (A : Matrix α β R) (b : α → R) : Matrix α (Option β) R :=
  fun i j => match j with
    | none => b i
    | some j => A i j

@[simp] theorem augment_none {R α β : Type*} [CommRing R]
    (A : Matrix α β R) (b : α → R) (i : α) : augment A b i none = b i := rfl

@[simp] theorem augment_some {R α β : Type*} [CommRing R]
    (A : Matrix α β R) (b : α → R) (i : α) (j : β) : augment A b i (some j) = A i j := rfl

theorem mulVec_augment {R α β : Type*} [CommRing R] [Fintype β]
    (A : Matrix α β R) (b : α → R) (v : Option β → R) :
    (augment A b).mulVec v = v none • b + A.mulVec (fun j => v (some j)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option,
    augment_none, augment_some, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm (b i)]

variable {K α β : Type*} [Field K] [Fintype α] [Fintype β]

/-- The original matrix image lies inside the augmented matrix image. -/
theorem range_le (A : Matrix α β K) (b : α → K) :
    LinearMap.range A.mulVecLin ≤ LinearMap.range (augment A b).mulVecLin := by
  rintro _ ⟨v, rfl⟩
  refine ⟨Option.elim' 0 v, ?_⟩
  change (augment A b).mulVec (Option.elim' 0 v) = A.mulVec v
  rw [mulVec_augment]
  change 0 • b + A.mulVec v = A.mulVec v
  simp only [zero_smul, zero_add]

/-- The adjoined column itself belongs to the augmented image. -/
theorem column_mem_range (A : Matrix α β K) (b : α → K) :
    b ∈ LinearMap.range (augment A b).mulVecLin := by
  refine ⟨Option.elim' 1 (fun _ => 0), ?_⟩
  change (augment A b).mulVec (Option.elim' 1 (fun _ => 0)) = b
  rw [mulVec_augment]
  change (1 : K) • b + A.mulVec 0 = b
  simp only [one_smul, Matrix.mulVec_zero, add_zero]

/-- For a full-column-rank matrix, the literal linear equation is solvable
exactly when adjoining its right-hand side does not increase the rank. -/
theorem exists_mulVec_eq_iff_rank_le (A : Matrix α β K) (b : α → K)
    (hA : A.rank = Fintype.card β) :
    (∃ c : β → K, A.mulVec c = b) ↔ (augment A b).rank ≤ Fintype.card β := by
  constructor
  · rintro ⟨c, hc⟩
    have hb : b ∈ LinearMap.range A.mulVecLin := ⟨c, hc⟩
    have hle : LinearMap.range (augment A b).mulVecLin ≤ LinearMap.range A.mulVecLin := by
      rintro _ ⟨v, rfl⟩
      change (augment A b).mulVec v ∈ LinearMap.range A.mulVecLin
      rw [mulVec_augment]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) ⟨_, rfl⟩
    have h := Submodule.finrank_mono hle
    change (augment A b).rank ≤ A.rank at h
    exact h.trans_eq hA
  · intro h
    have he : LinearMap.range A.mulVecLin = LinearMap.range (augment A b).mulVecLin :=
      Submodule.eq_of_le_of_finrank_le (range_le A b) (by
        change (augment A b).rank ≤ A.rank
        rwa [hA])
    have hb := column_mem_range A b
    rw [← he] at hb
    exact hb

/-- The augmented matrix has just `card β + 1` columns. Its rank is at
most `card β` exactly when every maximal square minor vanishes. No rank
hypothesis on the original matrix is needed for this equivalence. -/
theorem rank_le_iff_maximal_minors_zero (A : Matrix α β K) (b : α → K) :
    (augment A b).rank ≤ Fintype.card β ↔
      ∀ (rows : Fin (Fintype.card β + 1) → α)
        (cols : Fin (Fintype.card β + 1) → Option β),
        ((augment A b).submatrix rows cols).det = 0 := by
  constructor
  · intro h rows cols
    by_contra hne
    have hm := HessianTheorem11.MatrixRankMinors.minor_size_le_rank
      (augment A b) rows cols hne
    omega
  · intro h
    by_contra hlarge
    have hup := (augment A b).rank_le_card_width
    simp only [Fintype.card_option] at hup
    have hrank : (augment A b).rank = Fintype.card β + 1 := by omega
    have hex : ∃ (rows : Fin (Fintype.card β + 1) → α)
        (cols : Fin (Fintype.card β + 1) → Option β),
        ((augment A b).submatrix rows cols).det ≠ 0 := by
      exact hrank ▸ HessianTheorem11.MatrixRankMinors.exists_rank_minor (augment A b)
    obtain ⟨rows, cols, hne⟩ := hex
    exact hne (h rows cols)

end CubicTenVariables.MatrixAugmentedColumn
