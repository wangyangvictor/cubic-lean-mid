import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Generalized inverses of actual symmetric matrices over a field, and
the induced nondegenerate pairing on their images. No geometric input. -/

noncomputable section
namespace HessianTheorem11
open Matrix Module

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_matrix_generalizedInverse (H : Matrix ι ι K) :
    ∃ N : Matrix ι ι K, H * N * H = H := by
  let A := H.mulVecLin
  obtain ⟨s, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  obtain ⟨p, hp⟩ := (LinearMap.range A).subtype.exists_leftInverse_of_injective
    (LinearMap.range A).ker_subtype
  refine ⟨LinearMap.toMatrix' (s.comp p), ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (H * LinearMap.toMatrix' (s.comp p) * H).mulVec v = H.mulVec v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have hpv := LinearMap.congr_fun hp (A.rangeRestrict v)
  have hsv := congrArg Subtype.val (LinearMap.congr_fun hs (A.rangeRestrict v))
  change p (H.mulVec v) = A.rangeRestrict v at hpv
  change H.mulVec (s (A.rangeRestrict v)) = H.mulVec v at hsv
  change H.mulVec (s (p (H.mulVec v))) = H.mulVec v
  rwa [hpv]

theorem exists_symmetric_generalizedInverse [CharZero K]
    (H : Matrix ι ι K) (hH : H.IsSymm) :
    ∃ N : Matrix ι ι K, N.IsSymm ∧ H * N * H = H := by
  obtain ⟨N, hN⟩ := exists_matrix_generalizedInverse H
  have hNt : H * N.transpose * H = H := by
    have h := congrArg Matrix.transpose hN
    simpa only [Matrix.transpose_mul, hH.eq, Matrix.mul_assoc] using h
  refine ⟨(1 / 2 : K) • (N + N.transpose), ?_, ?_⟩
  · change ((1 / 2 : K) • (N + N.transpose)).transpose = _
    simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hN, hNt]
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
    ring

/-- The pairing defined by a symmetric generalized inverse is
nondegenerate on the image of the original symmetric matrix. -/
theorem generalizedInverse_pairing_nondegenerate_on_range
    (H N : Matrix ι ι K) (hH : H.IsSymm) (hN : H * N * H = H)
    (g : ι → K) (hg : g ∈ LinearMap.range H.mulVecLin) (hg0 : g ≠ 0) :
    ∃ z ∈ LinearMap.range H.mulVecLin, dotProduct (N.mulVec g) z ≠ 0 := by
  by_contra he
  push_neg at he
  have heq : H.mulVec (N.mulVec g) = 0 := by
    ext i
    have hz := he (H.mulVec (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hH.eq] at hz
    simpa using hz
  obtain ⟨v, hv⟩ := hg
  change H.mulVec v = g at hv
  apply hg0
  calc
    g = (H * N * H).mulVec v := by rw [hN]; exact hv.symm
    _ = H.mulVec (N.mulVec g) := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv]
    _ = 0 := heq

/-- An actual Jacobian image lies in a proper hyperplane of `range H`
when it annihilates the generalized-inverse pairing with a nonzero
vector of that range. -/
theorem rank_lt_of_generalizedInverse_annihilator
    {σ : Type*} [Fintype σ] (H N : Matrix ι ι K) (hH : H.IsSymm)
    (hN : H * N * H = H) (J : Matrix ι σ K)
    (hJrange : LinearMap.range J.mulVecLin ≤ LinearMap.range H.mulVecLin)
    (g : ι → K) (hg : g ∈ LinearMap.range H.mulVecLin) (hg0 : g ≠ 0)
    (hJ : J.transpose.mulVec (N.mulVec g) = 0) : J.rank < H.rank := by
  let S := LinearMap.range H.mulVecLin
  let f : (ι → K) →ₗ[K] K := {
    toFun := fun z => dotProduct (N.mulVec g) z
    map_add' := fun u v => dotProduct_add _ u v
    map_smul' := fun c z => by simp [dotProduct_smul]
  }
  have hle : LinearMap.range J.mulVecLin ≤ S ⊓ LinearMap.ker f := by
    rintro z ⟨v, rfl⟩
    refine ⟨hJrange ⟨v, rfl⟩, ?_⟩
    change dotProduct (N.mulVec g) (J.mulVec v) = 0
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hJ]
    simp
  obtain ⟨z, hz, hz0⟩ := generalizedInverse_pairing_nondegenerate_on_range H N hH hN g hg hg0
  have hlt : S ⊓ LinearMap.ker f < S := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hm : z ∈ S ⊓ LinearMap.ker f := by rw [he]; exact hz
    exact hz0 hm.2
  exact (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)

end HessianTheorem11
