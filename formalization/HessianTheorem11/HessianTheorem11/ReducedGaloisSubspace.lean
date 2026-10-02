import HessianTheorem11.RationalDescent
import HessianTheorem11.MatrixRankMinors
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Galois-invariant coordinate subspaces have rational coordinate bases.
The proof normalizes a basis by an invertible coordinate minor; uniqueness
of that normalization forces each coordinate into the Galois fixed field. -/
noncomputable section
namespace HessianTheorem11.ReducedRationalDescent
open Matrix Module

theorem coordinate_projection_equiv {K : Type*} [Field K] {n : ℕ}
    (T : Submodule K (Fin n → K)) :
    ∃ (rows : Fin (finrank K T) → Fin n)
      (e : T ≃ₗ[K] (Fin (finrank K T) → K)),
      ∀ x i, e x i = (x : Fin n → K) (rows i) := by
  classical
  let b := Module.finBasis K T
  let A : Matrix (Fin n) (Fin (finrank K T)) K := fun j i => (b i).val j
  have hli : LinearIndependent K A.transpose.row :=
    b.linearIndependent.map' T.subtype (by simp)
  have hr : A.rank = finrank K T := by
    rw [← rank_transpose]
    simpa using hli.rank_matrix
  obtain ⟨rows, cols, hd⟩ :
      ∃ (rows : Fin (finrank K T) → Fin n)
        (cols : Fin (finrank K T) → Fin (finrank K T)),
        (A.submatrix rows cols).det ≠ 0 := by
    obtain ⟨rows,cols,hd⟩ := MatrixRankMinors.exists_rank_minor A
    let e : Fin (finrank K T) ≃ Fin A.rank := finCongr hr.symm
    refine ⟨rows ∘ e, cols ∘ e, ?_⟩
    change ((A.submatrix rows cols).submatrix e e).det ≠ 0
    rwa [Matrix.det_submatrix_equiv_self]
  let L : T →ₗ[K] (Fin (finrank K T) → K) := {
    toFun := fun x i => (x : Fin n → K) (rows i)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hs : Function.Surjective L := by
    intro y
    let e := Matrix.toLinearEquiv (Pi.basisFun K _) (A.submatrix rows cols)
      (isUnit_iff_ne_zero.mpr hd)
    obtain ⟨c, hc⟩ := e.surjective y
    refine ⟨∑ j, c j • b (cols j), ?_⟩
    ext i
    have hi := congrFun hc i
    simpa [e, L, Matrix.toLinearEquiv, Matrix.toLin_apply, Matrix.mulVec,
      dotProduct, A, Matrix.submatrix_apply, mul_comm, Pi.single_apply] using hi
  have hi : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr hs
  exact ⟨rows, LinearEquiv.ofBijective L ⟨hi, hs⟩, fun _ _ => rfl⟩

/-- A coordinate subspace stable under every rational Galois automorphism
has a basis whose actual ambient coordinates are rational. -/
theorem invariant_subspace_rational_basis {n : ℕ}
    (T : Submodule GeometricField (GeometricPoint n))
    (hT : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField),
      ∀ x ∈ T, (fun i => σ (x i)) ∈ T) :
    ∃ b : Basis (Fin (finrank GeometricField T)) GeometricField T,
      ∀ i j, ∃ q : ℚ, algebraMap ℚ GeometricField q = (b i).val j := by
  classical
  obtain ⟨rows,e,he⟩ := coordinate_projection_equiv T
  let b := (Pi.basisFun GeometricField (Fin (finrank GeometricField T))).map e.symm
  have hn (i j) : (b i).val (rows j) =
      (Pi.basisFun GeometricField (Fin (finrank GeometricField T)) i) j := by
    rw [← he]
    simp [b]
  refine ⟨b, ?_⟩
  intro i j
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed ((b i).val j)).mpr
  intro σ
  let y : T := ⟨fun k => σ ((b i).val k), hT σ _ (b i).property⟩
  have hy : y = b i := by
    apply e.injective
    ext k
    rw [he, he]
    change σ ((b i).val (rows k)) = (b i).val (rows k)
    rw [hn]
    simp [Pi.basisFun_apply, Pi.single_apply]
  exact congrArg (fun z : T => z.val j) hy

end HessianTheorem11.ReducedRationalDescent
