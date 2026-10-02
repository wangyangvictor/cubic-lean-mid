import HessianTheorem11.ReducedGaloisSubspace

/-! Descent of actual coordinate subspaces over an arbitrary Galois extension.
An invertible coordinate minor normalizes the basis uniquely, so every
coordinate of that basis lies in the fixed field. No finite extension or
previously supplied rational point is needed. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.GaloisStableSubspacePoint
open Module

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable {n : ℕ}

/-- A stable coordinate subspace has a basis with actual base-field coordinates. -/
theorem invariant_subspace_basis
    (T : Submodule L (Fin n → L))
    (hT : ∀ (σ : L ≃ₐ[K] L), ∀ x ∈ T, (fun i => σ (x i)) ∈ T) :
    ∃ b : Basis (Fin (finrank L T)) L T,
      ∀ i j, ∃ q : K, algebraMap K L q = (b i).val j := by
  classical
  obtain ⟨rows,e,he⟩ := HessianTheorem11.ReducedRationalDescent.coordinate_projection_equiv T
  let b := (Pi.basisFun L (Fin (finrank L T))).map e.symm
  have hn (i j) : (b i).val (rows j) =
      (Pi.basisFun L (Fin (finrank L T)) i) j := by
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

/-- Every positive-dimensional Galois-stable subspace contains a nonzero
vector whose coordinates are in the base field. -/
theorem exists_nonzero_base_point
    (T : Submodule L (Fin n → L)) (hdim : 0 < finrank L T)
    (hT : ∀ (σ : L ≃ₐ[K] L), ∀ x ∈ T, (fun i => σ (x i)) ∈ T) :
    ∃ z : Fin n → K, z ≠ 0 ∧ (fun i => algebraMap K L (z i)) ∈ T := by
  classical
  obtain ⟨b,hb⟩ := invariant_subspace_basis T hT
  let i : Fin (finrank L T) := ⟨0, hdim⟩
  choose z hz using hb i
  have he : (fun j => algebraMap K L (z j)) = (b i).val := funext hz
  refine ⟨z, ?_, he ▸ (b i).property⟩
  intro hzero
  have hbzero : b i = 0 := by
    apply Subtype.ext
    rw [← he, hzero]
    ext j
    exact map_zero (algebraMap K L)
  exact b.ne_zero i hbzero

end CubicTenVariables.GaloisStableSubspacePoint
