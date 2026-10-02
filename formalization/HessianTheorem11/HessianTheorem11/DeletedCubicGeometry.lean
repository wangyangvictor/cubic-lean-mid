import HessianTheorem11.CoordinateDeletion
import HessianTheorem11.PureCubeRank
import HessianTheorem11.LinearEmbeddingGeometry
import HessianTheorem11.HessianDeterminant
import HessianTheorem11.Restriction

/-! Actual coordinate deletion: projection of the base, preservation of
dimension, and the Hessian ranks of the complementary cubic. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module Restriction

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

@[simp] theorem coordinateProjectionMatrix_mulVec (c : Fin (n+1)) (x : Fin (n+1) → K) :
    (coordinateDeletionMatrix c).transpose.mulVec x = c.removeNth x := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, coordinateDeletionMatrix, Fin.removeNth]

theorem coordinateProjectionMatrix_linearForms (c : Fin (n+1)) (i : Fin n) :
    PolynomialRestriction.linearForms (coordinateDeletionMatrix c : Matrix _ _ K).transpose i =
      X (c.succAbove i) := by
  classical
  simp [PolynomialRestriction.linearForms, coordinateDeletionMatrix, eq_comm]

theorem restrict_projection_eq_rename (c : Fin (n+1)) (G : MvPolynomial (Fin n) K) :
    PolynomialRestriction.restrict (coordinateDeletionMatrix c).transpose G =
      rename c.succAbove G := by
  have hh : (aeval (PolynomialRestriction.linearForms
      (coordinateDeletionMatrix c : Matrix _ _ K).transpose) :
        MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K) = rename c.succAbove := by
    ext i
    simp [coordinateProjectionMatrix_linearForms]
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K => f G) hh

theorem eraseCoordinate_eq_restrict_delete (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) :
    eraseCoordinate c G = PolynomialRestriction.restrict
      (coordinateDeletionMatrix c).transpose (deleteCoordinate c G) := by
  rw [restrict_projection_eq_rename, rename_deleteCoordinate]

theorem hessian_erase_rank_le_deleted (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) (x : Fin (n+1) → K) :
    (hessian (eraseCoordinate c G) x).rank ≤
      (hessian (deleteCoordinate c G) (c.removeNth x)).rank := by
  rw [eraseCoordinate_eq_restrict_delete, PolynomialRestriction.hessian_restrict,
    coordinateProjectionMatrix_mulVec]
  exact rank_congruence_le _ _

theorem hessian_deleted_rank_eq_of_coordinate_zero (c : Fin (n+1))
    (G : MvPolynomial (Fin (n+1)) K) (κ : K)
    (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (x : Fin (n+1) → K) (hxc : x c = 0) :
    (hessian (deleteCoordinate c G) (c.removeNth x)).rank = (hessian G x).rank := by
  have hx : (coordinateDeletionMatrix c).mulVec (c.removeNth x) = x := by
    rw [coordinateDeletionMatrix_mulVec, ← hxc, Fin.insertNth_self_removeNth]
  apply le_antisymm
  · rw [deleteCoordinate_eq_restrict, PolynomialRestriction.hessian_restrict, hx]
    exact rank_congruence_le _ _
  · have hh : hessian G x = hessian (eraseCoordinate c G) x := by
      conv_lhs => rw [hsplit]
      rw [hessian_add_pure_cube, hxc]
      simp
    rw [hh]
    exact hessian_erase_rank_le_deleted c G x

theorem rank_matrix_single_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι) (a : K) : (Matrix.single c c a : Matrix ι ι K).rank ≤ 1 := by
  have hh : (Matrix.single c c a : Matrix ι ι K) =
      Matrix.vecMulVec (Pi.single c a) (Pi.single c 1) := by
    ext i j
    by_cases hi : i = c <;> by_cases hj : j = c <;>
      simp_all [Matrix.single, Matrix.vecMulVec_apply, Pi.single_apply] <;> aesop
  rw [hh]
  exact Matrix.rank_vecMulVec_le _ _

theorem deleted_hessianDeterminant_ne_zero [Infinite K]
    (c : Fin (n+1)) (G : MvPolynomial (Fin (n+1)) K) (κ : K)
    (hsplit : G = eraseCoordinate c G + C κ * X c ^ 3)
    (hdet : hessianDeterminantPolynomial G ≠ 0) :
    hessianDeterminantPolynomial (deleteCoordinate c G) ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, eval x (hessianDeterminantPolynomial G) ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hdet (MvPolynomial.funext (fun x => by simpa using hh x))
  rw [eval_hessianDeterminantPolynomial] at hx
  have hr : (hessian G x).rank = n+1 := by
    simpa using Matrix.rank_of_isUnit (hessian G x)
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
  have hH : hessian G x = hessian (eraseCoordinate c G) x +
      Matrix.single c c (6 * κ * x c) := by
    conv_lhs => rw [hsplit]
    exact hessian_add_pure_cube _ c κ x
  have hb := MatrixRankBounds.rank_add_le (hessian (eraseCoordinate c G) x)
    (Matrix.single c c (6 * κ * x c))
  rw [← hH, hr] at hb
  have hs := rank_matrix_single_le_one c (6 * κ * x c)
  have he := hessian_erase_rank_le_deleted c G x
  let M := hessian (deleteCoordinate c G) (c.removeNth x)
  have hrM : M.rank = n := by
    have hh : M.rank ≤ n := Matrix.rank_le_width M
    change (hessian (eraseCoordinate c G) x).rank ≤ M.rank at he
    omega
  have hker : LinearMap.ker M.mulVecLin = ⊥ := by
    have hd := M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank + _ = _ at hd
    rw [hrM] at hd
    simp only [Module.finrank_pi, Fintype.card_fin] at hd
    apply Submodule.finrank_eq_zero.mp
    omega
  have hm : M.det ≠ 0 := by
    intro hz
    obtain ⟨u, hu, huk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
    have hmem : u ∈ LinearMap.ker M.mulVecLin := huk
    rw [hker] at hmem
    exact hu (by simpa using hmem)
  intro hz
  apply hm
  change (hessian (deleteCoordinate c G) (c.removeNth x)).det = 0
  rw [← eval_hessianDeterminantPolynomial, hz, map_zero]

theorem algebraicallyClosedSet_polynomialMap_preimage
    {σ τ : Type*} (P : τ → MvPolynomial σ GeometricField)
    {Z : Set (τ → GeometricField)} (hZ : AlgebraicallyClosedSet Z) :
    AlgebraicallyClosedSet (polynomialMap P ⁻¹' Z) := by
  apply le_antisymm
  · intro x hx
    have h := polynomialMap_image_closure_subset P (polynomialMap P ⁻¹' Z)
      (Set.mem_image_of_mem (polynomialMap P) hx)
    exact geometricClosure_subset_closed (Set.image_preimage_subset (polynomialMap P) Z) hZ h
  · exact subset_geometricClosure _

def deletedBase (c : Fin (n+1)) (Z : Set (GeometricPoint (n+1))) :
    Set (GeometricPoint n) := {v | c.insertNth 0 v ∈ Z}

theorem deletedBase_embedding_image (c : Fin (n+1)) (Z : Set (GeometricPoint (n+1)))
    (hZ : ∀ x ∈ Z, x c = 0) :
    (coordinateDeletionMatrix c).mulVec '' deletedBase c Z = Z := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [coordinateDeletionMatrix_mulVec] using hv
  · intro hx
    refine ⟨c.removeNth x, ?_, ?_⟩
    · change c.insertNth 0 (c.removeNth x) ∈ Z
      rw [← hZ x hx, Fin.insertNth_self_removeNth]
      exact hx
    · rw [coordinateDeletionMatrix_mulVec, ← hZ x hx, Fin.insertNth_self_removeNth]

theorem deletedBase_dimension (c : Fin (n+1)) (Z : Set (GeometricPoint (n+1)))
    (hZ : ∀ x ∈ Z, x c = 0) : affineDimension (deletedBase c Z) = affineDimension Z := by
  calc
    _ = affineDimension ((coordinateDeletionMatrix c).mulVec '' deletedBase c Z) :=
      (affineDimension_linearMap_image (coordinateDeletionMatrix c).mulVecLin
        (coordinateDeletionMatrix_injective c) (deletedBase c Z)).symm
    _ = affineDimension Z := congrArg affineDimension (deletedBase_embedding_image c Z hZ)

theorem deletedBase_closed (c : Fin (n+1)) (Z : Set (GeometricPoint (n+1)))
    (hZ : AlgebraicallyClosedSet Z) : AlgebraicallyClosedSet (deletedBase c Z) := by
  have hh := algebraicallyClosedSet_polynomialMap_preimage
    (linearCoordinatePolynomials (coordinateDeletionMatrix c).mulVecLin) hZ
  have hm : polynomialMap (linearCoordinatePolynomials
      (coordinateDeletionMatrix c : Matrix _ _ GeometricField).mulVecLin) =
      (fun x : Fin n → GeometricField => c.insertNth 0 x) := by
    funext x
    simp only [polynomialMap_linearCoordinatePolynomials, Matrix.mulVecLin_apply,
      coordinateDeletionMatrix_mulVec]
  rw [hm] at hh
  exact hh

end HessianTheorem11
