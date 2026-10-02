import CubicTenVariables.BinarySliceCounting
import TranslatedDepthSeven.IndependentFamilyComplementDualInternal
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Integral physical coordinates for a rational frequency plane of
codimension two. The transpose sends the given frequency plane to the
literal coordinate plane, as required by Fourier change of variables. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace CubicTenVariables.RationalCodimensionTwoCoordinates

open Module Matrix BinarySliceCounting TranslatedDepthSeven

/-- The frequency plane on which the two selected coordinates vanish. -/
def coordinatePlane {n : ℕ} {K : Type*} [CommRing K] (e : Fin 2 ↪ Fin n) :
    Submodule K (Fin n → K) where
  carrier := {v | ∀ j, v (e j) = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j; simp [hx j, hy j]
  smul_mem' := by intro c x hx j; simp [hx j]

@[simp] theorem mem_coordinatePlane {n : ℕ} {K : Type*} [CommRing K]
    (e : Fin 2 ↪ Fin n) (v : Fin n → K) :
    v ∈ coordinatePlane e ↔ ∀ j, v (e j) = 0 := Iff.rfl

/-- The two coordinate equations are independent over every field. -/
theorem finrank_coordinatePlane {n : ℕ} {K : Type*} [Field K]
    (e : Fin 2 ↪ Fin n) : finrank K (coordinatePlane (K := K) e) = n - 2 := by
  let f : (Fin n → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun v j => v (e j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨combine e z 0, ?_⟩
    ext j
    exact combine_selected e z 0 j
  have hker : LinearMap.ker f = coordinatePlane e := by
    ext v
    simp only [LinearMap.mem_ker, mem_coordinatePlane, funext_iff, Pi.zero_apply]
    rfl
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, hker] at h
  simp only [finrank_top, finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

private theorem exists_rational_coordinate_map {n : ℕ}
    (L : Submodule ℚ (Fin n → ℚ)) (hn : 2 ≤ n) (hL : finrank ℚ L = n - 2) :
    ∃ (e : Fin 2 ↪ Fin n) (T : Matrix (Fin n) (Fin n) ℚ),
      T.det ≠ 0 ∧ L.map T.mulVecLin = coordinatePlane e := by
  classical
  let bL := Module.finBasisOfFinrankEq ℚ L hL
  let u : Fin (n - 2) → (Fin n → ℚ) := fun i => (bL i : Fin n → ℚ)
  have hu : LinearIndependent ℚ u := bL.linearIndependent.map'
    L.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨b₀, hb₀⟩ := exists_basis_finSum_extending_independent_family u hu
  have hdim : finrank ℚ (Fin n → ℚ) = n := by simp
  have htwo : finrank ℚ (Fin n → ℚ) - (n - 2) = 2 := by rw [hdim]; omega
  let I := Fin (n - 2) ⊕ Fin (finrank ℚ (Fin n → ℚ) - (n - 2))
  let E : I ≃ Fin n := finSumFinEquiv.trans (finCongr (by rw [hdim]; omega))
  let j : Fin 2 ≃ Fin (finrank ℚ (Fin n → ℚ) - (n - 2)) := (finCongr htwo).symm
  let e : Fin 2 ↪ Fin n := ⟨fun a => E (Sum.inr (j a)),
    E.injective.comp (Sum.inr_injective.comp j.injective)⟩
  let b := b₀.reindex E
  let T := LinearMap.toMatrix' b.equivFun.toLinearMap
  have hT (x : Fin n → ℚ) : T.mulVec x = b.equivFun x :=
    LinearMap.toMatrix'_mulVec _ x
  have hTdet : T.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det T).mp (Matrix.mulVec_injective_iff_isUnit.mp
      (by intro x y h; apply b.equivFun.injective; simpa only [hT] using h)))
  have hb (i : Fin (n - 2)) : b (E (Sum.inl i)) = u i := by
    simp only [b, Basis.reindex_apply]
    exact (congrArg b₀ (E.symm_apply_apply (Sum.inl i))).trans (hb₀ i)
  have hzero (i : Fin (n - 2)) (a : Fin 2) : b.equivFun (u i) (e a) = 0 := by
    rw [← hb i, Basis.equivFun_self]
    simp [e, E.injective.eq_iff]
  have hle : L.map T.mulVecLin ≤ coordinatePlane e := by
    rintro y ⟨x, hx, rfl⟩ a
    change T.mulVec x (e a) = 0
    rw [hT]
    have hex : (∑ i, bL.repr ⟨x, hx⟩ i • u i) = x := by
      simpa only [u, Submodule.coe_sum, Submodule.coe_smul] using
        congrArg (fun z : L => (z : Fin n → ℚ)) (bL.sum_repr ⟨x, hx⟩)
    rw [← hex, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, hzero, smul_zero,
      Finset.sum_const_zero]
  have hmap : T.mulVecLin = b.equivFun.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact hT x
  refine ⟨e, T, hTdet, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  rw [hmap, b.equivFun.finrank_map_eq, hL, finrank_coordinatePlane]

/-- Every rational codimension-two frequency plane admits integral
physical coordinates with nonzero determinant whose transpose takes that
plane to an actual coordinate plane. -/
theorem exists_integral_coordinates {n : ℕ}
    (L : Submodule ℚ (Fin n → ℚ)) (hn : 2 ≤ n) (hL : finrank ℚ L = n - 2) :
    ∃ (e : Fin 2 ↪ Fin n) (A : Matrix (Fin n) (Fin n) ℤ),
      A.det ≠ 0 ∧
      L.map (A.map (Int.castRingHom ℚ)).transpose.mulVecLin = coordinatePlane e := by
  classical
  obtain ⟨e, T, hT, hmap⟩ := exists_rational_coordinate_map L hn hL
  let B := T.transpose
  have hden : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have hnum : B.num.map (Int.castRingHom ℚ) = (B.den : ℚ) • B := by
    ext i j
    exact (div_eq_iff hden).mp (B.num_div_den i j) |>.trans (mul_comm _ _)
  have hdet : (B.num.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [hnum, Matrix.det_smul, show B.det = T.det from Matrix.det_transpose T]
    exact mul_ne_zero (pow_ne_zero _ hden) hT
  refine ⟨e, B.num, ?_, ?_⟩
  · intro hz
    apply hdet
    have he : (B.num.det : ℚ) = (B.num.map (Int.castRingHom ℚ)).det :=
      Int.cast_det B.num
    rw [← he, hz]
    simp
  · have htranspose : (B.num.map (Int.castRingHom ℚ)).transpose.mulVecLin =
        (B.den : ℚ) • T.mulVecLin := by
      rw [hnum, Matrix.transpose_smul, Matrix.transpose_transpose]
      apply LinearMap.ext
      intro x
      change ((B.den : ℚ) • T).mulVec x = (B.den : ℚ) • T.mulVec x
      exact Matrix.smul_mulVec _ _ _
    rw [htranspose, Submodule.map_smul _ _ _ hden, hmap]

end CubicTenVariables.RationalCodimensionTwoCoordinates
