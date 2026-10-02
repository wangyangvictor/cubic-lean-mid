import TranslatedDepthSeven.BoundedIntegralDistinguishedNormalizationMenuInternal
import TranslatedDepthSeven.AffineChartProjectionMenu
import TranslatedDepthSeven.AugmentedLinearNormalization

/-!
# Literal bounded projection matrices with first row fixed

Insert the primitive integral row alongside the normalization rows and
interchange the first two rows. Thus the first output coordinate remains
the original homogenizing coordinate, not the primitive coordinate.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Matrix StandardAG
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

def primitiveAffineProjectionMatrix {N r : ℕ}
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℤ)
    (c : Fin (N + 1) → ℕ) : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ :=
  fun i ↦ Fin.cases (fun j ↦ (c j : ℤ)) A
    (Equiv.swap (0 : Fin (r + 2)) 1 i)

def boundedIntegralAffineProjectionMatrices (N r D : ℕ) :
    Finset (Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) :=
  Fintype.piFinset fun _ : Fin (r + 2) ↦
    Fintype.piFinset fun _ : Fin (N + 1) ↦
      Finset.Icc (-(max ((D + 1) ^ N) ((D * D + 1) ^ (N + 1)) : ℕ) : ℤ)
        ((max ((D + 1) ^ N) ((D * D + 1) ^ (N + 1)) : ℕ) : ℤ)

theorem primitiveAffineProjectionMatrix_mem_boundedIntegralAffineProjectionMatrices
    {N r D : ℕ} (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℤ)
    (hA : A ∈ boundedIntegralDistinguishedNormalizationMatrices N r D)
    (c : Fin (N + 1) → ℕ) (hc : ∀ j, c j ≤ (D * D + 1) ^ (N + 1)) :
    primitiveAffineProjectionMatrix A c ∈ boundedIntegralAffineProjectionMatrices N r D := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  have hentry (k : Fin (r + 1)) :
      -(((D + 1) ^ N : ℕ) : ℤ) ≤ A k j ∧
        A k j ≤ (((D + 1) ^ N : ℕ) : ℤ) :=
    Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp hA k) j)
  dsimp only [primitiveAffineProjectionMatrix]
  generalize Equiv.swap (0 : Fin (r + 2)) 1 i = k
  refine Fin.cases ?_ (fun k ↦ ?_) k
  · simp only [Fin.cases_zero]
    have hh : (c j : ℤ) ≤ (((D * D + 1) ^ (N + 1) : ℕ) : ℤ) := by exact_mod_cast hc j
    constructor <;> omega
  · simp only [Fin.cases_succ]
    obtain ⟨hl, hu⟩ := hentry k
    have hmax : (((D + 1) ^ N : ℕ) : ℤ) ≤
        ((max ((D + 1) ^ N) ((D * D + 1) ^ (N + 1)) : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_max_left ((D + 1) ^ N) ((D * D + 1) ^ (N + 1))
    constructor <;> omega

theorem primitiveAffineProjectionMatrix_first_row
    {N r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℤ)
    (c : Fin (N + 1) → ℕ) (hfirst : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    FirstFinProjectionRowIsHomogenizingCoordinate
      ((primitiveAffineProjectionMatrix A c).map (Int.castRingHom ℚ)) := by
  constructor
  · simp only [primitiveAffineProjectionMatrix, Matrix.map_apply, Equiv.swap_apply_left]
    rw [show (1 : Fin (r + 2)) = (0 : Fin (r + 1)).succ by ext; simp]
    rw [Fin.cases_succ]
    simp [hfirst]
  · intro j
    simp only [primitiveAffineProjectionMatrix, Matrix.map_apply, Equiv.swap_apply_left]
    rw [show (1 : Fin (r + 2)) = (0 : Fin (r + 1)).succ by ext; simp]
    rw [Fin.cases_succ]
    simp [hfirst]

theorem primitiveAffineProjectionMatrix_coordinateMap_eq_augmented
    {N r : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (A : Matrix (Fin (r + 1)) (Fin (N + 1)) ℤ)
    (hinjective : Function.Injective ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom ℚ))))))
    (hfinite : ((Ideal.Quotient.mkₐ ℚ I).comp
      (aeval (indexedMatrixRowLinearPolynomial (A.map (Int.castRingHom ℚ))))).Finite)
    (c : Fin (N + 1) → ℕ) :
    let D := homogeneousLinearNormalizationDataOfIntegralMatrix I A hinjective hfinite
    let w := ∑ j, C (c j : ℚ) * X j
    projectiveMatrixCoordinateMap I
      ((primitiveAffineProjectionMatrix A c).map (Int.castRingHom ℚ)) =
      (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).comp
        (renameEquiv ℚ (Equiv.swap (0 : Fin (r + 2)) 1)).toAlgHom := by
  dsimp only
  apply MvPolynomial.algHom_ext
  intro i
  have hrename {s : ℕ} (e : Fin s ≃ Fin s) (j : Fin s) :
      (renameEquiv ℚ e).toAlgHom (X j) = X (e j) := by
    change rename e (X j) = _
    exact rename_X _ _
  rw [AlgHom.comp_apply]
  trans augmentedLinearNormalizationHom
    (homogeneousLinearNormalizationDataOfIntegralMatrix I A hinjective hfinite)
    (Ideal.Quotient.mk I (∑ j, C (c j : ℚ) * X j))
    (X (Equiv.swap (0 : Fin (r + 2)) 1 i))
  · simp only [projectiveMatrixCoordinateMap, AlgHom.comp_apply, aeval_X]
    dsimp only [projectiveMatrixLinearForm, Matrix.map_apply, primitiveAffineProjectionMatrix]
    generalize Equiv.swap (0 : Fin (r + 2)) 1 i = k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · simp [augmentedLinearNormalizationHom_X_zero]
    · simp only [Fin.cases_succ, augmentedLinearNormalizationHom_X_succ]
      simp [HomogeneousLinearNormalizationData.hom,
        homogeneousLinearNormalizationDataOfIntegralMatrix,
        indexedMatrixRowLinearPolynomial]
  · exact congrArg (augmentedLinearNormalizationHom
      (homogeneousLinearNormalizationDataOfIntegralMatrix I A hinjective hfinite)
      (Ideal.Quotient.mk I (∑ j, C (c j : ℚ) * X j)))
      (hrename (Equiv.swap (0 : Fin (r + 2)) 1) i).symm

end
end TranslatedDepthSeven
