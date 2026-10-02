import HessianTheorem11.CoisotropicMiddleBasis
import HessianTheorem11.SaturatedCubicResolvent
import HessianTheorem11.CliffordNormalization

/-! Actual beta, e and M in the last saturated incidence configuration.
They are extracted from the original cubic tensor in its constructed basis. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section
namespace HessianTheorem11
open Matrix Module MvPolynomial
namespace CoisotropicBasis.Data
variable {F : GeometricPolynomial 13} {x : GeometricPoint 13}
  {T : Submodule GeometricField (GeometricPoint 13)}
  (D : Data (hessianBilinear F x) T x 5 2 4)

def fourBeta : LinearMap.BilinForm GeometricField (GeometricPoint 4) :=
  Matrix.toBilin' D.middleGram

theorem middleGram_symm : D.middleGram.IsSymm := by
  ext i j
  exact polarization_swap_first F _ _ x

theorem fourBeta_symm : D.fourBeta.IsSymm :=
  CliffordNormalization.toBilin'_isSymm _ D.middleGram_symm

theorem fourBeta_nondegenerate : D.fourBeta.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr D.middleGram_det_ne_zero

theorem middleGramAt_symm (a : GeometricPoint 13) : (D.middleGramAt a).IsSymm := by
  ext i j
  exact polarization_swap_first F _ _ a

theorem middleGramAt_radical_add (hF : F.IsHomogeneous 3) (a b : GeometricPoint 5) :
    D.middleGramAt (D.radicalMatrix.mulVec (a+b)) =
      D.middleGramAt (D.radicalMatrix.mulVec a) + D.middleGramAt (D.radicalMatrix.mulVec b) := by
  ext i j
  simp [middleGramAt,complementGramAt,Matrix.mulVec_add,polarization_add_third hF]

theorem middleGramAt_radical_smul (hF : F.IsHomogeneous 3) (c : GeometricField) (a : GeometricPoint 5) :
    D.middleGramAt (D.radicalMatrix.mulVec (c • a)) = c • D.middleGramAt (D.radicalMatrix.mulVec a) := by
  ext i j
  simp [middleGramAt,complementGramAt,Matrix.mulVec_smul,polarization_smul_third hF]

theorem mixedGramAt_radical_add (hF : F.IsHomogeneous 3) (a b : GeometricPoint 5) :
    D.mixedGramAt (D.radicalMatrix.mulVec (a+b)) =
      D.mixedGramAt (D.radicalMatrix.mulVec a) + D.mixedGramAt (D.radicalMatrix.mulVec b) := by
  ext i j
  simp [mixedGramAt,complementGramAt,Matrix.mulVec_add,polarization_add_third hF]

theorem mixedGramAt_radical_smul (hF : F.IsHomogeneous 3) (c : GeometricField) (a : GeometricPoint 5) :
    D.mixedGramAt (D.radicalMatrix.mulVec (c • a)) = c • D.mixedGramAt (D.radicalMatrix.mulVec a) := by
  ext i j
  simp [mixedGramAt,complementGramAt,Matrix.mulVec_smul,polarization_smul_third hF]

def fourE (hF : F.IsHomogeneous 3) (eta : Fin 2) :
    GeometricPoint 5 →ₗ[GeometricField] GeometricPoint 4 where
  toFun a := D.middleGram⁻¹.mulVec (D.mixedGramAt (D.radicalMatrix.mulVec a) eta)
  map_add' a b := by
    rw [D.mixedGramAt_radical_add hF]
    exact Matrix.mulVec_add _ _ _
  map_smul' c a := by
    rw [D.mixedGramAt_radical_smul hF]
    change D.middleGram⁻¹.mulVec (c • (D.mixedGramAt (D.radicalMatrix.mulVec a) eta)) = _
    exact Matrix.mulVec_smul _ _ _

def fourM (hF : F.IsHomogeneous 3) :
    GeometricPoint 5 →ₗ[GeometricField] Module.End GeometricField (GeometricPoint 4) where
  toFun a := (D.middleGram⁻¹ * D.middleGramAt (D.radicalMatrix.mulVec a)).mulVecLin
  map_add' a b := by
    rw [D.middleGramAt_radical_add hF,Matrix.mul_add,Matrix.mulVecLin_add]
  map_smul' c a := by
    rw [D.middleGramAt_radical_smul hF,Matrix.mul_smul]
    ext u i
    simp [Matrix.mulVec_smul]

theorem fourBeta_inverse_left (u v : GeometricPoint 4) :
    D.fourBeta (D.middleGram⁻¹.mulVec u) v = dotProduct u v := by
  rw [fourBeta,Matrix.toBilin'_apply',Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,
    D.middleGram_symm.eq,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr D.middleGram_det_ne_zero),Matrix.one_mulVec]

theorem middleGramAt_pairing (hF : F.IsHomogeneous 3) (a : GeometricPoint 13)
    (b c : GeometricPoint 4) :
    Matrix.toBilin' (D.middleGramAt a) b c =
      polarization F a (D.middleMatrix.mulVec b) (D.middleMatrix.mulVec c) := by
  rw [polarization_swap_first,polarization_swap_last hF,D.middleMatrix_mulVec_sum,D.middleMatrix_mulVec_sum]
  simp only [polarization_sum_first,polarization_sum_second,polarization_smul_first,
    polarization_smul_second,Matrix.toBilin'_apply',Matrix.mulVec,dotProduct,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [middleGramAt,complementGramAt,complementVector,middleVector]
  ring

theorem fourE_pairing (hF : F.IsHomogeneous 3) (eta : Fin 2)
    (a : GeometricPoint 5) (b : GeometricPoint 4) :
    D.fourBeta (D.fourE hF eta a) b =
      polarization F (D.radicalMatrix.mulVec a) (D.isotropicVector eta) (D.middleMatrix.mulVec b) := by
  change D.fourBeta (D.middleGram⁻¹.mulVec _) _ = _
  rw [D.fourBeta_inverse_left,polarization_swap_first,polarization_swap_last hF,D.middleMatrix_mulVec_sum]
  simp only [polarization_sum_second,polarization_smul_second,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  change _ * _ = _ * _
  dsimp [mixedGramAt,complementGramAt,complementVector,isotropicVector,middleVector]
  ring

theorem fourM_pairing (hF : F.IsHomogeneous 3) (a : GeometricPoint 5)
    (b c : GeometricPoint 4) :
    D.fourBeta ((D.fourM hF a) b) c =
      polarization F (D.radicalMatrix.mulVec a) (D.middleMatrix.mulVec b) (D.middleMatrix.mulVec c) := by
  change D.fourBeta ((D.middleGram⁻¹ * D.middleGramAt (D.radicalMatrix.mulVec a)).mulVec b) c = _
  rw [← Matrix.mulVec_mulVec,D.fourBeta_inverse_left]
  have he : dotProduct ((D.middleGramAt (D.radicalMatrix.mulVec a)).mulVec b) c =
      dotProduct b ((D.middleGramAt (D.radicalMatrix.mulVec a)).mulVec c) := by
    simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(D.middleGramAt_symm _).apply j i]
    ring
  rw [he]
  simpa only [Matrix.toBilin'_apply'] using D.middleGramAt_pairing hF (D.radicalMatrix.mulVec a) b c

theorem fourM_selfAdjoint (hF : F.IsHomogeneous 3) (a : GeometricPoint 5)
    (b c : GeometricPoint 4) :
    D.fourBeta ((D.fourM hF a) b) c = D.fourBeta b ((D.fourM hF a) c) := by
  rw [D.fourBeta_symm.eq b _,D.fourM_pairing hF,D.fourM_pairing hF,polarization_swap_last hF]

theorem fourBeta_pairing (hF : F.IsHomogeneous 3) (b c : GeometricPoint 4) :
    D.fourBeta b c = polarization F (D.middleMatrix.mulVec b) (D.middleMatrix.mulVec c) x := by
  change Matrix.toBilin' (D.middleGramAt x) b c = _
  rw [D.middleGramAt_pairing hF,polarization_swap_first,polarization_swap_last hF]

end CoisotropicBasis.Data
end HessianTheorem11
