import HessianTheorem11.InvariantIsotropicExclusion
import HessianTheorem11.SaturatedFourDimensionalData

/-! The invariant-isotropic exclusion specialized to the operators extracted
from the actual saturated cubic tensor. -/
noncomputable section
namespace HessianTheorem11
open Module Matrix MvPolynomial NonzeroLimitTransport

theorem thirteen_four_invariant_subspace_impossible
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (F : AnisotropicCubic 13) {x : GeometricPoint 13}
    {T : Submodule GeometricField (GeometricPoint 13)}
    (D : CoisotropicBasis.Data (hessianBilinear (geometricPolynomial F.polynomial) x) T x 5 2 4)
    (hker : LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin ≤ T)
    (hann : ∀t∈T,∀u∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀v∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
        polarization (geometricPolynomial F.polynomial) t u v=0)
    (hC : ∀a∈LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,D.isotropicGramAt a=0)
    (η : Fin 2) (hη : η≠D.radial)
    (W : Submodule GeometricField (GeometricPoint 4))
    (hW : ∀u∈W,∀v∈W,D.fourBeta u v=0)
    (heW : LinearMap.range (D.fourE (geometric_homogeneous F.homogeneous) η) ≤ W)
    (hMW : ∀a u,u∈W→D.fourM (geometric_homogeneous F.homogeneous) a u∈W) : False := by
  exact thirteen_invariant_isotropic_subspace_impossible boundary bigCell F D hker hann hC
    D.fourBeta D.fourBeta_symm D.fourBeta_nondegenerate
    (D.fourBeta_pairing (geometric_homogeneous F.homogeneous)) η hη
    (D.fourE (geometric_homogeneous F.homogeneous) η)
    (D.fourM (geometric_homogeneous F.homogeneous))
    (D.fourE_pairing (geometric_homogeneous F.homogeneous) η)
    (D.fourM_pairing (geometric_homogeneous F.homogeneous))
    (D.fourM_selfAdjoint (geometric_homogeneous F.homogeneous)) W hW heW hMW

end HessianTheorem11
