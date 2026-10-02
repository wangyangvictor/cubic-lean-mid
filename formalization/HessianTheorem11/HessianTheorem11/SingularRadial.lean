import HessianTheorem11.RadialWeights
import HessianTheorem11.Semistability
import HessianTheorem11.SingularLinearAlgebra

/-! The singular radial inequality, proved from actual tensor vanishing and
weight semistability. The determinantal tangent formula supplies the tensor
vanishing in geometric applications; no dimension bound is an input here. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem singular_radial_of_tensor_vanishing
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin n → K) (hx : x ≠ 0)
    (T : Submodule K (Fin n → K)) (hxT : x ∈ T)
    (hTL : T ≤ LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
      polarization F t u v = 0) :
    finrank K T + 3 ≤ 2 * (hessian F x).rank := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let A := adaptedFlagBasis T L hTL x hx hxT
  let w := singularRadialWeight A.radial A.tangentIndices A.kernelIndices
  have hkernel (i : Fin n) (hi : i ∈ A.kernelIndices) :
      (hessian F (A.basis A.radial)).mulVec (A.basis i) = 0 := by
    rw [A.radial_eq]
    exact (A.mem_kernel_iff i).mpr hi
  have htangent (i : Fin n) (hi : i ∈ A.tangentIndices)
      (j : Fin n) (hj : j ∈ A.kernelIndices)
      (l : Fin n) (hl : l ∈ A.kernelIndices) :
      polarization F (A.basis i) (A.basis j) (A.basis l) = 0 :=
    htensor _ ((A.mem_tangent_iff i).mpr hi)
      _ ((A.mem_kernel_iff j).mpr hj) _ ((A.mem_kernel_iff l).mpr hl)
  have hsum : 0 ≤ ∑ i, w i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF
      (basisMatrix A.basis) (basisMatrix_injective A.basis) w
    intro i j l hne
    change coeff 0 (pderiv l (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    exact singularRadialWeight_nonnegative_tensor F hF A.basis
      A.radial A.tangentIndices A.kernelIndices A.radial_mem A.indices_nested
      hkernel htangent i j l hne
  change 0 ≤ ∑ i, singularRadialWeight A.radial A.tangentIndices A.kernelIndices i at hsum
  rw [sum_singularRadialWeight, A.tangent_card, A.kernel_card] at hsum
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change (hessian F x).rank + finrank K L = n at hr
  omega

end HessianTheorem11
