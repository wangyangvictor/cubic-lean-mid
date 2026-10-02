import HessianTheorem11.NormalQuadrics

/-! The strengthened radial weight obstruction for a square-zero tensor
subspace in the Hessian kernel at a smooth cubic point. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem radial_square_zero_subspace_dimension_bound
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : Fin n → K) (hx : eval x F = 0)
    (L : Submodule K (Fin n → K)) (hxL : x ∉ L)
    (hkernel : L ≤ LinearMap.ker (hessian F x).mulVecLin)
    (hzero : ∀ v : Fin n → K, ∀ u ∈ L, ∀ w ∈ L, polarization F v u w = 0) :
    6 * (finrank K L : ℤ) + 3 ≤ 2 * (n : ℤ) := by
  let A := simultaneousSubspaceBasis (⊤ : Submodule K (Fin n → K)) L x
    (Submodule.mem_top) hxL
  have hk (i : Fin n) (hi : i ∈ A.kernelIndices) :
      (hessian F (A.basis A.radial)).mulVec (A.basis i) = 0 := by
    rw [A.radial_eq]
    exact hkernel ((A.mem_kernel_iff i).mpr hi)
  have ht (i : Fin n) (_ : i ∈ A.tangentIndices)
      (j : Fin n) (hj : j ∈ A.kernelIndices) (k : Fin n) (hk : k ∈ A.kernelIndices) :
      polarization F (A.basis i) (A.basis j) (A.basis k) = 0 :=
    hzero _ _ ((A.mem_kernel_iff j).mpr hj) _ ((A.mem_kernel_iff k).mpr hk)
  have hz : polarization F (A.basis A.radial) (A.basis A.radial) (A.basis A.radial) = 0 := by
    rw [A.radial_eq]
    change dotProduct x ((hessian F x).mulVec x) = 0
    rw [hessian_cubic_identity hF, hx, mul_zero]
  have hnonneg : 0 ≤ ∑ i, liftedRadialWeight A.radial A.tangentIndices A.kernelIndices i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF (basisMatrix A.basis)
      (basisMatrix_injective A.basis)
    intro i j k hne
    change coeff 0 (pderiv k (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    exact liftedRadialWeight_nonnegative_tensor F hF A.basis A.radial
      A.tangentIndices A.kernelIndices A.radial_mem_tangent A.radial_notMem_kernel
      hk ht hz i j k hne
  rw [sum_liftedRadialWeight, A.tangent_card, A.kernel_card] at hnonneg
  have htop : finrank K (⊤ : Submodule K (Fin n → K)) = n := by simp
  rw [htop] at hnonneg
  omega

theorem thirteen_radial_square_zero_finrank_le_three
    (F : MvPolynomial (Fin 13) K) (hF : F.IsHomogeneous 3) (hsemi : WeightSemistable F)
    (x : Fin 13 → K) (hx : eval x F = 0)
    (L : Submodule K (Fin 13 → K)) (hxL : x ∉ L)
    (hkernel : L ≤ LinearMap.ker (hessian F x).mulVecLin)
    (hzero : ∀ v : Fin 13 → K, ∀ u ∈ L, ∀ w ∈ L, polarization F v u w = 0) :
    finrank K L ≤ 3 := by
  have h := radial_square_zero_subspace_dimension_bound F hF hsemi x hx L hxL hkernel hzero
  omega

end HessianTheorem11
