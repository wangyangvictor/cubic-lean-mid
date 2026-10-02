import HessianTheorem11.GeometricRadial

/-! Equality in the actual smooth radial estimate. The adapted basis and
nonnegative monomial support are constructed, and the extra kernel block is
proved empty. No equality-case rigidity statement is an input. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The data forced by equality in the smooth radial inequality. -/
structure SmoothRadialEqualityData (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) (T : Submodule K (Fin n → K)) where
  adapted : SimultaneousSubspaceBasis T (LinearMap.ker (hessian F x).mulVecLin) x
  kernel_subset_tangent : adapted.kernelIndices ⊆ adapted.tangentIndices
  total_weight_zero : ∑ i, smoothRadialWeight adapted.radial
    adapted.tangentIndices adapted.kernelIndices i = 0
  support_nonnegative : HasNonnegativeWeights
    (PolynomialRestriction.restrict (basisMatrix adapted.basis) F)
    (smoothRadialWeight adapted.radial adapted.tangentIndices adapted.kernelIndices)

/-- The explicit smooth radial calculation retains its equality information:
the Hessian kernel lies inside the tangent space, and the displayed radial
weights already sum to zero. -/
theorem smooth_radial_equality_data
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin n → K)
    (T : Submodule K (Fin n → K)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
        polarization F t u v = 0)
    (hradial : ∀ t ∈ T, polarization F x x t = 0)
    (heq : 3 * ((finrank K T : ℤ) - ((hessian F x).rank : ℤ)) + 3 = (n : ℤ)) :
    Nonempty (SmoothRadialEqualityData F x T) := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  let A := simultaneousSubspaceBasis T L x hxT hxL
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
  have hrad (i : Fin n) (hi : i ∈ A.tangentIndices) :
      polarization F (A.basis A.radial) (A.basis A.radial) (A.basis i) = 0 := by
    rw [A.radial_eq]
    exact hradial _ ((A.mem_tangent_iff i).mpr hi)
  have hnonnegative : HasNonnegativeWeights
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)
      (smoothRadialWeight A.radial A.tangentIndices A.kernelIndices) := by
    apply nonnegativeWeights_of_thirdPartials _ (PolynomialRestriction.homogeneous_restrict _ F hF)
    intro i j l hne
    change coeff 0 (pderiv l (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix A.basis) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    exact smoothRadialWeight_nonnegative_tensor F hF A.basis A.radial
      A.tangentIndices A.kernelIndices A.radial_mem_tangent A.radial_notMem_kernel
      hkernel htangent hrad i j l hne
  have hsum := hsemi.nonnegative_weight_sum hF (basisMatrix A.basis)
    (basisMatrix_injective A.basis)
    (smoothRadialWeight A.radial A.tangentIndices A.kernelIndices) hnonnegative
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change (hessian F x).rank + finrank K L = n at hr
  have hs := sum_smoothRadialWeight_difference A.radial A.tangentIndices A.kernelIndices
  rw [A.tangent_card, A.kernel_card] at hs
  have hc : (A.kernelIndices \ A.tangentIndices).card = 0 := by omega
  have hsub : A.kernelIndices ⊆ A.tangentIndices :=
    Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hc)
  refine ⟨⟨A, hsub, ?_, hnonnegative⟩⟩
  omega

theorem SmoothRadialEqualityData.kernel_le_tangent
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialEqualityData F x T) :
    LinearMap.ker (hessian F x).mulVecLin ≤ T := by
  calc
    LinearMap.ker (hessian F x).mulVecLin =
        Submodule.span K (E.adapted.basis '' (E.adapted.kernelIndices : Set (Fin n))) :=
      E.adapted.kernel_span.symm
    _ ≤ Submodule.span K (E.adapted.basis '' (E.adapted.tangentIndices : Set (Fin n))) :=
      Submodule.span_mono (Set.image_mono E.kernel_subset_tangent)
    _ = T := E.adapted.tangent_span

/-- At equality the only variable weights are `−2, 1, 4`. The minimum-weight
space consists precisely of the Hessian kernel and the radial coordinate. -/
theorem SmoothRadialEqualityData.weight_values
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialEqualityData F x T) (i : Fin n) :
    smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i =
      if i ∈ E.adapted.kernelIndices ∨ i = E.adapted.radial then -2
      else if i ∈ E.adapted.tangentIndices then 1 else 4 := by
  have hrT := E.adapted.radial_mem_tangent
  have hrL := E.adapted.radial_notMem_kernel
  by_cases hiL : i ∈ E.adapted.kernelIndices
  · have hiT := E.kernel_subset_tangent hiL
    have hne : i ≠ E.adapted.radial := by rintro rfl; exact hrL hiL
    simp [smoothRadialWeight, hiL, hiT, hne]
  · by_cases hir : i = E.adapted.radial
    · subst i
      simp [smoothRadialWeight, hrT, hrL]
    · by_cases hiT : i ∈ E.adapted.tangentIndices <;>
        simp [smoothRadialWeight, hiL, hir, hiT]

end HessianTheorem11
