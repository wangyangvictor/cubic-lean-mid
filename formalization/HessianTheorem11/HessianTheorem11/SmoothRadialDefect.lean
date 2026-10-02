import HessianTheorem11.SmoothRadialEquality
import HessianTheorem11.IncidenceRadial
import HessianTheorem11.Concentration

/-! The full smooth radial support data, retaining the possible transverse
kernel block. In the thirteen-variable dimension-sixteen case its dimension
is proved to be at most one. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

structure SmoothRadialSupportData (F : MvPolynomial (Fin n) K)
    (x : Fin n → K) (T : Submodule K (Fin n → K)) where
  adapted : SimultaneousSubspaceBasis T (LinearMap.ker (hessian F x).mulVecLin) x
  support_nonnegative : HasNonnegativeWeights
    (PolynomialRestriction.restrict (basisMatrix adapted.basis) F)
    (smoothRadialWeight adapted.radial adapted.tangentIndices adapted.kernelIndices)
  total_weight_nonnegative : 0 ≤ ∑ i, smoothRadialWeight adapted.radial
    adapted.tangentIndices adapted.kernelIndices i

theorem smooth_radial_support_data
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin n → K)
    (T : Submodule K (Fin n → K)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
        polarization F t u v = 0)
    (hradial : ∀ t ∈ T, polarization F x x t = 0) :
    Nonempty (SmoothRadialSupportData F x T) := by
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
  exact ⟨⟨A, hnonnegative, hsemi.nonnegative_weight_sum hF (basisMatrix A.basis)
    (basisMatrix_injective A.basis) _ hnonnegative⟩⟩

def SmoothRadialSupportData.defect
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialSupportData F x T) : ℕ :=
  (E.adapted.kernelIndices \ E.adapted.tangentIndices).card

theorem SmoothRadialSupportData.total_weight_eq
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialSupportData F x T) :
    ∑ i, smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i =
      (n : ℤ) - 3 * ((finrank K T : ℤ) - ((hessian F x).rank : ℤ)) - E.defect - 3 := by
  rw [sum_smoothRadialWeight_difference, E.adapted.tangent_card, E.adapted.kernel_card]
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change (hessian F x).rank + _ = n at hr
  unfold defect
  omega

/-- The four possible variable weights, with the zero block explicitly
identified as the part of the kernel outside the tangent space. -/
theorem SmoothRadialSupportData.weight_values
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialSupportData F x T) (i : Fin n) :
    smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i =
      if i ∈ E.adapted.tangentIndices ∩ E.adapted.kernelIndices ∨ i = E.adapted.radial then -2
      else if i ∈ E.adapted.kernelIndices then 0
      else if i ∈ E.adapted.tangentIndices then 1 else 4 := by
  have hrT := E.adapted.radial_mem_tangent
  have hrL := E.adapted.radial_notMem_kernel
  by_cases hir : i = E.adapted.radial
  · subst i
    simp [smoothRadialWeight, hrT, hrL]
  · by_cases hiT : i ∈ E.adapted.tangentIndices <;>
      by_cases hiL : i ∈ E.adapted.kernelIndices <;>
      simp [smoothRadialWeight, hir, hiT, hiL]

theorem SmoothRadialSupportData.kernel_le_tangent_of_defect_zero
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {T : Submodule K (Fin n → K)}
    (E : SmoothRadialSupportData F x T) (h : E.defect = 0) :
    LinearMap.ker (hessian F x).mulVecLin ≤ T := by
  have hsub : E.adapted.kernelIndices ⊆ E.adapted.tangentIndices :=
    Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h)
  calc
    LinearMap.ker (hessian F x).mulVecLin =
        Submodule.span K (E.adapted.basis '' (E.adapted.kernelIndices : Set (Fin n))) :=
      E.adapted.kernel_span.symm
    _ ≤ Submodule.span K (E.adapted.basis '' (E.adapted.tangentIndices : Set (Fin n))) :=
      Submodule.span_mono (Set.image_mono hsub)
    _ = T := E.adapted.tangent_span

theorem SmoothRadialSupportData.defect_le_one_of_thirteen
    {F : MvPolynomial (Fin 13) K} {x : Fin 13 → K} {T : Submodule K (Fin 13 → K)}
    (E : SmoothRadialSupportData F x T)
    (he : (finrank K T : ℤ) - ((hessian F x).rank : ℤ) = 3) :
    E.defect ≤ 1 ∧
      ∑ i, smoothRadialWeight E.adapted.radial E.adapted.tangentIndices E.adapted.kernelIndices i =
        1 - (E.defect : ℤ) := by
  have hs := E.total_weight_eq
  rw [he] at hs
  have hh := E.total_weight_nonnegative
  constructor <;> omega

end HessianTheorem11
