import HessianTheorem11.Polarization
import HessianTheorem11.Semistability
import HessianTheorem11.SimultaneousBasis

/-!
The smooth radial weights of Proposition 6.2, applied to the actual cubic
polarization tensor. The two index sets describe a basis simultaneously adapted
to the tangent space and Hessian kernel. All vanishings are explicit tensor or
matrix equations; no geometric dimension estimate is an input.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

/-- Weights `−2, 1, 0, 4` on `T ∩ L`, `T \ L`, `L \ T`, and the
complement of `T ∪ L`, with an additional subtraction of `3` at the radial
coordinate. When the radial vector lies in `T \ L`, its resulting weight is `−2`. -/
def smoothRadialWeight {n : ℕ} (radial : Fin n) (IT IL : Finset (Fin n))
    (i : Fin n) : ℤ :=
  (if i = radial then -3 else 0) + 4 - (if i ∈ IT then 3 else 0) -
    (if i ∈ IL then 4 else 0) + (if i ∈ IT ∩ IL then 1 else 0)

theorem smoothRadialWeight_radial {n : ℕ} {radial : Fin n} {IT IL : Finset (Fin n)}
    (hrT : radial ∈ IT) (hrL : radial ∉ IL) :
    smoothRadialWeight radial IT IL radial = -2 := by
  simp [smoothRadialWeight, hrT, hrL]

theorem smoothRadialWeight_normal {n : ℕ} {radial i : Fin n} {IT IL : Finset (Fin n)}
    (hrT : radial ∈ IT) (hiT : i ∉ IT) (hiL : i ∉ IL) :
    smoothRadialWeight radial IT IL i = 4 := by
  have hne : i ≠ radial := by rintro rfl; exact hiT hrT
  simp [smoothRadialWeight, hne, hiT, hiL]

theorem smoothRadialWeight_outside_kernel {n : ℕ} {radial i : Fin n}
    {IT IL : Finset (Fin n)} (hne : i ≠ radial) (hiL : i ∉ IL) :
    1 ≤ smoothRadialWeight radial IT IL i := by
  unfold smoothRadialWeight
  simp only [hne, if_false, hiL, Finset.mem_inter, and_false]
  split_ifs <;> norm_num

theorem sum_smoothRadialWeight {n : ℕ} (radial : Fin n) (IT IL : Finset (Fin n)) :
    ∑ i, smoothRadialWeight radial IT IL i =
      4 * (n : ℤ) - 3 * (IT.card : ℤ) - 4 * (IL.card : ℤ) +
        ((IT ∩ IL).card : ℤ) - 3 := by
  classical
  unfold smoothRadialWeight
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ i : Fin n, if i = radial then (-3 : ℤ) else 0) = -3 := by simp
  have h2 : (∑ i : Fin n, if i ∈ IT then (3 : ℤ) else 0) = 3 * IT.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have h3 : (∑ i : Fin n, if i ∈ IL then (4 : ℤ) else 0) = 4 * IL.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have h4 : (∑ i : Fin n, if i ∈ IT ∩ IL then (1 : ℤ) else 0) = (IT ∩ IL).card := by
    rw [← Finset.sum_filter]
    rw [show Finset.univ.filter (fun i => i ∈ IT ∩ IL) = IT ∩ IL by ext i; simp]
    simp
  rw [h1, h2, h3, h4]
  simp
  ring

/-- The same total expressed using the tangent dimension, Hessian corank,
and the part of the kernel outside the tangent space. -/
theorem sum_smoothRadialWeight_difference {n : ℕ} (radial : Fin n)
    (IT IL : Finset (Fin n)) :
    ∑ i, smoothRadialWeight radial IT IL i =
      (n : ℤ) - 3 * ((IT.card : ℤ) - ((n : ℤ) - (IL.card : ℤ))) -
        ((IL \ IT).card : ℤ) - 3 := by
  rw [sum_smoothRadialWeight]
  have hc : (IL \ IT).card + (IT ∩ IL).card = IL.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter IL IT
  have hc' : ((IL \ IT).card : ℤ) + ((IT ∩ IL).card : ℤ) = (IL.card : ℤ) := by
    exact_mod_cast hc
  omega

private theorem smoothRadialWeight_nonnegative_without_radial
    {n : ℕ} {radial i j l : Fin n} {IT IL : Finset (Fin n)}
    (hir : i ≠ radial) (hjr : j ≠ radial) (hlr : l ≠ radial)
    (hi : i ∈ IT → j ∈ IL → l ∈ IL → False)
    (hj : j ∈ IT → i ∈ IL → l ∈ IL → False)
    (hl : l ∈ IT → i ∈ IL → j ∈ IL → False) :
    0 ≤ smoothRadialWeight radial IT IL i + smoothRadialWeight radial IT IL j +
      smoothRadialWeight radial IT IL l := by
  by_cases hiT : i ∈ IT <;> by_cases hiL : i ∈ IL <;>
    by_cases hjT : j ∈ IT <;> by_cases hjL : j ∈ IL <;>
    by_cases hlT : l ∈ IT <;> by_cases hlL : l ∈ IL <;>
    simp_all [smoothRadialWeight]

section Tensor
variable {K : Type*} [Field K] {n : ℕ}

theorem smoothRadialWeight_nonnegative_tensor
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (b : Basis (Fin n) K (Fin n → K)) (radial : Fin n) (IT IL : Finset (Fin n))
    (hrT : radial ∈ IT) (hrL : radial ∉ IL)
    (hkernel : ∀ i ∈ IL, (hessian F (b radial)).mulVec (b i) = 0)
    (htangent : ∀ i ∈ IT, ∀ j ∈ IL, ∀ l ∈ IL,
      polarization F (b i) (b j) (b l) = 0)
    (hradial : ∀ i ∈ IT, polarization F (b radial) (b radial) (b i) = 0)
    (i j l : Fin n) (hne : polarization F (b i) (b j) (b l) ≠ 0) :
    0 ≤ smoothRadialWeight radial IT IL i + smoothRadialWeight radial IT IL j +
      smoothRadialWeight radial IT IL l := by
  have hradzero (a c : Fin n) (ha : a ∈ IL) :
      polarization F (b radial) (b a) (b c) = 0 := by
    rw [polarization_rotate hF, polarization_swap_last hF]
    change dotProduct (b c) ((hessian F (b radial)).mulVec (b a)) = 0
    rw [hkernel a ha]
    simp
  have hradweights (a c : Fin n)
      (h : polarization F (b radial) (b a) (b c) ≠ 0) :
      0 ≤ smoothRadialWeight radial IT IL radial + smoothRadialWeight radial IT IL a +
        smoothRadialWeight radial IT IL c := by
    have haL : a ∉ IL := fun ha => h (hradzero a c ha)
    have hcL : c ∉ IL := by
      intro hc
      apply h
      rw [polarization_swap_last hF]
      exact hradzero c a hc
    by_cases har : a = radial
    · subst a
      have hcT : c ∉ IT := fun hc => h (hradial c hc)
      rw [smoothRadialWeight_radial hrT hrL, smoothRadialWeight_normal hrT hcT hcL]
      norm_num
    by_cases hcr : c = radial
    · subst c
      have haT : a ∉ IT := by
        intro ha
        apply h
        rw [polarization_swap_last hF]
        exact hradial a ha
      rw [smoothRadialWeight_radial hrT hrL, smoothRadialWeight_normal hrT haT haL]
      norm_num
    have ha := smoothRadialWeight_outside_kernel (IT := IT) har haL
    have hc := smoothRadialWeight_outside_kernel (IT := IT) hcr hcL
    rw [smoothRadialWeight_radial hrT hrL]
    omega
  by_cases hir : i = radial
  · subst i
    exact hradweights j l hne
  by_cases hjr : j = radial
  · subst j
    have h' : polarization F (b radial) (b i) (b l) ≠ 0 := by
      rwa [polarization_swap_first]
    have h := hradweights i l h'
    omega
  by_cases hlr : l = radial
  · subst l
    have h' : polarization F (b radial) (b i) (b j) ≠ 0 := by
      intro hz
      apply hne
      rw [polarization_rotate hF]
      exact hz
    have h := hradweights i j h'
    omega
  apply smoothRadialWeight_nonnegative_without_radial hir hjr hlr
  · intro hi hj hl
    exact hne (htangent i hi j hj l hl)
  · intro hj hi hl
    apply hne
    rw [polarization_swap_first]
    exact htangent j hj i hi l hl
  · intro hl hi hj
    apply hne
    rw [polarization_rotate hF]
    exact htangent l hl i hi j hj

variable [CharZero K]

/-- Semistability converts the proved tensor support constraint into the
smooth radial numerical inequality, with the kernel-transverse correction. -/
theorem smooth_radial_of_tensor_vanishing
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F)
    (b : Basis (Fin n) K (Fin n → K)) (radial : Fin n) (IT IL : Finset (Fin n))
    (hrT : radial ∈ IT) (hrL : radial ∉ IL)
    (hkernel : ∀ i ∈ IL, (hessian F (b radial)).mulVec (b i) = 0)
    (htangent : ∀ i ∈ IT, ∀ j ∈ IL, ∀ l ∈ IL,
      polarization F (b i) (b j) (b l) = 0)
    (hradial : ∀ i ∈ IT, polarization F (b radial) (b radial) (b i) = 0) :
    3 * ((IT.card : ℤ) - ((n : ℤ) - (IL.card : ℤ))) + 3 ≤
      (n : ℤ) - ((IL \ IT).card : ℤ) := by
  have hsum : 0 ≤ ∑ i, smoothRadialWeight radial IT IL i := by
    apply hsemi.nonnegative_weight_sum_of_thirdPartials hF
      (basisMatrix b) (basisMatrix_injective b) (smoothRadialWeight radial IT IL)
    intro i j l hne
    change coeff 0 (pderiv l (pderiv j (pderiv i
      (PolynomialRestriction.restrict (basisMatrix b) F)))) ≠ 0 at hne
    rw [polarization_in_coordinates F hF] at hne
    exact smoothRadialWeight_nonnegative_tensor F hF b radial IT IL hrT hrL
      hkernel htangent hradial i j l hne
  rw [sum_smoothRadialWeight_difference] at hsum
  omega

/-- The intrinsic smooth radial bound. The simultaneous basis is constructed
from the actual tangent subspace and Hessian kernel. -/
theorem smooth_radial_subspace_of_tensor_vanishing
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F) (x : Fin n → K)
    (T : Submodule K (Fin n → K)) (hxT : x ∈ T)
    (hxL : x ∉ LinearMap.ker (hessian F x).mulVecLin)
    (htensor : ∀ t ∈ T,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
      polarization F t u v = 0)
    (hradial : ∀ t ∈ T, polarization F x x t = 0) :
    3 * ((finrank K T : ℤ) - ((hessian F x).rank : ℤ)) + 3 ≤ (n : ℤ) := by
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
  have hbound := smooth_radial_of_tensor_vanishing F hF hsemi A.basis A.radial
    A.tangentIndices A.kernelIndices A.radial_mem_tangent A.radial_notMem_kernel
    hkernel htangent hrad
  rw [A.tangent_card, A.kernel_card] at hbound
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change (hessian F x).rank + finrank K L = n at hr
  have hc : (0 : ℤ) ≤ ((A.kernelIndices \ A.tangentIndices).card : ℤ) := by positivity
  omega

end Tensor
end HessianTheorem11
