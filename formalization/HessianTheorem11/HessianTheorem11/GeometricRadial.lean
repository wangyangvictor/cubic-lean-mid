import HessianTheorem11.SmoothRadialWeights
import HessianTheorem11.SingularRadial
import HessianTheorem11.TextbookGeometry

/-!
The common radial inequality for an actual subset of the cubic zero set. The
only geometric input is the general determinantal tangent formula. The smooth
and singular branches use the actual vanishing ideal tangent space, the cubic
Euler identity, and the already proved radial weight arguments.
-/

noncomputable section
namespace HessianTheorem11
open MvPolynomial Module

section Differential
variable {K : Type*} [Field K] {n : ℕ}

/-- Euler's identity expresses the radial tensor as twice the differential. -/
theorem polarization_self_self_eq_two_differential
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x t : Fin n → K) :
    polarization F x x t = 2 * polynomialDifferential F x t := by
  rw [polarization_rotate hF]
  unfold polarization
  rw [hessian_mulVec_self hF, polynomialDifferential_apply]
  simp only [dotProduct, Pi.smul_apply, nsmul_eq_mul, gradient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Differentiating the actual cubic equation on a subset supplies the
radial-radial-tangent tensor vanishing used in the smooth weight argument. -/
theorem polarization_self_self_tangent_zero
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (Z : Set (Fin n → K)) (hcontained : ∀ y ∈ Z, eval y F = 0)
    (x t : Fin n → K) (ht : t ∈ affineTangentSpace Z x) :
    polarization F x x t = 0 := by
  have hFZ : F ∈ vanishingIdeal K Z := hcontained
  have hd := mem_affineTangentSpace.mp ht F hFZ
  rw [polarization_self_self_eq_two_differential hF, hd, mul_zero]

variable [CharZero K]

/-- A smooth point of a cubic is transverse to its Hessian kernel. -/
theorem self_notMem_hessian_ker_of_gradient_ne_zero
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (hgradient : gradient F x ≠ 0) :
    x ∉ LinearMap.ker (hessian F x).mulVecLin := by
  intro hx
  have hz : (hessian F x).mulVec x = 0 := hx
  rw [hessian_mulVec_self hF] at hz
  apply hgradient
  ext i
  have hi := congrFun hz i
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

end Differential

/-- The determinantal tangent input supplies the actual cubic tensor
vanishing on one tangent direction and two Hessian-kernel directions. -/
theorem hessian_tangent_polarization_zero
    (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n) (hxZ : x ∈ Z)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank) :
    ∀ t ∈ affineTangentSpace Z x,
      ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
        polarization F t u v = 0 := by
  intro t ht u hu v hv
  have hp := DT.tangent_kernel_pairing (hessianLinearMap F hF)
    (hessian_symmetric F) Z x hxZ hmax t ht u hu v hv
  rw [polarization_swap_first, polarization_swap_last hF]
  exact hp

/-- The stronger common radial inequality in the singular branch. -/
theorem geometric_singular_radial_inequality
    (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n)
    (hxZ : x ∈ Z) (hx0 : x ≠ 0) (hxT : x ∈ affineTangentSpace Z x)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hsingular : ∀ y ∈ Z, gradient F y = 0) :
    3 * ((finrank GeometricField (affineTangentSpace Z x) : ℤ) -
      ((hessian F x).rank : ℤ)) + 6 ≤ (n : ℤ) := by
  have hTL := affineTangentSpace_le_hessian_ker F Z hsingular x
  have htensor := hessian_tangent_polarization_zero DT F hF Z x hxZ hmax
  have hrad := singular_radial_of_tensor_vanishing F hF hsemi x hx0
    (affineTangentSpace Z x) hxT hTL htensor
  have hdim := matrix_rank_add_finrank_le_of_le_ker (hessian F x)
    (affineTangentSpace Z x) hTL
  omega

/-- The common radial bound for a rank-maximal radial tangent point of a
subset of the cubic. If the chosen point is singular, the entire subset must
lie in the singular locus. This is the ordinary generic-point dichotomy that
geometric applications arrange when choosing the point. -/
theorem geometric_radial_inequality
    (DT : SymmetricDeterminantalTangentInput)
    {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F)
    (Z : Set (GeometricPoint n)) (x : GeometricPoint n)
    (hxZ : x ∈ Z) (hx0 : x ≠ 0) (hxT : x ∈ affineTangentSpace Z x)
    (hmax : ∀ y ∈ Z, (hessian F y).rank ≤ (hessian F x).rank)
    (hcontained : ∀ y ∈ Z, eval y F = 0)
    (hgenericSing : gradient F x = 0 → ∀ y ∈ Z, gradient F y = 0) :
    3 * ((finrank GeometricField (affineTangentSpace Z x) : ℤ) -
      ((hessian F x).rank : ℤ)) + 3 ≤ (n : ℤ) := by
  by_cases hs : gradient F x = 0
  · have h := geometric_singular_radial_inequality DT F hF hsemi Z x
      hxZ hx0 hxT hmax (hgenericSing hs)
    omega
  · apply smooth_radial_subspace_of_tensor_vanishing F hF hsemi x
      (affineTangentSpace Z x) hxT
      (self_notMem_hessian_ker_of_gradient_ne_zero hF x hs)
    · exact hessian_tangent_polarization_zero DT F hF Z x hxZ hmax
    · intro t ht
      exact polarization_self_self_tangent_zero hF Z hcontained x t ht

end HessianTheorem11
