import HessianTheorem11.CoisotropicBasis

/-! Applying the constructed coisotropic basis to an actual cubic Hessian. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem hessian_coisotropic_of_conormal_image
    (F : MvPolynomial (Fin n) K) (x : Fin n → K)
    (T : Submodule K (Fin n → K))
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (himage : (coordinatePairing (K := K) (n := n)).orthogonal T ≤
      LinearMap.range ((hessian F x).mulVecLin.domRestrict T)) :
    (hessianBilinear F x).orthogonal T ≤ T := by
  intro u hu
  have hcon : (hessian F x).mulVec u ∈ (coordinatePairing (K := K) (n := n)).orthogonal T := by
    intro t ht
    have h := hu t ht
    change hessianBilinear F x t u = 0 at h
    rw [hessianBilinear_apply] at h
    exact h
  obtain ⟨v,hv⟩ := himage hcon
  have hdiff : u-(v : Fin n → K) ∈ LinearMap.ker (hessian F x).mulVecLin := by
    rw [LinearMap.mem_ker, map_sub]
    change (hessian F x).mulVec u - (hessian F x).mulVec v = 0
    exact sub_eq_zero.mpr hv.symm
  have hadd := T.add_mem (hker hdiff) v.property
  simpa using hadd

theorem radial_mem_hessian_orthogonal_of_conormal_gradient
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (T : Submodule K (Fin n → K))
    (hgrad : gradient F x ∈ (coordinatePairing (K := K) (n := n)).orthogonal T) :
    x ∈ (hessianBilinear F x).orthogonal T := by
  intro t ht
  change hessianBilinear F x t x = 0
  rw [hessianBilinear_apply]
  change dotProduct t ((hessian F x).mulVec x) = 0
  rw [hessian_mulVec_self hF, dotProduct_smul]
  have h := hgrad t ht
  change dotProduct t (gradient F x) = 0 at h
  rw [h, smul_zero]

theorem exists_cubic_coisotropic_basis
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (hx : gradient F x ≠ 0)
    (T : Submodule K (Fin n → K))
    (hker : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (hgrad : gradient F x ∈ (coordinatePairing (K := K) (n := n)).orthogonal T)
    (himage : (coordinatePairing (K := K) (n := n)).orthogonal T ≤
      LinearMap.range ((hessian F x).mulVecLin.domRestrict T)) :
    ∃ m d q, Nonempty (CoisotropicBasis.Data (hessianBilinear F x) T x m d q) := by
  apply CoisotropicBasis.exists_data _ (hessianBilinear_symmetric F x) T
  · rwa [ker_hessianBilinear]
  · exact hessian_coisotropic_of_conormal_image F x T hker himage
  · exact radial_mem_hessian_orthogonal_of_conormal_gradient F hF x T hgrad
  · rw [ker_hessianBilinear]
    exact self_notMem_hessian_ker_of_gradient_ne_zero hF x hx

namespace CoisotropicBasis.Data

theorem hessian_dimensions
    {F : MvPolynomial (Fin n) K} {x : Fin n → K}
    {T : Submodule K (Fin n → K)} {m d q : ℕ}
    (D : Data (hessianBilinear F x) T x m d q) :
    m + (hessian F x).rank = n ∧ 2*d+q = (hessian F x).rank := by
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hm := D.radical_dimension
  rw [ker_hessianBilinear] at hm
  have hn := D.dimension
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hr hn
  change (hessian F x).rank + _ = n at hr
  omega

theorem radical_hessian_kernel
    {F : MvPolynomial (Fin n) K} {x : Fin n → K}
    {T : Submodule K (Fin n → K)} {m d q : ℕ}
    (D : Data (hessianBilinear F x) T x m d q) (i : Fin m) :
    D.basis (Sum.inl i) ∈ LinearMap.ker (hessian F x).mulVecLin := by
  rw [← ker_hessianBilinear]
  exact D.radical_vectors i

theorem thirteen_codimension_three_middle_one
    {F : MvPolynomial (Fin 13) K} {x : Fin 13 → K}
    {T : Submodule K (Fin 13 → K)} {m d q : ℕ}
    (D : Data (hessianBilinear F x) T x m d q)
    (hT : finrank K T = 10) (hker : finrank K (LinearMap.ker (hessian F x).mulVecLin) = 6) :
    m = 6 ∧ d = 3 ∧ q = 1 := by
  have hm := D.radical_dimension
  rw [ker_hessianBilinear, hker] at hm
  have hc := D.codimension
  have hd := D.dimension
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hc hd
  omega

theorem thirteen_codimension_two_middle_four
    {F : MvPolynomial (Fin 13) K} {x : Fin 13 → K}
    {T : Submodule K (Fin 13 → K)} {m d q : ℕ}
    (D : Data (hessianBilinear F x) T x m d q)
    (hT : finrank K T = 11) (hker : finrank K (LinearMap.ker (hessian F x).mulVecLin) = 5) :
    m = 5 ∧ d = 2 ∧ q = 4 := by
  have hm := D.radical_dimension
  rw [ker_hessianBilinear, hker] at hm
  have hc := D.codimension
  have hd := D.dimension
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hc hd
  omega

end CoisotropicBasis.Data
end HessianTheorem11
