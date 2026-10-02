import HessianTheorem11.SingularRadial
import HessianTheorem11.PolarizationExpansion

/-! The cubic-zero singular-kernel obstruction, source Lemma 11.3.
It follows from the already proved actual radial weight argument, with the
whole Hessian kernel as the tangent subspace. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Module
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem polarization_eq_third_difference
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (u v w : Fin n → K) :
    polarization F u v w =
      eval (u + v + w) F - eval (u + v) F - eval (u + w) F - eval (v + w) F +
        eval u F + eval v F + eval w F := by
  simp only [eval_cubic_add hF, polarization_add_first, polarization_add_second]
  rw [polarization_swap_first F v u w]
  ring

theorem polarization_zero_on_cubic_zero_subspace
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    (L : Submodule K (Fin n → K)) (hL : ∀ z ∈ L, eval z F = 0)
    (u : Fin n → K) (hu : u ∈ L) (v : Fin n → K) (hv : v ∈ L)
    (w : Fin n → K) (hw : w ∈ L) : polarization F u v w = 0 := by
  rw [polarization_eq_third_difference hF]
  rw [hL _ (L.add_mem (L.add_mem hu hv) hw), hL _ (L.add_mem hu hv),
    hL _ (L.add_mem hu hw), hL _ (L.add_mem hv hw), hL u hu, hL v hv, hL w hw]
  ring

/-- If the full Hessian kernel at a nonzero singular point is cubic-zero,
its rank must satisfy 3r ≥ n+3. -/
theorem singular_cubic_zero_kernel_rank_bound
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (hsemi : WeightSemistable F)
    (x : Fin n → K) (hx : x ≠ 0) (hsing : gradient F x = 0)
    (hzero : ∀ z ∈ LinearMap.ker (hessian F x).mulVecLin, eval z F = 0) :
    n + 3 ≤ 3 * (hessian F x).rank := by
  let L := LinearMap.ker (hessian F x).mulVecLin
  have hxL : x ∈ L := by
    change (hessian F x).mulVec x = 0
    rw [hessian_mulVec_self hF, hsing, smul_zero]
  have hb := singular_radial_of_tensor_vanishing F hF hsemi x hx L hxL le_rfl
    (polarization_zero_on_cubic_zero_subspace hF L hzero)
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hn : finrank K (Fin n → K) = n := by simp
  rw [hn] at hr
  change (hessian F x).rank + finrank K L = n at hr
  omega

end HessianTheorem11
