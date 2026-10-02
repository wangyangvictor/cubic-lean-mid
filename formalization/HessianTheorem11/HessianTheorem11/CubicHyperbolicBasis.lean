import HessianTheorem11.HyperbolicBasis
import HessianTheorem11.GeometricRadial

/-! The hyperbolic coordinate basis is constructed from the actual Hessian
at a smooth point of the cubic. Its radical block has the actual Hessian
nullity, and the other block has dimension rank(H)-2. -/

noncomputable section
namespace HessianTheorem11
open Module MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

def hessianBilinear (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    LinearMap.BilinForm K (Fin n → K) := (hessian F x).toBilin'

theorem hessianBilinear_apply (F : MvPolynomial (Fin n) K) (x u v : Fin n → K) :
    hessianBilinear F x u v = polarization F u v x :=
  Matrix.toBilin'_apply' _ _ _

theorem hessianBilinear_symmetric (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    (hessianBilinear F x).IsSymm := by
  constructor
  intro u v
  simp only [hessianBilinear_apply]
  exact polarization_swap_first F u v x

theorem ker_hessianBilinear (F : MvPolynomial (Fin n) K) (x : Fin n → K) :
    LinearMap.ker (hessianBilinear F x) = LinearMap.ker (hessian F x).mulVecLin := by
  ext u
  have hB := hessianBilinear_symmetric F x
  constructor
  · intro hu
    change (hessian F x).mulVec u = 0
    apply dotProduct_eq_zero
    intro v
    rw [dotProduct_comm, ← Matrix.toBilin'_apply']
    change hessianBilinear F x v u = 0
    rw [hB.eq]
    exact congrArg (fun f : (Fin n → K) →ₗ[K] K => f v) hu
  · intro hu
    apply LinearMap.ext
    intro v
    change hessianBilinear F x u v = 0
    rw [hB.eq, hessianBilinear_apply]
    change dotProduct v ((hessian F x).mulVec u) = 0
    rw [show (hessian F x).mulVec u = 0 from hu]
    simp

theorem exists_cubic_hyperbolic_splitting
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (hx : eval x F = 0) (hgrad : gradient F x ≠ 0) :
    ∃ m q, Nonempty (HyperbolicBasis.Splitting (hessianBilinear F x) x m q) := by
  apply HyperbolicBasis.exists_splitting _ (hessianBilinear_symmetric F x)
  · rw [hessianBilinear_apply]
    unfold polarization
    rw [hessian_cubic_identity hF, hx, mul_zero]
  · rw [ker_hessianBilinear]
    exact self_notMem_hessian_ker_of_gradient_ne_zero hF x hgrad

namespace HyperbolicBasis.Splitting

theorem hessian_rank_dimensions
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {m q : ℕ}
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) :
    m + (hessian F x).rank = n ∧ q + 2 = (hessian F x).rank := by
  have hr := (hessian F x).mulVecLin.finrank_range_add_finrank_ker
  have hm := S.radical_dimension
  rw [ker_hessianBilinear] at hm
  have hn := S.ambient_dimension
  simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] at hr hn
  change (hessian F x).rank + _ = n at hr
  omega

theorem radical_hessian_kernel
    {F : MvPolynomial (Fin n) K} {x : Fin n → K} {m q : ℕ}
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) (i : Fin m) :
    S.basis (Sum.inl i) ∈ LinearMap.ker (hessian F x).mulVecLin := by
  rw [← ker_hessianBilinear]
  exact S.radical_vectors i

theorem radical_differential_zero
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x : Fin n → K} {m q : ℕ}
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) (i : Fin m) :
    polynomialDifferential F x (S.basis (Sum.inl i)) = 0 := by
  have hz : polarization F x x (S.basis (Sum.inl i)) = 0 := by
    rw [polarization_swap_last hF]
    unfold polarization
    rw [show (hessian F x).mulVec (S.basis (Sum.inl i)) = 0 from
      S.radical_hessian_kernel i]
    simp
  rw [polarization_self_self_eq_two_differential hF] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem middle_differential_zero
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous 3)
    {x : Fin n → K} {m q : ℕ}
    (S : HyperbolicBasis.Splitting (hessianBilinear F x) x m q) (j : Fin q) :
    polynomialDifferential F x (S.basis (Sum.inr (Sum.inl j))) = 0 := by
  have hz := S.middle_orthogonal j 0
  rw [S.radial_eq, hessianBilinear_apply, ← polarization_swap_last hF] at hz
  rw [polarization_self_self_eq_two_differential hF] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end HyperbolicBasis.Splitting
end HessianTheorem11
