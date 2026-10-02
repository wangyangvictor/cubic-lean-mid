import HessianTheorem11.ReducedDeterminantalTangent

/-!
The rational tangent-space step in Davenport's geometric argument.

At a point of maximal Hessian rank in any rational point set, the reduced
rational tangent space meets the Hessian kernel trivially. Rational anisotropy
and the proved determinantal tangent formula give this without smoothness,
irreducibility, or a dimension theorem. This module does not assert a
rational-closure dimension bound or an integer-point counting bound.
-/

noncomputable section
namespace CubicTenVariables.DavenportTangent
open MvPolynomial HessianTheorem11 Module

/-- The actual reduced rational tangent space and the actual Hessian kernel
have zero intersection at any point of maximal rank in a rational point set. -/
theorem tangent_inf_hessian_ker_eq_bot {n : ℕ}
    (F : AnisotropicCubic n) (Z : Set (Fin n → ℚ)) (x : Fin n → ℚ)
    (hx : x ∈ Z)
    (hmax : ∀ y ∈ Z, (hessian F.polynomial y).rank ≤
      (hessian F.polynomial x).rank) :
    affineTangentSpace Z x ⊓ LinearMap.ker (hessian F.polynomial x).mulVecLin = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  change y = 0
  apply F.anisotropic
  have hp := (provedDeterminantalTangentOver ℚ).tangent_kernel_pairing
    (hessianLinearMap F.polynomial F.homogeneous)
    (hessian_symmetric F.polynomial) Z x hx hmax y hy.1 y hy.2 y hy.2
  change dotProduct y ((hessian F.polynomial y).mulVec y) = 0 at hp
  have he := hessian_cubic_identity F.homogeneous y
  rw [hp] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- At a maximal-rank rational point, the tangent dimension is at most the
Hessian rank. Neither smoothness nor rational density is a premise. -/
theorem tangent_finrank_le_hessian_rank {n : ℕ}
    (F : AnisotropicCubic n) (Z : Set (Fin n → ℚ)) (x : Fin n → ℚ)
    (hx : x ∈ Z)
    (hmax : ∀ y ∈ Z, (hessian F.polynomial y).rank ≤
      (hessian F.polynomial x).rank) :
    finrank ℚ (affineTangentSpace Z x) ≤ (hessian F.polynomial x).rank := by
  let T := affineTangentSpace Z x
  let H := (hessian F.polynomial x).mulVecLin
  have hinf : T ⊓ LinearMap.ker H = ⊥ :=
    tangent_inf_hessian_ker_eq_bot F Z x hx hmax
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.ker H)
  rw [hinf, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (T ⊔ LinearMap.ker H)
  have hnull := H.finrank_range_add_finrank_ker
  have hambient : finrank ℚ (Fin n → ℚ) = n := by simp
  rw [hambient] at hle hnull
  change (hessian F.polynomial x).rank + finrank ℚ (LinearMap.ker H) = n at hnull
  change finrank ℚ T ≤ _
  omega

/-- The exact-rank locus has rational tangent dimension at most that rank
at every one of its rational points. This concerns its reduced rational
vanishing ideal, not the geometric locus over an algebraic closure. -/
theorem rank_locus_tangent_finrank_le {n r : ℕ}
    (F : AnisotropicCubic n) (x : Fin n → ℚ)
    (hx : (hessian F.polynomial x).rank = r) :
    finrank ℚ (affineTangentSpace
      {y : Fin n → ℚ | (hessian F.polynomial y).rank = r} x) ≤ r := by
  have ht := tangent_finrank_le_hessian_rank F
    {y : Fin n → ℚ | (hessian F.polynomial y).rank = r} x hx
    (fun y hy => le_of_eq (hy.trans hx.symm))
  simpa only [hx] using ht

end CubicTenVariables.DavenportTangent
