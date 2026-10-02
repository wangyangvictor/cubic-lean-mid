import HessianTheorem11.Polarization
import HessianTheorem11.SingularLinearAlgebra

/-! The equality step in incidence concentration. Equality of the actual
restriction nullity with the full nullity forces full-kernel containment. -/

noncomputable section
namespace HessianTheorem11
open Module MvPolynomial

theorem ker_le_of_restriction_nullity_equality
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (A : V →ₗ[K] W) (T : Submodule K V)
    (balance : finrank K T = finrank K (LinearMap.range (A.domRestrict T)) +
      finrank K (LinearMap.ker A)) : LinearMap.ker A ≤ T := by
  let S := (LinearMap.ker (A.domRestrict T)).map T.subtype
  have hSK : S ≤ LinearMap.ker A := by
    rintro v ⟨u, hu, rfl⟩
    exact hu
  have hST : S ≤ T := by
    rintro v ⟨u, _, rfl⟩
    exact u.property
  have hd : finrank K S = finrank K (LinearMap.ker A) := by
    change finrank K ((LinearMap.ker (A.domRestrict T)).map T.subtype) = _
    rw [Submodule.finrank_map_subtype_eq]
    have hr := (A.domRestrict T).finrank_range_add_finrank_ker
    omega
  have heq : S = LinearMap.ker A := Submodule.eq_of_le_of_finrank_eq hSK hd
  rwa [heq] at hST

theorem cubic_vanishes_on_kernel_of_tangent_containment
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous 3)
    (x : Fin n → K) (T : Submodule K (Fin n → K))
    (hKT : LinearMap.ker (hessian F x).mulVecLin ≤ T)
    (htensor : ∀ t ∈ T, ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian F x).mulVecLin,
        polarization F t u v = 0) :
    ∀ u ∈ LinearMap.ker (hessian F x).mulVecLin, eval u F = 0 := by
  intro u hu
  have hz := htensor u (hKT hu) u hu u hu
  have he := hessian_cubic_identity hF u
  change dotProduct u ((hessian F u).mulVec u) = 0 at hz
  rw [hz] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

end HessianTheorem11
