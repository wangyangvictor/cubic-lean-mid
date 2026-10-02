import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The common zero subspace of a rank-two map on a five-dimensional
space and one further linear functional has dimension at least two. -/
noncomputable section
namespace HessianTheorem11
open Module
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

def scalarZeroSubspace (e : V →ₗ[K] W) (α : LinearMap.ker e →ₗ[K] K) : Submodule K V :=
  (LinearMap.ker α).map (LinearMap.ker e).subtype

theorem scalarZeroSubspace_le_ker (e : V →ₗ[K] W) (α : LinearMap.ker e →ₗ[K] K) :
    scalarZeroSubspace e α ≤ LinearMap.ker e := by
  rintro z ⟨u,hu,rfl⟩
  exact u.property

theorem scalarZeroSubspace_value (e : V →ₗ[K] W) (α : LinearMap.ker e →ₗ[K] K)
    (z : V) (hz : z ∈ scalarZeroSubspace e α) :
    α ⟨z,scalarZeroSubspace_le_ker e α hz⟩ = 0 := by
  obtain ⟨u,hu,he⟩ := hz
  have he' : (⟨z,scalarZeroSubspace_le_ker e α (by exact ⟨u,hu,he⟩)⟩ : LinearMap.ker e) = u :=
    Subtype.ext he.symm
  simpa only [he'] using hu

theorem scalarZeroSubspace_finrank (e : V →ₗ[K] W) (α : LinearMap.ker e →ₗ[K] K) :
    finrank K V ≤ finrank K (LinearMap.range e) + finrank K (scalarZeroSubspace e α) + 1 := by
  have he := e.finrank_range_add_finrank_ker
  have ha := α.finrank_range_add_finrank_ker
  have hr : finrank K (LinearMap.range α) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range α)
  have hd : finrank K (scalarZeroSubspace e α) = finrank K (LinearMap.ker α) :=
    (Submodule.equivMapOfInjective (LinearMap.ker e).subtype
      (LinearMap.ker e).subtype_injective (LinearMap.ker α)).finrank_eq.symm
  omega

theorem scalarZeroSubspace_finrank_ge_two (e : V →ₗ[K] W)
    (α : LinearMap.ker e →ₗ[K] K) (hd : finrank K V = 5)
    (he : finrank K (LinearMap.range e) = 2) :
    2 ≤ finrank K (scalarZeroSubspace e α) := by
  have h := scalarZeroSubspace_finrank e α
  omega

end HessianTheorem11
