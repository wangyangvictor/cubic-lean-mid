import HessianTheorem11.UnconditionalFlagProjection
import Mathlib.Algebra.BigOperators.Fin

/-! An explicit basis of a hyperplane obtained by projecting all but a pivot
column of an existing basis. This is actual finite-dimensional linear algebra. -/
noncomputable section
namespace HessianTheorem11.UnconditionalFlags
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Project every nonpivot basis vector into the hyperplane kernel. -/
theorem exists_projected_kernel_basis {n : ℕ} (b : Basis (Fin (n+1)) K V)
    (l : V →ₗ[K] K) (j : Fin (n+1)) (hj : l (b j) ≠ 0) :
    ∃ c : Basis (Fin n) K (LinearMap.ker l), ∀ i,
      (c i : V) = hyperplaneProjection l ((l (b j))⁻¹ • b j) (b (j.succAbove i)) := by
  classical
  let v := (l (b j))⁻¹ • b j
  have hv : l v = 1 := by simp [v,hj]
  let p := hyperplaneProjection l v
  let f : Fin n → LinearMap.ker l := fun i =>
    ⟨p (b (j.succAbove i)),projection_mem_ker l v hv _⟩
  have hcoord (i k : Fin n) :
      b.coord (j.succAbove k) (f i : V) = if i = k then 1 else 0 := by
    simp [f,p,hyperplaneProjection_apply,v,Basis.coord_apply,
      Fin.succAbove_ne,Finsupp.single_apply]
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have he := congrArg (fun x : LinearMap.ker l => b.coord (j.succAbove k) (x : V)) hg
    simpa only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,hcoord,
      smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
      if_true,Submodule.coe_zero,map_zero] using he
  have hpj : p (b j) = 0 := by simp [p,v,smul_smul,hj]
  have hsp : ⊤ ≤ Submodule.span K (Set.range f) := by
    intro x _
    have he : ∑ i : Fin n, b.repr (x : V) (j.succAbove i) • f i = x := by
      apply Subtype.ext
      have e := congrArg p (b.sum_repr (x : V))
      rw [map_sum,Fin.sum_univ_succAbove _ j] at e
      simpa [f,hpj,projection_eq_self l v (x : V) x.property,p] using e
    rw [← he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))
  exact ⟨Basis.mk hli hsp,fun i => by simp [Basis.mk_apply,f,p,v]⟩

end HessianTheorem11.UnconditionalFlags
