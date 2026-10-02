import CubicTenVariables.HomogeneousOriginOpen
import CubicTenVariables.FiniteVariableEquations

/-! The proved homogeneous-origin principal-open theorem, reindexed from
`Fin n` to an arbitrary finite variable type. -/

set_option autoImplicit false
noncomputable section

namespace CubicTenVariables.HomogeneousOriginOpenFinite

open MvPolynomial

/-- Origin-only common zeros persist on a principal open for any finite
coordinate type.  This is only a variable-renaming adapter to
`HomogeneousOriginOpen.exists_principal_open`. -/
theorem exists_principal_open
    {sigma iota R Omega : Type*} [Fintype sigma] [Fintype iota]
    [CommRing R] [Field Omega] [IsAlgClosed Omega]
    (rho : R →+* Omega) (f : iota → MvPolynomial sigma R) (degree : iota → ℕ)
    (hf : ∀ j, (f j).IsHomogeneous (degree j))
    (horigin : ∀ x : sigma → Omega,
      (∀ j, eval x (map rho (f j)) = 0) → x = 0) :
    ∃ s : R, rho s ≠ 0 ∧
      ∀ (K : Type*) [Field K] [IsAlgClosed K] (tau : R →+* K), tau s ≠ 0 →
        ∀ x : sigma → K, (∀ j, eval x (map tau (f j)) = 0) → x = 0 := by
  classical
  let q : sigma ≃ Fin (Fintype.card sigma) := Fintype.equivFin sigma
  let g : iota → MvPolynomial (Fin (Fintype.card sigma)) R :=
    fun j ↦ rename q (f j)
  have hg : ∀ j, (g j).IsHomogeneous (degree j) := by
    intro j
    exact (hf j).rename_isHomogeneous
  have hzero : ∀ y : Fin (Fintype.card sigma) → Omega,
      (∀ j, eval y (map rho (g j)) = 0) → y = 0 := by
    intro y hy
    have hx : (fun i : sigma ↦ y (q i)) = 0 := by
      apply horigin
      intro j
      have hj := hy j
      simpa only [g, map_rename, eval_rename, Function.comp_def] using hj
    funext j
    have hj := congrArg (fun z : sigma → Omega ↦ z (q.symm j)) hx
    simpa only [Pi.zero_apply, q.apply_symm_apply] using hj
  obtain ⟨s, hs, hgood⟩ :=
    HomogeneousOriginOpen.exists_principal_open rho g degree hg hzero
  refine ⟨s, hs, ?_⟩
  intro K _ _ tau htau x hx
  let y : Fin (Fintype.card sigma) → K := fun j ↦ x (q.symm j)
  have hy : y = 0 := by
    apply hgood K tau htau y
    intro j
    have hj := hx j
    simpa only [g, y, map_rename, eval_rename, Function.comp_def,
      q.symm_apply_apply] using hj
  funext i
  have hi := congrArg (fun z : Fin (Fintype.card sigma) → K ↦ z (q i)) hy
  simpa only [y, q.symm_apply_apply, Pi.zero_apply] using hi

end CubicTenVariables.HomogeneousOriginOpenFinite
