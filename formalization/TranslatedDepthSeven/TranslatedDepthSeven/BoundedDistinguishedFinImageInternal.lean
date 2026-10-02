import TranslatedDepthSeven.BoundedDistinguishedEliminationInternal
import TranslatedDepthSeven.FiniteLinearProjectionImageCertificateInternal
import TranslatedDepthSeven.ProjectiveDegreeSeparatorAllChartsInternal

/-!
# One bounded distinguished elimination in consecutive coordinates

The coordinate map is displayed without any source-dependent renaming:
`X0`, followed by `X(i+2) - z_i X1`, with `0 <= z_i <= d`.
The literal image is again prime homogeneous of the original dimension,
has degree at most `d`, and still avoids `X0`.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

def distinguishedFinEliminationForms
    {K : Type*} [Field K] {n : ℕ} (z : Fin n → ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 2)) K :=
  Fin.cases (X 0) (fun i ↦ X i.succ.succ - C (z i : K) * X 1)

theorem distinguishedFinEliminationForms_isHomogeneous
    {K : Type*} [Field K] {n : ℕ} (z : Fin n → ℕ) (i : Fin (n + 1)) :
    (distinguishedFinEliminationForms (K := K) z i).IsHomogeneous 1 := by
  refine Fin.cases (isHomogeneous_X K 0) (fun j ↦ ?_) i
  exact (isHomogeneous_X K j.succ.succ).sub
    ((isHomogeneous_X K 1).C_mul (z j : K))

theorem exists_boundedNat_distinguishedFiniteLinearImage
    {K : Type*} [Field K] [CharZero K] {n r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 2)) K))
    (hIne : I ≠ ⊥) (hX : X 0 ∉ I)
    (hdegree : HasProjectiveDimensionDegree I r d) :
    ∃ z : Fin n → ℕ, (∀ i, z i ≤ d) ∧
      let forms := distinguishedFinEliminationForms (K := K) z
      let h := (Ideal.Quotient.mkₐ K I).comp (aeval forms)
      let P := RingHom.ker h.toRingHom
      h.Finite ∧ P.IsPrime ∧ P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) ∧
        X 0 ∉ P ∧ ∃ e : ℕ, e ≤ d ∧ HasProjectiveDimensionDegree P r e := by
  classical
  let e : Fin (n + 2) ≃ Option (Option (Fin n)) :=
    (_root_.finSuccEquiv (n + 1)).trans (distinguishedFinSuccEquiv n)
  let E := renameEquiv K e
  let J := I.map E
  letI : I.IsPrime := hIprime
  have hJprime : J.IsPrime := by dsimp only [J, E]; infer_instance
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Option (Option (Fin n))) K) :=
    map_renameEquiv_isHomogeneous e I hIhom
  have hJne : J ≠ ⊥ := by
    dsimp only [J]
    exact (Ideal.map_eq_bot_iff_of_injective E.injective).not.mpr hIne
  have he0 : e 0 = some none := by simp [e]
  have he1 : e 1 = none := by
    have h1 : (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ := by ext; simp
    change distinguishedFinSuccEquiv n ((_root_.finSuccEquiv (n + 1)) 1) = none
    rw [h1]
    rw [_root_.finSuccEquiv_succ, distinguishedFinSuccEquiv_some_zero]
  have hei (i : Fin n) : e i.succ.succ = some (some i) := by simp [e]
  have hJX : X (some none) ∉ J := by
    intro hx
    apply hX
    have hh : E (X 0) ∈ J := by simpa [E, he0] using hx
    exact (Ideal.apply_mem_of_equiv_iff (f := E.toRingEquiv)).1 hh
  have hJdegree : HasProjectiveDimensionDegree
      (J.map (renameEquiv K (doubleOptionFinEquiv n))) r d := by
    have heq : J.map (renameEquiv K (doubleOptionFinEquiv n)) =
        I.map (renameEquiv K (e.trans (doubleOptionFinEquiv n))) := by
      dsimp only [J, E]
      change Ideal.map (renameEquiv K (doubleOptionFinEquiv n)).toRingHom
        (Ideal.map (renameEquiv K e).toRingHom I) =
        Ideal.map (renameEquiv K (e.trans (doubleOptionFinEquiv n))).toRingHom I
      rw [Ideal.map_map]
      have hcomp : (renameEquiv K (doubleOptionFinEquiv n)).toAlgHom.comp
          (renameEquiv K e).toAlgHom =
          (renameEquiv K (e.trans (doubleOptionFinEquiv n))).toAlgHom := by
        apply MvPolynomial.algHom_ext
        intro i
        simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
          MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.trans_apply]
      exact congrArg (fun f ↦ Ideal.map f I) (congrArg AlgHom.toRingHom hcomp)
    rw [heq]
    exact hasProjectiveDimensionDegree_map_renameEquiv_over _ I hdegree
  obtain ⟨z, hz, hfinite⟩ :=
    exists_boundedNat_finite_distinguishedHomogeneousElimination
      J hJprime hJhom hJne hJX hJdegree
  let c : Option (Fin n) → K := fun u ↦ u.elim 0 (fun i ↦ (z i : K))
  let q := Ideal.quotientEquivAlg I J E rfl
  let R := renameEquiv K (_root_.finSuccEquiv n)
  let forms := distinguishedFinEliminationForms (K := K) z
  let h := (Ideal.Quotient.mkₐ K I).comp (aeval forms)
  have hh : q.toAlgHom.comp h =
      (homogeneousLinearEliminationHom c J).comp R.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [AlgHom.comp_apply, h, MvPolynomial.aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      change q (Ideal.Quotient.mk I (X 0)) =
        homogeneousLinearEliminationHom c J (R (X 0))
      rw [Ideal.quotientEquivAlg_mk]
      simp [R, E, he0, homogeneousLinearEliminationHom_X, c]
    · simp only [AlgHom.comp_apply, h, MvPolynomial.aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      change q (Ideal.Quotient.mk I
        (X j.succ.succ - C (z j : K) * X 1)) =
        homogeneousLinearEliminationHom c J (R (X j.succ))
      rw [Ideal.quotientEquivAlg_mk]
      simp [R, E, hei, he1, homogeneousLinearEliminationHom_X, c]
  have hhfinite : h.Finite := by
    have hcompfinite : (q.toAlgHom.comp h).Finite := by
      rw [hh]
      exact AlgHom.Finite.comp hfinite (AlgHom.Finite.of_surjective _ R.surjective)
    have hback : q.symm.toAlgHom.comp (q.toAlgHom.comp h) = h := by
      ext f
      simp
    rw [← hback]
    exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective _ q.symm.surjective) hcompfinite
  let P := RingHom.ker h.toRingHom
  have hPprime : P.IsPrime := RingHom.ker_isPrime h
  have hPhom : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
    kernel_homogeneousLinearCoordinateMap_isHomogeneous I hIhom forms
      (distinguishedFinEliminationForms_isHomogeneous z)
  have hPX : X 0 ∉ P := by
    intro hp
    have hpzero := RingHom.mem_ker.mp hp
    change Ideal.Quotient.mk I (aeval forms (X 0)) = 0 at hpzero
    rw [MvPolynomial.aeval_X] at hpzero
    apply hX
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hpzero
  refine ⟨z, hz, hhfinite, hPprime, hPhom, hPX, ?_⟩
  exact finite_homogeneousLinearImage_exists_projectiveDimensionDegree_le
    I hIprime hIhom hdegree forms (distinguishedFinEliminationForms_isHomogeneous z)
    hhfinite 0 hX

end
end TranslatedDepthSeven
