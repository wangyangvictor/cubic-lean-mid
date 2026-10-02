import TranslatedDepthSeven.ProjectiveExteriorPointSeparatorInternal
import TranslatedDepthSeven.FieldPolynomialNatGridInternal
import TranslatedDepthSeven.AffinePolynomialChange

/-!
# A bounded integral choice in distinguished homogeneous elimination

The eliminated coordinate has value one and the retained distinguished
coordinate has value zero. A degree-bounded equation separating one such
exterior point restricts to a nonzero polynomial on this affine space.
The fixed natural-number grid then supplies a choice whose coefficients
are all at most the projective degree. No coefficient-height bound on the
equation and no geometric generic-projection hypothesis are used.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published

attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Two successive standard chart indices, in consecutive order. -/
def doubleOptionFinEquiv (n : ℕ) : Option (Option (Fin n)) ≃ Fin (n + 2) :=
  ((_root_.finSuccEquiv (n + 1)).trans
    (Equiv.optionCongr (_root_.finSuccEquiv n))).symm

@[simp] theorem doubleOptionFinEquiv_symm_zero (n : ℕ) :
    (doubleOptionFinEquiv n).symm 0 = none := by
  simp [doubleOptionFinEquiv]

/-- An equation and an integral shear, with the distinguished coefficient
zero, obtained from the actual degree certificate of the same ideal in
consecutively indexed coordinates. -/
theorem exists_boundedNat_distinguishedAffineChartRelation
    {K : Type*} [Field K] [CharZero K] {n r d : ℕ}
    (J : Ideal (MvPolynomial (Option (Option (Fin n))) K))
    (hJprime : J.IsPrime)
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Option (Fin n))) K))
    (hJne : J ≠ ⊥) (hX : X (some none) ∉ J)
    (hdegree : HasProjectiveDimensionDegree
      (J.map (renameEquiv K (doubleOptionFinEquiv n))) r d) :
    ∃ (f : MvPolynomial (Option (Option (Fin n))) K) (k : ℕ)
      (z : Fin n → ℕ),
      k ≤ d ∧ f ∈ J ∧ f.IsHomogeneous k ∧ (∀ i, z i ≤ d) ∧
      eval (affineChartVector (fun u ↦ u.elim 0 (fun i ↦ (z i : K)))) f ≠ 0 := by
  classical
  obtain ⟨f₀, k₀, c₀, hf₀J, hf₀hom, hc₀, hf₀ne⟩ :=
    distinguishedAffineChartRelationSupply_of_infinite
      n J hJprime hJhom hJne hX
  let e := doubleOptionFinEquiv n
  let E := renameEquiv K e
  let I := J.map E
  let x : Fin (n + 2) → K := affineChartVector c₀ ∘ e.symm
  have hx0 : x 0 = 1 := by simp [x, e, affineChartVector]
  have heval (f : MvPolynomial (Option (Option (Fin n))) K) :
      eval x (E f) = eval (affineChartVector c₀) f := by
    change eval x (rename e f) = _
    rw [eval_rename]
    have hpoint : x ∘ e = affineChartVector c₀ := by
      funext i
      simp [x]
    rw [hpoint]
  letI : J.IsPrime := hJprime
  have hIprime : I.IsPrime := by dsimp only [I, E]; infer_instance
  have hIhom : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin (n + 2)) K) :=
    map_renameEquiv_isHomogeneous e J hJhom
  obtain ⟨k, G, hkd, hGhom, hGI, hGx⟩ :=
    exists_homogeneous_projectiveDegree_separator_at_firstChartPoint
      I hIprime hIhom hdegree x hx0
      ⟨E f₀, Ideal.mem_map_of_mem E hf₀J, by simpa only [heval] using hf₀ne⟩
  let f := E.symm G
  have hfJ : f ∈ J :=
    (Ideal.symm_apply_mem_of_equiv_iff (f := E.toRingEquiv)).2 hGI
  have hfhom : f.IsHomogeneous k := hGhom.rename_isHomogeneous
  have hfc₀ : eval (affineChartVector c₀) f = 1 := by
    rw [← heval]
    simpa only [f, AlgEquiv.apply_symm_apply] using hGx
  let l : Option (Option (Fin n)) → MvPolynomial (Fin n) K :=
    fun u ↦ u.elim 1 (fun v ↦ v.elim 0 X)
  let g := aeval l f
  have hevalRestriction (z : Fin n → K) :
      eval z g =
        eval (affineChartVector (fun u ↦ u.elim 0 z)) f := by
    change (aeval z) (aeval l f) = _
    rw [MvPolynomial.comp_aeval_apply]
    have hpoint : (fun u ↦ (aeval z) (l u)) =
        affineChartVector (fun u ↦ u.elim 0 z) := by
      funext u
      cases u with
      | none => simp [l, affineChartVector]
      | some v =>
        cases v with
        | none => simp [l, affineChartVector]
        | some i => simp [l, affineChartVector]
    rw [hpoint]
    rfl
  have hgne : g ≠ 0 := by
    intro hg
    have hh := hevalRestriction (fun i ↦ c₀ (some i))
    have hc : (fun u : Option (Fin n) ↦ u.elim 0 (fun i ↦ c₀ (some i))) = c₀ := by
      funext u
      cases u with
      | none => exact hc₀.symm
      | some i => rfl
    rw [hg, map_zero, hc, hfc₀] at hh
    exact zero_ne_one hh
  have hgdegree : g.totalDegree ≤ d := by
    refine (totalDegree_aeval_le_of_totalDegree_le_one l ?_ f).trans
      (hfhom.totalDegree_le.trans hkd)
    intro u
    cases u with
    | none => simp [l]
    | some v =>
      cases v with
      | none => simp [l]
      | some i => simp [l]
  obtain ⟨z, hz, hgz⟩ :=
    exists_nonzero_eval_on_boundedNatGrid_over_field g hgne hgdegree
  exact ⟨f, k, z, hkd, hfJ, hfhom, hz, (hevalRestriction _).symm ▸ hgz⟩

/-- The preceding bounded shear gives the literal finite elimination map.
The retained distinguished linear form is unchanged because its shear
coefficient is zero. -/
theorem exists_boundedNat_finite_distinguishedHomogeneousElimination
    {K : Type*} [Field K] [CharZero K] {n r d : ℕ}
    (J : Ideal (MvPolynomial (Option (Option (Fin n))) K))
    (hJprime : J.IsPrime)
    (hJhom : J.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Option (Option (Fin n))) K))
    (hJne : J ≠ ⊥) (hX : X (some none) ∉ J)
    (hdegree : HasProjectiveDimensionDegree
      (J.map (renameEquiv K (doubleOptionFinEquiv n))) r d) :
    ∃ z : Fin n → ℕ, (∀ i, z i ≤ d) ∧
      (homogeneousLinearEliminationHom
        (fun u ↦ u.elim 0 (fun i ↦ (z i : K))) J).Finite := by
  obtain ⟨f, k, z, hkd, hfJ, hfhom, hz, hfne⟩ :=
    exists_boundedNat_distinguishedAffineChartRelation J hJprime hJhom hJne hX hdegree
  exact ⟨z, hz, finite_homogeneousLinearEliminationHom_of_eval_ne_zero
    J f k hfJ hfhom _ hfne⟩

end
end TranslatedDepthSeven
