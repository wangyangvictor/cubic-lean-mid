import TranslatedDepthSeven.SmoothSurfaceResidueExponent

/-! Group the usable columns by their residue class and give each discarded
column its own singleton class. The latter contribute exactly zero jet
weight, including empty labels. -/

namespace TranslatedDepthSeven
noncomputable section
open scoped BigOperators

def mixedResidueLabel {ι ν : Type*} (good : ι → Prop) [DecidablePred good]
    (label : {j // good j} → ν) (j : ι) : ν ⊕ ι :=
  if h : good j then Sum.inl (label ⟨j, h⟩) else Sum.inr j

theorem mixedResidueLabel_eq_inl_iff {ι ν : Type*}
    (good : ι → Prop) [DecidablePred good] (label : {j // good j} → ν)
    (j : ι) (c : ν) :
    mixedResidueLabel good label j = Sum.inl c ↔ ∃ h : good j, label ⟨j, h⟩ = c := by
  by_cases h : good j <;> simp [mixedResidueLabel, h]

theorem mixedResidueLabel_eq_inr_iff {ι ν : Type*}
    (good : ι → Prop) [DecidablePred good] (label : {j // good j} → ν)
    (j k : ι) :
    mixedResidueLabel good label j = Sum.inr k ↔ ¬ good j ∧ j = k := by
  by_cases h : good j <;> simp [mixedResidueLabel, h]

def mixedResidueLeftFiberEquiv {ι ν : Type*}
    (good : ι → Prop) [DecidablePred good] (label : {j // good j} → ν) (c : ν) :
    {j // mixedResidueLabel good label j = Sum.inl c} ≃
      {j : {j // good j} // label j = c} where
  toFun j :=
    let h := (mixedResidueLabel_eq_inl_iff good label j.val c).mp j.property
    ⟨⟨j.val, h.choose⟩, h.choose_spec⟩
  invFun j := ⟨j.val.val,
    (mixedResidueLabel_eq_inl_iff good label _ c).mpr ⟨j.val.property, j.property⟩⟩
  left_inv j := by apply Subtype.ext; rfl
  right_inv j := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Zero and singleton classes have no local determinant gain. -/
theorem smoothSurfaceJetExponent_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) :
    smoothSurfaceJetExponent n = 0 := by
  interval_cases n
  · exact smoothSurfaceJetExponent_zero
  · have h := smoothSurfaceJetExponent_eq_of_layer 1 0 0
      (by simp [affinePlaneMonomialCount]) (by omega)
    simpa [affinePlaneMonomialWeight] using h

/-- The complete class sum retains exactly the contributions of the good
fibers. No smoothness or artificial weight is assigned to discarded points. -/
theorem sum_mixedResidueLabel_jetExponent
    {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (good : ι → Prop) [DecidablePred good] (label : {j // good j} → ν) :
    (∑ c : ν ⊕ ι, smoothSurfaceJetExponent
      (Fintype.card {j // mixedResidueLabel good label j = c})) =
        ∑ c : ν, smoothSurfaceJetExponent (Fintype.card {j // label j = c}) := by
  classical
  rw [Fintype.sum_sum_type]
  have hleft : (∑ c : ν, smoothSurfaceJetExponent
      (Fintype.card {j // mixedResidueLabel good label j = Sum.inl c})) =
        ∑ c : ν, smoothSurfaceJetExponent (Fintype.card {j // label j = c}) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.card_congr (mixedResidueLeftFiberEquiv good label c)]
  rw [hleft]
  have hright (k : ι) : smoothSurfaceJetExponent
      (Fintype.card {j // mixedResidueLabel good label j = Sum.inr k}) = 0 := by
    apply smoothSurfaceJetExponent_eq_zero_of_le_one
    letI : Subsingleton {j // mixedResidueLabel good label j = Sum.inr k} :=
      ⟨fun a b => Subtype.ext (((mixedResidueLabel_eq_inr_iff good label _ k).mp
        a.property).2.trans (((mixedResidueLabel_eq_inr_iff good label _ k).mp b.property).2.symm))⟩
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  simp only [hright, Finset.sum_const_zero, add_zero]

end
end TranslatedDepthSeven
