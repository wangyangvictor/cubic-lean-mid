import HessianTheorem11.BilinearRadicalSplit

/-! A Witt basis adapted to an arbitrary subspace of a nondegenerate
symmetric bilinear space. All vectors and complements are constructed. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace HessianTheorem11.WittSubspaceBasis
open Module Submodule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

abbrev Index (r l k : ℕ) := Fin r ⊕ ((Fin l ⊕ Fin l) ⊕ Fin k)
def regularIndex {r l k : ℕ} (i : Fin r) : Index r l k := Sum.inl i
def radicalIndex {r l k : ℕ} (i : Fin l) : Index r l k := Sum.inr (Sum.inl (Sum.inl i))
def dualIndex {r l k : ℕ} (i : Fin l) : Index r l k := Sum.inr (Sum.inl (Sum.inr i))
def residualIndex {r l k : ℕ} (i : Fin k) : Index r l k := Sum.inr (Sum.inr i)
def weight {r l k : ℕ} : Index r l k → ℤ := Sum.elim (fun _ => 4)
  (Sum.elim (Sum.elim (fun _ => 2) (fun _ => 6)) (fun _ => 4))

structure Data (B : LinearMap.BilinForm K V) (U : Submodule K V) (r l k : ℕ) where
  basis : Basis (Index r l k) K V
  ambient_dimension : r + 2*l + k = finrank K V
  subspace_dimension : r + l = finrank K U
  subspace_span : Submodule.span K (Set.range (Sum.elim
    (fun i => basis (regularIndex i)) (fun i => basis (radicalIndex i)))) = U
  regular_nonsingular : Matrix.det (fun i j => B (basis (regularIndex i))
    (basis (regularIndex j)) : Matrix (Fin r) (Fin r) K) ≠ 0
  gram_weight : ∀ i j, B (basis i) (basis j) ≠ 0 → weight i + weight j = 8
  radical_dual : ∀ i j, B (basis (radicalIndex i)) (basis (dualIndex j)) =
    if i = j then 1 else 0
  regular_orthogonal : ∀ i j, B (basis (regularIndex i)) (basis (Sum.inr j)) = 0

private theorem orthogonal_nondegenerate (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (P : Submodule K V)
    (hP : IsCompl P (B.orthogonal P)) : (B.restrict (B.orthogonal P)).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    HyperbolicBasis.kernel_restrict_orthogonal B hB P hP, hn.ker_eq_bot]
  simp

theorem exists_data (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (U : Submodule K V) :
    ∃ r l k, Nonempty (Data B U r l k) := by
  classical
  obtain ⟨D⟩ := BilinearRadicalSplit.nonempty_data B hB U
  let W := B.orthogonal D.regular
  let BW := B.restrict W
  have hBW : BW.IsSymm := ⟨fun x y => hB.eq x y⟩
  have hRW : IsCompl D.regular W := D.isCompl_regular_orthogonal hB
  have hnW : BW.Nondegenerate := orthogonal_nondegenerate B hB hn D.regular hRW
  let R := D.radical.comap W.subtype
  let eR := Submodule.comapSubtypeEquivOfLe (D.radical_le_orthogonal hB)
  let br := (Module.finBasis K D.radical).map eR.symm
  have hR : ∀ u ∈ R, ∀ v ∈ R, BW u v = 0 := by
    intro u hu v hv
    exact D.radical_isotropic _ hu _ hv
  obtain ⟨z,hwz,hzz⟩ := IsotropicDual.exists_dual_family BW hBW hnW R hR br
  let w := fun i => (br i : W)
  have hww : ∀ i j, BW (w i) (w j) = 0 := fun i j => hR _ (br i).property _ (br j).property
  have hi := IsotropicDual.hyperbolic_family_independent BW hBW w z hww hzz hwz
  let H := Submodule.span K (Set.range (Sum.elim w z))
  let C := BW.orthogonal H
  have hnH : (BW.restrict H).Nondegenerate :=
    IsotropicDual.hyperbolic_span_nondegenerate BW hBW w z hww hzz hwz
  have hHC : IsCompl H C := BW.isCompl_orthogonal_of_restrict_nondegenerate hBW.isRefl hnH
  let bh := Basis.span hi
  let bc := Module.finBasis K C
  let bW := (bh.prod bc).map (H.prodEquivOfIsCompl C hHC)
  let bR := Module.finBasis K D.regular
  let b := (bR.prod bW).map (D.regular.prodEquivOfIsCompl W hRW)
  have hbR (i) : b (regularIndex i) = (bR i : V) := by
    simp [b, regularIndex, Basis.prod_apply]
    change (bR i : V) + 0 = _
    exact add_zero _
  have hbW (i) : b (radicalIndex i) = (w i : V) := by
    simp [b, bW, bh, radicalIndex, Basis.prod_apply]
    change (0 : V) + (((Basis.span hi (Sum.inl i) : W) + 0 : W) : V) = _
    simp only [add_zero, zero_add, Basis.span_apply, Sum.elim_inl]
  have hbZ (i) : b (dualIndex i) = (z i : V) := by
    simp [b, bW, bh, dualIndex, Basis.prod_apply]
    change (0 : V) + (((Basis.span hi (Sum.inr i) : W) + 0 : W) : V) = _
    simp only [add_zero, zero_add, Basis.span_apply, Sum.elim_inr]
  have hbC (i) : b (residualIndex i) = ((bc i : W) : V) := by
    simp [b, bW, residualIndex, Basis.prod_apply]
    change (0 : V) + (((0 : W) + (bc i : W) : W) : V) = _
    simp only [zero_add]
  have hbOther (j) : b (Sum.inr j) ∈ W := by
    simp only [b, Basis.map_apply, Basis.prod_apply, Sum.elim_inr]
    change (0 : V) + (bW j : V) ∈ W
    simpa only [zero_add] using (bW j).property
  have hRegOther (i j) : B (b (regularIndex i)) (b (Sum.inr j)) = 0 := by
    rw [hbR]
    exact hbOther j _ (bR i).property
  have hHCzero (j i) : BW (Sum.elim w z j) (bc i : W) = 0 := by
    exact (bc i).property _ (Submodule.subset_span ⟨j,rfl⟩)
  simp only [regularIndex] at hbR
  simp only [radicalIndex] at hbW
  simp only [dualIndex] at hbZ
  simp only [residualIndex] at hbC
  have hDimU : finrank K D.regular + finrank K D.radical = finrank K U := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq D.regular D.radical
    rw [D.sup_eq, D.disjoint.eq_bot, finrank_bot, add_zero] at he
    exact he.symm
  have hSpan : Submodule.span K (Set.range (Sum.elim
      (fun i => b (regularIndex i)) (fun i => b (radicalIndex i)))) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      cases i with
      | inl i => rw [Sum.elim_inl, regularIndex, hbR]; exact D.regular_le (bR i).property
      | inr i =>
        rw [Sum.elim_inr,radicalIndex,hbW]
        exact D.radical_le (br i).property
    · have hsub : Function.Injective (Sum.elim regularIndex radicalIndex :
          Fin (finrank K D.regular) ⊕ Fin (finrank K D.radical) →
            Index (finrank K D.regular) (finrank K D.radical) (finrank K C)) := by
        intro i j he
        cases i <;> cases j <;> simp only [Sum.elim_inl, Sum.elim_inr,
          regularIndex, radicalIndex, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at he ⊢ <;> assumption
      have hh := b.linearIndependent.comp (Sum.elim regularIndex radicalIndex) hsub
      have he : ⇑b ∘ Sum.elim regularIndex radicalIndex =
          Sum.elim (fun i => b (regularIndex i)) (fun i => b (radicalIndex i)) := by
        funext i
        cases i <;> rfl
      rw [he] at hh
      rw [finrank_span_eq_card hh]
      simpa using hDimU
  refine ⟨finrank K D.regular,finrank K D.radical,finrank K C,⟨{
    basis := b
    ambient_dimension := ?_
    subspace_dimension := hDimU
    subspace_span := hSpan
    regular_nonsingular := ?_
    gram_weight := ?_
    radical_dual := ?_
    regular_orthogonal := hRegOther }⟩⟩
  · have he := (finrank_eq_card_basis b).symm
    simpa [Index, two_mul, add_assoc] using he
  · convert (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bR).mp
      D.regular_nondegenerate using 1
    congr 1
    funext i j
    simp only [regularIndex, hbR]
    simp [BilinForm.toMatrix_apply]
  · intro i j hne
    cases i with
    | inl i =>
      cases j with
      | inl j => norm_num [weight]
      | inr j => exact (hne (hRegOther i j)).elim
    | inr i =>
      cases j with
      | inl j => exact (hne ((hB.eq _ _).trans (hRegOther j i))).elim
      | inr j =>
        cases i with
        | inl i =>
          cases j with
          | inl j =>
            cases i with
            | inl i =>
              cases j with
              | inl j => exact (hne (by simpa only [hbW] using hww i j)).elim
              | inr j => norm_num [weight]
            | inr i =>
              cases j with
              | inl j => norm_num [weight]
              | inr j => exact (hne (by simpa only [hbZ] using hzz i j)).elim
          | inr j =>
            exact (hne (by
              cases i with
              | inl i => simpa only [hbW,hbC, Sum.elim_inl] using hHCzero (Sum.inl i) j
              | inr i => simpa only [hbZ,hbC, Sum.elim_inr] using hHCzero (Sum.inr i) j)).elim
        | inr i =>
          cases j with
          | inr j => norm_num [weight]
          | inl j =>
            apply False.elim
            apply hne
            rw [hB.eq]
            cases j with
            | inl j => simpa only [hbW,hbC, Sum.elim_inl] using hHCzero (Sum.inl j) i
            | inr j => simpa only [hbZ,hbC, Sum.elim_inr] using hHCzero (Sum.inr j) i
  · intro i j
    simpa only [radicalIndex,dualIndex,hbW,hbZ] using hwz i j

end HessianTheorem11.WittSubspaceBasis
