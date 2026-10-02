import HessianTheorem11.IsotropicDual
import HessianTheorem11.TwoByTwoResolvent

/-! An actual Witt basis and a lift of the range coordinates for a
rank-two linear map into a four-dimensional symmetric space. -/
noncomputable section
namespace HessianTheorem11.IsotropicPlaneCoordinates
open Module Submodule Matrix TwoByTwoResolvent
variable {K A V : Type*} [Field K] [CharZero K]
  [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

structure Data (B : LinearMap.BilinForm K V) (W : Submodule K V) where
  basis : Basis (Fin 2 ⊕ Fin 2) K V
  gram_eq : BilinForm.toMatrix basis B = gram
  left_span : span K (Set.range fun i : Fin 2 => basis (Sum.inl i)) = W

theorem exists_data (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (hn : B.Nondegenerate) (hd : finrank K V=4)
    (W : Submodule K V) (hW : ∀ u∈W, ∀v∈W, B u v=0) (hw : finrank K W=2) :
    Nonempty (Data B W) := by
  classical
  let bw := (Module.finBasis K W).reindex (finCongr hw)
  let w : Fin 2 → V := fun i => bw i
  obtain ⟨z,hwz,hzz⟩ := IsotropicDual.exists_dual_family B hB hn W hW bw
  change ∀ i j, B (w i) (z j)=if i=j then 1 else 0 at hwz
  have hww : ∀ i j, B (w i) (w j)=0 := fun i j => hW _ (bw i).property _ (bw j).property
  have hi := IsotropicDual.hyperbolic_family_independent B hB w z hww hzz hwz
  have hspan : span K (Set.range (Sum.elim w z)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hi,hd]
    simp
  let b := Basis.mk hi hspan.ge
  have hb (i : Fin 2 ⊕ Fin 2) : b i=Sum.elim w z i := Basis.mk_apply _ _ i
  have hleft : span K (Set.range fun i : Fin 2 => b (Sum.inl i))=W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      change b (Sum.inl i) ∈ W
      rw [hb]
      exact (bw i).property
    · have hiL : LinearIndependent K (fun i : Fin 2 => b (Sum.inl i)) := b.linearIndependent.comp Sum.inl Sum.inl_injective
      rw [finrank_span_eq_card hiL,hw]
      simp
  refine ⟨⟨b,?_,hleft⟩⟩
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [BilinForm.toMatrix_apply,hb,hww,gram]
  · simp [BilinForm.toMatrix_apply,hb,hwz,gram,Matrix.one_apply]
  · simp [BilinForm.toMatrix_apply,hb,hB.eq (z i) (w j),hwz,gram,Matrix.one_apply,eq_comm]
  · simp [BilinForm.toMatrix_apply,hb,hzz,gram]

variable {B : LinearMap.BilinForm K V} {W : Submodule K V}

def Data.leftMap (D : Data B W) : Vec K →ₗ[K] V :=
  (Pi.basisFun K (Fin 2)).constr K (fun i => D.basis (Sum.inl i))

theorem leftMap_eq (D : Data B W) (u : Vec K) :
    D.leftMap u = D.basis.equivFun.symm (embed u) := by
  simp [Data.leftMap,Basis.constr_apply_fintype,Basis.equivFun_symm_apply,embed,Fintype.sum_sum_type]

theorem leftMap_range (D : Data B W) : LinearMap.range D.leftMap=W := by
  rw [Data.leftMap,Basis.constr_range]
  exact D.left_span

theorem exists_lift (e : A →ₗ[K] V) (D : Data B (LinearMap.range e)) :
    ∃ L : Vec K →ₗ[K] A, ∀ u, e (L u) = D.leftMap u := by
  classical
  have hb (i : Fin 2) : D.basis (Sum.inl i) ∈ LinearMap.range e := by
    exact D.left_span.le (subset_span ⟨i,rfl⟩)
  choose a ha using hb
  let L := (Pi.basisFun K (Fin 2)).constr K a
  refine ⟨L,fun u => ?_⟩
  simp [L,Data.leftMap,Basis.constr_apply_fintype,map_sum,map_smul,ha]

theorem Data.pair_left (D : Data B W) (i : Fin 2) (v : V) :
    B (D.basis (Sum.inl i)) v = D.basis.equivFun v (Sum.inr i) := by
  rw [BilinForm.apply_eq_dotProduct_toMatrix_mulVec D.basis B,D.gram_eq]
  fin_cases i <;> simp [gram,dotProduct,mulVec,Fintype.sum_sum_type,Basis.repr_self]

theorem Data.pair_right (D : Data B W) (i : Fin 2) (v : V) :
    B (D.basis (Sum.inr i)) v = D.basis.equivFun v (Sum.inl i) := by
  rw [BilinForm.apply_eq_dotProduct_toMatrix_mulVec D.basis B,D.gram_eq]
  fin_cases i <;> simp [gram,dotProduct,mulVec,Fintype.sum_sum_type,Basis.repr_self]

def Data.blockMap (D : Data B W) (r c : Fin 2 → Fin 2 ⊕ Fin 2) :
    Module.End K V →ₗ[K] Mat K where
  toFun T := (LinearMap.toMatrix D.basis D.basis T).submatrix r c
  map_add' T S := by ext i j; simp
  map_smul' c T := by ext i j; simp

theorem Data.blockMap_apply (D : Data B W) (r c : Fin 2 → Fin 2 ⊕ Fin 2)
    (T : Module.End K V) (i j : Fin 2) :
    D.blockMap r c T i j = D.basis.equivFun (T (D.basis (c j))) (r i) := by
  exact LinearMap.toMatrix_apply D.basis D.basis T (r i) (c j)

theorem Data.selfAdjoint_blocks (D : Data B W) (hB : B.IsSymm)
    (T : Module.End K V) (hT : ∀ u v, B (T u) v = B u (T v)) :
    LinearMap.toMatrix D.basis D.basis T =
      block (D.blockMap Sum.inl Sum.inl T) (D.blockMap Sum.inl Sum.inr T)
        (D.blockMap Sum.inr Sum.inl T) ∧
      (D.blockMap Sum.inl Sum.inr T).IsSymm ∧
      (D.blockMap Sum.inr Sum.inl T).IsSymm := by
  have hdiag (i j : Fin 2) :
      D.basis.equivFun (T (D.basis (Sum.inr j))) (Sum.inr i) =
        D.basis.equivFun (T (D.basis (Sum.inl i))) (Sum.inl j) := by
    have h := hT (D.basis (Sum.inr j)) (D.basis (Sum.inl i))
    rw [hB.eq, D.pair_left,D.pair_right] at h
    exact h
  refine ⟨?_,?_,?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · rfl
    · simpa [block,Data.blockMap,LinearMap.toMatrix_apply] using hdiag i j
  · ext i j
    change D.blockMap Sum.inl Sum.inr T j i = D.blockMap Sum.inl Sum.inr T i j
    simp only [Data.blockMap_apply]
    have h := hT (D.basis (Sum.inr i)) (D.basis (Sum.inr j))
    rw [hB.eq,D.pair_right,D.pair_right] at h
    exact h
  · ext i j
    change D.blockMap Sum.inr Sum.inl T j i = D.blockMap Sum.inr Sum.inl T i j
    simp only [Data.blockMap_apply]
    have h := hT (D.basis (Sum.inl i)) (D.basis (Sum.inl j))
    rw [hB.eq,D.pair_left,D.pair_left] at h
    exact h

theorem Data.right_coordinate_zero (D : Data B W) (v : V) (hv : v∈W) (i : Fin 2) :
    D.basis.equivFun v (Sum.inr i)=0 := by
  have hle : W ≤ LinearMap.ker (D.basis.coord (Sum.inr i)) := by
    apply D.left_span.symm.le.trans
    apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    simp
  exact hle hv

theorem Data.leftMap_coordinates (D : Data B W) (v : V) (hv : v∈W) :
    D.leftMap (fun i => D.basis.equivFun v (Sum.inl i))=v := by
  apply D.basis.equivFun.injective
  rw [leftMap_eq,LinearEquiv.apply_symm_apply]
  ext i
  rcases i with i | i
  · rfl
  · simpa [embed] using (D.right_coordinate_zero v hv i).symm

theorem Data.mem_iff_right_zero (D : Data B W) (v : V) :
    v∈W ↔ ∀ i : Fin 2, D.basis.equivFun v (Sum.inr i)=0 := by
  refine ⟨fun hv => D.right_coordinate_zero v hv,fun hv => ?_⟩
  have he : D.leftMap (fun i => D.basis.equivFun v (Sum.inl i))=v := by
    apply D.basis.equivFun.injective
    rw [leftMap_eq,LinearEquiv.apply_symm_apply]
    ext i
    rcases i with i | i
    · rfl
    · simpa [embed] using (hv i).symm
  have hm : D.leftMap (fun i => D.basis.equivFun v (Sum.inl i)) ∈ LinearMap.range D.leftMap :=
    LinearMap.mem_range_self _ _
  rwa [leftMap_range,he] at hm

theorem Data.right_T_leftMap (D : Data B W) (T : Module.End K V) (u : Vec K) (i : Fin 2) :
    D.basis.equivFun (T (D.leftMap u)) (Sum.inr i) =
      (D.blockMap Sum.inr Sum.inl T).mulVec u i := by
  simp [Data.leftMap,Basis.constr_apply_fintype,map_sum,map_smul,
    Data.blockMap_apply,mulVec,dotProduct,Fin.sum_univ_two,mul_comm]

theorem Data.preserves_of_lower_zero (D : Data B W) (T : Module.End K V)
    (hz : D.blockMap Sum.inr Sum.inl T=0) : ∀ v∈W, T v∈W := by
  intro v hv
  apply (D.mem_iff_right_zero _).mpr
  intro i
  conv_lhs => rw [← D.leftMap_coordinates v hv]
  rw [D.right_T_leftMap,hz,Matrix.zero_mulVec]
  rfl

end HessianTheorem11.IsotropicPlaneCoordinates
