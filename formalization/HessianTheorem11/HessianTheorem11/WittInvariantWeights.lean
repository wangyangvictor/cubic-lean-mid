import HessianTheorem11.WittSubspaceBasis

/-! Explicit middle-space weights for an invariant isotropic subspace,
constructed from the actual Witt basis. -/
noncomputable section
namespace HessianTheorem11.WittSubspaceBasis
open Module Submodule
variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def middleWeight {r l k : ℕ} : Index r l k → ℤ :=
  Sum.elim (fun _ => 1) (Sum.elim (Sum.elim (fun _ => 0) (fun _ => 2)) (fun _ => 1))

theorem weight_eq_middleWeight {r l k : ℕ} (i : Index r l k) :
    weight i = 2*middleWeight i+2 := by
  rcases i with i | ((i|i)|i) <;> rfl

theorem middleWeight_bounds {r l k : ℕ} (i : Index r l k) :
    0 ≤ middleWeight i ∧ middleWeight i ≤ 2 := by
  rcases i with i | ((i|i)|i) <;> norm_num [middleWeight]

theorem Data.middleWeight_gram {B : LinearMap.BilinForm K V} {W : Submodule K V}
    {r l k : ℕ} (S : Data B W r l k) (i j : Index r l k)
    (h : B (S.basis i) (S.basis j) ≠ 0) : middleWeight i+middleWeight j=2 := by
  have hh := S.gram_weight i j h
  rw [weight_eq_middleWeight,weight_eq_middleWeight] at hh
  omega

theorem Data.regular_dimension_zero_of_isotropic {B : LinearMap.BilinForm K V} {W : Submodule K V}
    {r l k : ℕ} (S : Data B W r l k)
    (hW : ∀u∈W,∀v∈W,B u v=0) : r=0 := by
  classical
  by_contra hr
  have hrpos : 0<r := Nat.pos_of_ne_zero hr
  letI : Nonempty (Fin r) := ⟨⟨0,hrpos⟩⟩
  have hmem (i : Fin r) : S.basis (regularIndex i) ∈ W := by
    apply S.subspace_span.le
    exact Submodule.subset_span ⟨Sum.inl i,rfl⟩
  have hz : (fun i j => B (S.basis (regularIndex i)) (S.basis (regularIndex j))) =
      (0 : Matrix (Fin r) (Fin r) K) := funext fun i => funext fun j =>
    hW _ (hmem i) _ (hmem j)
  have hh := S.regular_nonsingular
  rw [hz,Matrix.det_zero (by infer_instance)] at hh
  exact hh rfl

theorem Data.basis_mem_of_middleWeight_zero {B : LinearMap.BilinForm K V} {W : Submodule K V}
    {r l k : ℕ} (S : Data B W r l k) (i : Index r l k)
    (hi : middleWeight i=0) : S.basis i ∈ W := by
  rcases i with i | ((i|i)|i)
  · norm_num [middleWeight] at hi
  · apply S.subspace_span.le
    exact Submodule.subset_span ⟨Sum.inr i,rfl⟩
  · norm_num [middleWeight] at hi
  · norm_num [middleWeight] at hi

theorem Data.isotropic_pairing_weight {B : LinearMap.BilinForm K V} {W : Submodule K V}
    {l k : ℕ} (S : Data B W 0 l k) (u : V) (hu : u∈W)
    (i : Index 0 l k) (h : B u (S.basis i) ≠ 0) : middleWeight i=2 := by
  classical
  by_contra hi
  have hz : B u (S.basis i)=0 := by
    clear h
    rw [← S.subspace_span] at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨j,rfl⟩ := hu
      rcases j with j|j
      · exact Fin.elim0 j
      · by_contra hn
        have hh := S.middleWeight_gram (radicalIndex j) i hn
        have hw : middleWeight (radicalIndex (r:=0) (k:=k) j)=0 := rfl
        rw [hw,zero_add] at hh
        exact hi hh
    | zero => simp
    | add a b _ _ ha hb => simp [map_add,ha,hb]
    | smul c a _ ha => simp [map_smul,ha]
  exact h hz

theorem Data.invariant_selfAdjoint_pairing_weight
    {B : LinearMap.BilinForm K V} {W : Submodule K V} {l k : ℕ}
    (S : Data B W 0 l k) (hB : B.IsSymm) (M : V →ₗ[K] V)
    (hM : ∀u v,B (M u) v=B u (M v)) (hinv : ∀u∈W,M u∈W)
    (i j : Index 0 l k) (h : B (M (S.basis i)) (S.basis j)≠0) :
    2≤middleWeight i+middleWeight j := by
  have hi := middleWeight_bounds i
  have hj := middleWeight_bounds j
  by_contra hn
  have hzero : middleWeight i=0 ∨ middleWeight j=0 := by omega
  rcases hzero with hz|hz
  · have hw := S.isotropic_pairing_weight (M (S.basis i))
      (hinv _ (S.basis_mem_of_middleWeight_zero i hz)) j h
    omega
  · have h' : B (M (S.basis j)) (S.basis i)≠0 := by
      rw [hM,hB.eq]
      exact h
    have hw := S.isotropic_pairing_weight (M (S.basis j))
      (hinv _ (S.basis_mem_of_middleWeight_zero j hz)) i h'
    omega

theorem Data.sum_middleWeight {B : LinearMap.BilinForm K V} {W : Submodule K V}
    {r l k : ℕ} (S : Data B W r l k) :
    ∑i:Index r l k,middleWeight i = (finrank K V : ℤ) := by
  classical
  have hd := S.ambient_dimension
  simp [middleWeight,Fintype.sum_sum_type]
  omega

theorem exists_invariant_weight_basis {A : Type*} {q : ℕ}
    (B : LinearMap.BilinForm K (Fin q → K)) (hB : B.IsSymm) (hn : B.Nondegenerate)
    (W : Submodule K (Fin q → K)) (hW : ∀u∈W,∀v∈W,B u v=0)
    (e : A → (Fin q → K)) (M : A → ((Fin q → K) →ₗ[K] (Fin q → K)))
    (he : ∀a,e a∈W) (hM : ∀a u v,B (M a u) v=B u (M a v))
    (hinv : ∀a u,u∈W→M a u∈W) :
    ∃ (b : Basis (Fin q) K (Fin q → K)) (w : Fin q → ℤ),
      (∀i,0≤w i) ∧ (∑i,w i)=(q:ℤ) ∧
      (∀i j,B (b i) (b j)≠0→w i+w j=2) ∧
      (∀a i,B (e a) (b i)≠0→w i=2) ∧
      (∀a i j,B (M a (b i)) (b j)≠0→2≤w i+w j) := by
  classical
  obtain ⟨r,l,k,⟨S⟩⟩ := exists_data B hB hn W
  have hr := S.regular_dimension_zero_of_isotropic hW
  subst r
  have hc : Fintype.card (Index 0 l k)=q := by
    simpa using (finrank_eq_card_basis S.basis).symm
  let f : Index 0 l k ≃ Fin q := (Fintype.equivFin _).trans (finCongr hc)
  let b := S.basis.reindex f
  let w := fun i => middleWeight (f.symm i)
  refine ⟨b,w,?_,?_,?_,?_,?_⟩
  · intro i
    exact (middleWeight_bounds (f.symm i)).1
  · have hs := S.sum_middleWeight
    simpa only [w,f.symm.sum_comp,Module.finrank_pi,Fintype.card_fin] using hs
  · intro i j hij
    apply S.middleWeight_gram (f.symm i) (f.symm j)
    simpa only [b,Basis.reindex_apply] using hij
  · intro a i hai
    apply S.isotropic_pairing_weight (e a) (he a) (f.symm i)
    simpa only [b,Basis.reindex_apply] using hai
  · intro a i j hij
    apply S.invariant_selfAdjoint_pairing_weight hB (M a) (hM a) (hinv a) (f.symm i) (f.symm j)
    simpa only [b,Basis.reindex_apply] using hij

end HessianTheorem11.WittSubspaceBasis
